//! Ordered instruction records and composition-set storage with actual replies.
use super::*;
verus! {
pub struct Part2InstructionStorageContext {
    pub input:Part2BoxReference,
    pub composition:(u32,u32,u8),
    pub base:u64,
    pub limits:crate::ResourceLimits,
}
pub struct Part2InstructionRequestContext {
    pub child:Part2InstructionStorageContext,
    pub before:Seq<Part2RawInstructionSet>,
}
pub struct Part2InstructionAppendContext {
    pub request:Part2InstructionRequestContext,
    pub parsed:Part2RawInstructionSet,
}
pub(crate) open spec fn part2_instruction_storage_count(context:Part2InstructionStorageContext)->nat {
    let payload=context.input.1;
    if !part2_box_add_offset(context.base,context.input.0.1).is_ok() || payload.len()<8 {0}else{
        let flags=part2_box_u16([payload[0],payload[1]]);
        let bytes=part2_instruction_record_words(flags)*4;
        let remaining=(payload.len()-8) as nat;
        if flags & !0x0027u16!=0 || bytes==0 {0}
        else if remaining%bytes!=0 {0}else{
            let count=remaining/bytes;
            if count as u64>crate::limits::resource_work_limit(&context.limits) {0}else{count}
        }
    }
}
pub(crate) open spec fn part2_instruction_capacity_run(context:Part2InstructionStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_instruction_storage_count(context);
    if count==0 {Some((Ok(()),events))}else if events.len()==0 {None}else{match events[0] {
        Part2JpipSnapshotEvent::InstructionCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=count {None}
            else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}
pub closed spec fn part2_instruction_capacity_result(context:Part2InstructionStorageContext,
    result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_instruction_capacity_run(context,events),result)
}
pub(crate) proof fn part2_instruction_capacity_observed(context:Part2InstructionStorageContext,
    result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (result==Err(crate::DecodeError::AllocationFailed) &&
        part2_instruction_storage_count(context)>0),
    ensures part2_instruction_capacity_result(context,result),
{
    let count=part2_instruction_storage_count(context);
    let prefix=if count==0 {Seq::empty()}else{
        seq![Part2JpipSnapshotEvent::InstructionCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_instruction_capacity_run(context,prefix+tail)==Some((result,tail)) by {
        if count==0 {assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_instruction_capacity_run(context,events),prefix,result));
}
pub(crate) proof fn part2_instruction_capacity_frames(context:Part2InstructionStorageContext,
    result:Result<(),crate::DecodeError>)
    requires part2_instruction_capacity_result(context,result),
    ensures part2_cold_framed(|events|part2_instruction_capacity_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_instruction_capacity_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_instruction_capacity_run(context,events),result);}
pub(crate) open spec fn part2_instruction_storage_run(context:Part2InstructionStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawInstructionSet> {
    part2_jpip_snapshot_bind(part2_instruction_capacity_run(context,events),
        |_:(),rest|Some((part2_parse_instruction_set(context.input,context.composition,context.base,&context.limits),rest)))
}
pub closed spec fn part2_instruction_storage_result(context:Part2InstructionStorageContext,
    result:Result<Part2RawInstructionSet,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_instruction_storage_run(context,events),result)
}
pub(crate) proof fn part2_instruction_storage_normal(context:Part2InstructionStorageContext)
    ensures part2_instruction_storage_result(context,
        part2_parse_instruction_set(context.input,context.composition,context.base,&context.limits)),
{
    let result=part2_parse_instruction_set(context.input,context.composition,context.base,&context.limits);
    part2_instruction_capacity_observed(context,Ok(()));part2_instruction_capacity_frames(context,Ok(()));
    part2_cold_pure(result);
    part2_cold_bind(|events|part2_instruction_capacity_run(context,events),
        |_:(),rest|Some((result,rest)),Ok(()),result);
}
pub(crate) proof fn part2_instruction_storage_refused(context:Part2InstructionStorageContext,error:crate::DecodeError)
    requires part2_instruction_storage_count(context)>0,part2_instruction_capacity_result(context,Err(error)),
    ensures part2_instruction_storage_result(context,Err(error)),
{
    part2_instruction_capacity_frames(context,Err(error));
    part2_cold_bind(|events|part2_instruction_capacity_run(context,events),
        |_:(),rest|Some((part2_parse_instruction_set(context.input,context.composition,context.base,&context.limits),rest)),
        Err(error),Err(error));
}
pub(crate) proof fn part2_instruction_storage_frames(context:Part2InstructionStorageContext,
    result:Result<Part2RawInstructionSet,crate::DecodeError>)
    requires part2_instruction_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_instruction_storage_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawInstructionSet>|
            (forall|events| #[trigger] other(events)==part2_instruction_storage_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_instruction_storage_run(context,events),result);}

pub(crate) open spec fn part2_instruction_append_count_admitted(context:Part2InstructionRequestContext)->bool {
    let count=context.before.len()+1;
    count<=usize::MAX as nat && count as u64<=crate::limits::resource_layer_limit(&context.child.limits) as u64
}
pub(crate) open spec fn part2_instruction_append_admitted(context:Part2InstructionAppendContext)->bool {
    part2_instruction_append_count_admitted(context.request) &&
        part2_parse_instruction_set(context.request.child.input,context.request.child.composition,
            context.request.child.base,&context.request.child.limits)==Ok(context.parsed)
}
pub(crate) open spec fn part2_instruction_append_capacity_run(context:Part2InstructionAppendContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    if !part2_instruction_append_admitted(context) || events.len()==0 {None}else{match events[0] {
        Part2JpipSnapshotEvent::InstructionSetAppendCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=1 {None}
            else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}
pub closed spec fn part2_instruction_append_capacity_result(context:Part2InstructionAppendContext,
    result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_instruction_append_capacity_run(context,events),result)
}
pub(crate) proof fn part2_instruction_append_capacity_observed(context:Part2InstructionAppendContext,
    result:Result<(),crate::DecodeError>)
    requires part2_instruction_append_admitted(context),
        result==Ok(()) || result==Err(crate::DecodeError::AllocationFailed),
    ensures part2_instruction_append_capacity_result(context,result),
{
    let prefix=seq![Part2JpipSnapshotEvent::InstructionSetAppendCapacity {context,elements:1,succeeded:result.is_ok()}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_instruction_append_capacity_run(context,prefix+tail)==Some((result,tail)) by {
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|part2_instruction_append_capacity_run(context,events),prefix,result));
}
pub(crate) proof fn part2_instruction_append_capacity_frames(context:Part2InstructionAppendContext,
    result:Result<(),crate::DecodeError>)
    requires part2_instruction_append_capacity_result(context,result),
    ensures part2_cold_framed(|events|part2_instruction_append_capacity_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_instruction_append_capacity_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_instruction_append_capacity_run(context,events),result);}
pub(crate) open spec fn part2_instruction_request_after(context:Part2InstructionRequestContext,
    parsed:Part2RawInstructionSet,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    if !part2_instruction_append_count_admitted(context) {Some((Ok(()),events))}
    else{part2_instruction_append_capacity_run(Part2InstructionAppendContext {request:context,parsed},events)}
}
pub(crate) open spec fn part2_instruction_request_run(context:Part2InstructionRequestContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    part2_jpip_snapshot_bind(part2_instruction_storage_run(context.child,events),
        |parsed:Part2RawInstructionSet,rest|part2_instruction_request_after(context,parsed,rest))
}
pub(crate) proof fn part2_instruction_request_normal(context:Part2InstructionRequestContext)
    ensures part2_cold_framed(|events|part2_instruction_request_run(context,events),
        crate::allocation::inspection_capacity_outcome(part2_parse_instruction_set(context.child.input,
            context.child.composition,context.child.base,&context.child.limits))),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_instruction_request_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,crate::allocation::inspection_capacity_outcome(
                    part2_parse_instruction_set(context.child.input,context.child.composition,context.child.base,&context.child.limits))),
{
    let child=context.child;
    let parsed=part2_parse_instruction_set(child.input,child.composition,child.base,&child.limits);
    let result=crate::allocation::inspection_capacity_outcome(parsed);
    part2_instruction_storage_normal(child);part2_instruction_storage_frames(child,parsed);
    if let Ok(value)=parsed {
        if part2_instruction_append_count_admitted(context) {
            let append=Part2InstructionAppendContext {request:context,parsed:value};
            part2_instruction_append_capacity_observed(append,Ok(()));
            part2_instruction_append_capacity_frames(append,Ok(()));
        }else{part2_cold_pure(Ok(()));}
        part2_decode_eta(|events|part2_instruction_request_after(context,value,events),Ok(()));
    }
    part2_cold_bind(|events|part2_instruction_storage_run(child,events),
        |value:Part2RawInstructionSet,rest|part2_instruction_request_after(context,value,rest),parsed,result);
    part2_decode_eta(|events|part2_instruction_request_run(context,events),result);
}
pub(crate) proof fn part2_instruction_request_child_error(context:Part2InstructionRequestContext,error:crate::DecodeError)
    requires part2_instruction_storage_result(context.child,Err(error)),
    ensures part2_cold_framed(|events|part2_instruction_request_run(context,events),Err(error)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_instruction_request_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,Err(error)),
{
    part2_instruction_storage_frames(context.child,Err(error));
    part2_cold_bind(|events|part2_instruction_storage_run(context.child,events),
        |value:Part2RawInstructionSet,rest|part2_instruction_request_after(context,value,rest),Err(error),Err(error));
    part2_decode_eta(|events|part2_instruction_request_run(context,events),Err(error));
}
pub(crate) proof fn part2_instruction_request_append_error(context:Part2InstructionAppendContext,error:crate::DecodeError)
    requires part2_instruction_append_admitted(context),
        part2_instruction_storage_result(context.request.child,Ok(context.parsed)),
        part2_instruction_append_capacity_result(context,Err(error)),
    ensures part2_cold_framed(|events|part2_instruction_request_run(context.request,events),Err(error)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_instruction_request_run(context.request,events)) ==>
                #[trigger] part2_cold_framed(other,Err(error)),
{
    part2_instruction_append_capacity_frames(context,Err(error));
    part2_decode_eta(|events|part2_instruction_request_after(context.request,context.parsed,events),Err(error));
    part2_instruction_storage_frames(context.request.child,Ok(context.parsed));
    part2_cold_bind(|events|part2_instruction_storage_run(context.request.child,events),
        |value:Part2RawInstructionSet,rest|part2_instruction_request_after(context.request,value,rest),Ok(context.parsed),Err(error));
    part2_decode_eta(|events|part2_instruction_request_run(context.request,events),Err(error));
}

pub type Part2CompositionStorageState = (Option<(u32,u32,u8)>,Seq<Part2RawInstructionSet>,bool);
#[verifier::opaque]
pub(crate) open spec fn part2_composition_storage_step(input:Part2BoxReference,state:Part2CompositionStorageState,
    limits:crate::ResourceLimits,base:u64)->Result<Part2CompositionStorageState,crate::DecodeError> {
    if input.0.0==crate::jp2::BoxType::COMPOSITION_OPTIONS {
        if state.0.is_some() || state.1.len()>0 {
            Err(part2_image_box_error(base,input.0,crate::MalformedKind::InvalidBoxOrder))
        }else if input.1.len()!=9 {Err(part2_image_box_error(base,input.0,crate::MalformedKind::InvalidBoxLength))}
        else{
            let height=part2_composition_word_at(input.1,0);let width=part2_composition_word_at(input.1,4);
            match part2_validate_composition_dimensions(width,height,&limits,base) {
                Err(error)=>Err(error),Ok(())=>Ok((Some((width,height,input.1[8])),state.1,state.2)),
            }
        }
    }else if input.0.0==crate::jp2::BoxType::INSTRUCTION_SET {
        match state.0 {
            None=>Err(part2_image_box_error(base,input.0,crate::MalformedKind::InvalidBoxOrder)),
            Some(composition)=>match part2_parse_instruction_set(input,composition,base,&limits) {
                Err(error)=>Err(error),Ok(parsed)=>{
                    let count=state.1.len()+1;
                    if count>usize::MAX as nat {Err(part2_palette_arithmetic_error(base))}
                    else if count as u64>crate::limits::resource_layer_limit(&limits) as u64 {
                        Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::Layers,
                            limit:crate::limits::resource_layer_limit(&limits) as u64,actual:count as u64})
                    }else{Ok((state.0,state.1.push(parsed),state.2))}
                },
            },
        }
    }else{Ok((state.0,state.1,true))}
}
pub(crate) open spec fn part2_composition_storage_machine(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64)
    ->Part2HeaderStorageMachine<Part2CompositionStorageState,Part2RawComposition> {
    Part2HeaderStorageMachine {
        payload,base,prepare:|state:Part2CompositionStorageState|Ok(state),
        request:|input:Part2BoxReference,state:Part2CompositionStorageState|
            if input.0.0==crate::jp2::BoxType::INSTRUCTION_SET && state.0.is_some() {
                Some(Part2HeaderStorageRequest::InstructionSet {context:Part2InstructionRequestContext {
                    child:Part2InstructionStorageContext {input,composition:state.0.get_Some_0(),base,limits},before:state.1}})
            }else{None},
        step:|input,state|part2_composition_storage_step(input,state,limits,base),
        finish:|state:Part2CompositionStorageState|part2_composition_finish(state.0,state.1,state.2,base),
    }
}
pub(crate) proof fn part2_composition_storage_machine_valid(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64)
    ensures part2_header_storage_machine_valid(part2_composition_storage_machine(payload,limits,base)),
{
    reveal(part2_composition_storage_step);
    crate::jp2::channel_storage_box_kinds_known();
}
pub(crate) proof fn part2_composition_storage_value(payload:Seq<u8>,reader:Part2BoxReaderState,
    state:Part2CompositionStorageState,limits:crate::ResourceLimits,base:u64)
    ensures part2_header_storage_boxes_value(part2_composition_storage_machine(payload,limits,base),reader,state)
        ==part2_composition_boxes(payload,reader,state.0,state.1,state.2,limits,base),
    decreases payload.len() as int-reader.position as int,
{
    reveal_with_fuel(part2_header_storage_boxes_value,1);reveal_with_fuel(part2_composition_boxes,1);
    reveal(part2_composition_storage_step);
    let next=part2_box_reader_next_ref(reader);
    if let Some(Ok(input))=next.0 {
        if reader.position<next.1.position && next.1.position<=payload.len() {
            if let Ok(updated)=part2_composition_storage_step(input,state,limits,base) {
                part2_composition_storage_value(payload,next.1,updated,limits,base);
            }
        }
    }
}
pub(crate) open spec fn part2_composition_storage_start(input:Part2BoxReference,limits:crate::ResourceLimits)
    ->Result<(u64,Part2BoxReaderState),crate::DecodeError> {
    match part2_box_payload_offset(input.0) {
        Err(error)=>Err(error),Ok(base)=>match part2_box_reader_from_input(input.1,limits) {
            Err(error)=>Err(error),Ok(reader)=>Ok((base,reader)),
        },
    }
}
pub(crate) open spec fn part2_composition_storage_run(input:Part2BoxReference,limits:crate::ResourceLimits,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawComposition> {
    match part2_composition_storage_start(input,limits) {
        Err(error)=>Some((Err(error),events)),
        Ok((base,reader))=>part2_header_storage_boxes_run(part2_composition_storage_machine(input.1,limits,base),
            reader,(None,Seq::empty(),false),events),
    }
}
pub closed spec fn part2_composition_storage_result(input:Part2BoxReference,limits:crate::ResourceLimits,
    result:Result<Part2RawComposition,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_composition_storage_run(input,limits,events),result)
}
pub(crate) proof fn part2_composition_storage_normal(input:Part2BoxReference,limits:crate::ResourceLimits)
    ensures part2_composition_storage_result(input,limits,part2_parse_composition(input,limits)),
{
    let result=part2_parse_composition(input,limits);part2_cold_pure(result);
    if let Ok((base,reader))=part2_composition_storage_start(input,limits) {
        part2_composition_storage_machine_valid(input.1,limits,base);
        part2_composition_storage_value(input.1,reader,(None,Seq::empty(),false),limits,base);
        part2_header_storage_boxes_normal(part2_composition_storage_machine(input.1,limits,base),reader,(None,Seq::empty(),false));
    }
}
pub(crate) proof fn part2_composition_storage_observed(input:Part2BoxReference,limits:crate::ResourceLimits,
    result:Result<Part2RawComposition,crate::DecodeError>)
    requires part2_cold_framed(|events|part2_composition_storage_run(input,limits,events),result),
    ensures part2_composition_storage_result(input,limits,result),
{}
pub(crate) proof fn part2_composition_storage_frames(input:Part2BoxReference,limits:crate::ResourceLimits,
    result:Result<Part2RawComposition,crate::DecodeError>)
    requires part2_composition_storage_result(input,limits,result),
    ensures part2_cold_framed(|events|part2_composition_storage_run(input,limits,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawComposition>|
            (forall|events| #[trigger] other(events)==part2_composition_storage_run(input,limits,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_composition_storage_run(input,limits,events),result);}
}
