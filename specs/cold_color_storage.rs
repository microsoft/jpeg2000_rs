//! Selected opaque ICC ownership with actual copy replies and framed tails.
use super::*;
verus! {
pub struct Part2ColorStorageContext {
    pub input:Part2BoxReference,
    pub base:u64,
}
pub(crate) open spec fn part2_color_profile_count(context:Part2ColorStorageContext)->nat {
    let payload=context.input.1;
    if payload.len()<4 || payload.len()-3>u64::MAX as nat {0}
    else if payload[0]==2 || payload[0]==3 {(payload.len()-3) as nat}else{0}
}
pub(crate) open spec fn part2_color_capacity_run(context:Part2ColorStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_color_profile_count(context);
    if count==0 {Some((Ok(()),events))}else if events.len()==0 {None}else{match events[0] {
        Part2JpipSnapshotEvent::ColorProfileCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=count {None}
            else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}
pub closed spec fn part2_color_capacity_result(context:Part2ColorStorageContext,
    result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_color_capacity_run(context,events),result)
}
pub(crate) proof fn part2_color_capacity_observed(context:Part2ColorStorageContext,
    result:Result<(),crate::DecodeError>)
    requires result==Ok(()) ||
        (result==Err(crate::DecodeError::AllocationFailed) && part2_color_profile_count(context)>0),
    ensures part2_color_capacity_result(context,result),
{
    let count=part2_color_profile_count(context);
    let prefix=if count==0 {Seq::empty()}else{
        seq![Part2JpipSnapshotEvent::ColorProfileCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_color_capacity_run(context,prefix+tail)==Some((result,tail)) by {
        if count==0 {assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_color_capacity_run(context,events),prefix,result));
}
pub(crate) proof fn part2_color_capacity_frames(context:Part2ColorStorageContext,
    result:Result<(),crate::DecodeError>)
    requires part2_color_capacity_result(context,result),
    ensures part2_cold_framed(|events|part2_color_capacity_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_color_capacity_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_color_capacity_run(context,events),result);
}
pub(crate) open spec fn part2_color_storage_run(context:Part2ColorStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ColorSpecification> {
    part2_jpip_snapshot_bind(part2_color_capacity_run(context,events),
        |_:(),rest|Some((part2_parse_color_specification(context.input,context.base),rest)))
}
pub closed spec fn part2_color_storage_result(context:Part2ColorStorageContext,
    result:Result<Part2ColorSpecification,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_color_storage_run(context,events),result)
}
pub(crate) proof fn part2_color_storage_normal(context:Part2ColorStorageContext)
    ensures part2_color_storage_result(context,part2_parse_color_specification(context.input,context.base)),
{
    let result=part2_parse_color_specification(context.input,context.base);
    part2_color_capacity_observed(context,Ok(()));part2_color_capacity_frames(context,Ok(()));
    part2_cold_pure(result);
    part2_cold_bind(|events|part2_color_capacity_run(context,events),
        |_:(),rest|Some((result,rest)),Ok(()),result);
}
pub(crate) proof fn part2_color_storage_refused(context:Part2ColorStorageContext,error:crate::DecodeError)
    requires part2_color_profile_count(context)>0,part2_color_capacity_result(context,Err(error)),
    ensures part2_color_storage_result(context,Err(error)),
{
    part2_color_capacity_frames(context,Err(error));
    part2_cold_bind(|events|part2_color_capacity_run(context,events),
        |_:(),rest|Some((part2_parse_color_specification(context.input,context.base),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_color_storage_frames(context:Part2ColorStorageContext,
    result:Result<Part2ColorSpecification,crate::DecodeError>)
    requires part2_color_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_color_storage_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ColorSpecification>|
            (forall|events| #[trigger] other(events)==part2_color_storage_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_color_storage_run(context,events),result);
}

pub struct Part2ColorGroupStorageContext {
    pub input:Part2BoxReference,
    pub limits:crate::ResourceLimits,
    pub base:u64,
}
pub struct Part2ColorGroupAppendContext {
    pub group:Part2ColorGroupStorageContext,
    pub input:Part2BoxReference,
    pub before:Seq<Part2ColorSpecification>,
    pub parsed:Part2ColorSpecification,
}
pub(crate) open spec fn part2_color_group_append_admitted(context:Part2ColorGroupAppendContext)->bool {
    context.input.0.0==crate::jp2::BoxType::COLOR_SPECIFICATION &&
        part2_parse_color_specification(context.input,context.group.base)==Ok(context.parsed)
}
pub(crate) open spec fn part2_color_group_append_capacity_run(context:Part2ColorGroupAppendContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    if !part2_color_group_append_admitted(context) || events.len()==0 {None}
    else {match events[0] {
        Part2JpipSnapshotEvent::ColorGroupAppendCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=1 {None}
            else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}
pub closed spec fn part2_color_group_append_capacity_result(context:Part2ColorGroupAppendContext,
    result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_color_group_append_capacity_run(context,events),result)
}
pub(crate) proof fn part2_color_group_append_capacity_observed(context:Part2ColorGroupAppendContext,
    result:Result<(),crate::DecodeError>)
    requires part2_color_group_append_admitted(context),
        result==Ok(()) || result==Err(crate::DecodeError::AllocationFailed),
    ensures part2_color_group_append_capacity_result(context,result),
{
    let prefix=seq![Part2JpipSnapshotEvent::ColorGroupAppendCapacity {context,elements:1,succeeded:result.is_ok()}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_color_group_append_capacity_run(context,prefix+tail)==Some((result,tail)) by {
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|part2_color_group_append_capacity_run(context,events),prefix,result));
}
pub(crate) proof fn part2_color_group_append_capacity_frames(context:Part2ColorGroupAppendContext,
    result:Result<(),crate::DecodeError>)
    requires part2_color_group_append_capacity_result(context,result),
    ensures part2_cold_framed(|events|part2_color_group_append_capacity_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_color_group_append_capacity_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_color_group_append_capacity_run(context,events),result);
}
pub(crate) open spec fn part2_color_group_storage_accept(colors:Seq<Part2ColorSpecification>,
    color:Part2ColorSpecification,limits:crate::ResourceLimits)->Result<Seq<Part2ColorSpecification>,crate::DecodeError> {
    let updated=colors.push(color);
    if updated.len() as u64>crate::limits::resource_component_limit(&limits) as u64 {
        Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::Components,
            limit:crate::limits::resource_component_limit(&limits) as u64,actual:updated.len() as u64})
    }else{Ok(updated)}
}
pub(crate) open spec fn part2_color_group_storage_step_value(context:Part2ColorGroupStorageContext,
    input:Part2BoxReference,colors:Seq<Part2ColorSpecification>)->Result<Seq<Part2ColorSpecification>,crate::DecodeError> {
    if input.0.0!=crate::jp2::BoxType::COLOR_SPECIFICATION {
        Err(part2_image_box_error(context.base,input.0,crate::MalformedKind::InvalidBoxContents))
    }else{match part2_parse_color_specification(input,context.base) {
        Err(error)=>Err(error),Ok(color)=>part2_color_group_storage_accept(colors,color,context.limits),
    }}
}
pub(crate) open spec fn part2_color_group_storage_copied_run(context:Part2ColorGroupStorageContext,
    input:Part2BoxReference,colors:Seq<Part2ColorSpecification>,parsed:Part2ColorSpecification,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2ColorSpecification>> {
    part2_jpip_snapshot_bind(part2_color_group_append_capacity_run(
        Part2ColorGroupAppendContext {group:context,input,before:colors,parsed},events),
        |_:(),rest|Some((part2_color_group_storage_accept(colors,parsed,context.limits),rest)))
}
pub(crate) open spec fn part2_color_group_storage_step_run(context:Part2ColorGroupStorageContext,
    input:Part2BoxReference,colors:Seq<Part2ColorSpecification>,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<Seq<Part2ColorSpecification>> {
    if input.0.0!=crate::jp2::BoxType::COLOR_SPECIFICATION {
        Some((Err(part2_image_box_error(context.base,input.0,crate::MalformedKind::InvalidBoxContents)),events))
    }else{part2_jpip_snapshot_bind(part2_color_storage_run(Part2ColorStorageContext {input,base:context.base},events),
        |color:Part2ColorSpecification,rest|part2_color_group_storage_copied_run(context,input,colors,color,rest))}
}
pub(crate) proof fn part2_color_group_storage_step_normal(context:Part2ColorGroupStorageContext,
    input:Part2BoxReference,colors:Seq<Part2ColorSpecification>)
    ensures part2_cold_framed(|events|part2_color_group_storage_step_run(context,input,colors,events),
            part2_color_group_storage_step_value(context,input,colors)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2ColorSpecification>>|
            (forall|events| #[trigger] other(events)==part2_color_group_storage_step_run(context,input,colors,events)) ==>
                #[trigger] part2_cold_framed(other,part2_color_group_storage_step_value(context,input,colors)),
{
    let result=part2_color_group_storage_step_value(context,input,colors);
    part2_cold_pure(result);
    if input.0.0==crate::jp2::BoxType::COLOR_SPECIFICATION {
        let child=Part2ColorStorageContext {input,base:context.base};
        let parsed=part2_parse_color_specification(input,context.base);
        part2_color_storage_normal(child);part2_color_storage_frames(child,parsed);
        if let Ok(color)=parsed {
            let append=Part2ColorGroupAppendContext {group:context,input,before:colors,parsed:color};
            let accepted=part2_color_group_storage_accept(colors,color,context.limits);
            part2_color_group_append_capacity_observed(append,Ok(()));
            part2_color_group_append_capacity_frames(append,Ok(()));
            part2_cold_pure(accepted);
            part2_cold_bind(|events|part2_color_group_append_capacity_run(append,events),
                |_:(),rest|Some((accepted,rest)),Ok(()),accepted);
            part2_decode_eta(|events|part2_color_group_storage_copied_run(context,input,colors,color,events),accepted);
        }
        part2_cold_bind(|events|part2_color_storage_run(child,events),
            |color:Part2ColorSpecification,rest|part2_color_group_storage_copied_run(context,input,colors,color,rest),parsed,result);
    }
    part2_decode_eta(|events|part2_color_group_storage_step_run(context,input,colors,events),result);
}
#[verifier::opaque]
pub(crate) open spec fn part2_color_group_storage_boxes_run(context:Part2ColorGroupStorageContext,
    reader:Part2BoxReaderState,colors:Seq<Part2ColorSpecification>,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<Seq<Part2ColorSpecification>>
    decreases context.input.1.len() as int-reader.position as int,
{
    let next=part2_box_reader_next_ref(reader);
    match next.0 {
        None=>Some((part2_color_group_finish(colors,context.base),events)),
        Some(result)=>if next.1.position<=reader.position || next.1.position>context.input.1.len() {
            Some((Err(part2_resolution_progress_error(context.base,reader.position)),events))
        }else{match result {
            Err(error)=>Some((Err(part2_box_rebase_error(error,context.base)),events)),
            Ok(input)=>part2_jpip_snapshot_bind(part2_color_group_storage_step_run(context,input,colors,events),
                |updated:Seq<Part2ColorSpecification>,rest|part2_color_group_storage_boxes_run(context,next.1,updated,rest)),
        }},
    }
}
pub(crate) proof fn part2_color_group_storage_boxes_normal(context:Part2ColorGroupStorageContext,
    reader:Part2BoxReaderState,colors:Seq<Part2ColorSpecification>)
    ensures part2_cold_framed(|events|part2_color_group_storage_boxes_run(context,reader,colors,events),
            part2_color_group_boxes(context.input.1,reader,colors,context.limits,context.base)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2ColorSpecification>>|
            (forall|events| #[trigger] other(events)==part2_color_group_storage_boxes_run(context,reader,colors,events)) ==>
                #[trigger] part2_cold_framed(other,part2_color_group_boxes(context.input.1,reader,colors,context.limits,context.base)),
    decreases context.input.1.len() as int-reader.position as int,
{
    reveal_with_fuel(part2_color_group_storage_boxes_run,1);reveal_with_fuel(part2_color_group_boxes,1);
    let result=part2_color_group_boxes(context.input.1,reader,colors,context.limits,context.base);
    let next=part2_box_reader_next_ref(reader);
    part2_cold_pure(result);
    if let Some(Ok(input))=next.0 {
        if reader.position<next.1.position && next.1.position<=context.input.1.len() {
            let stepped=part2_color_group_storage_step_value(context,input,colors);
            part2_color_group_storage_step_normal(context,input,colors);
            if let Ok(updated)=stepped {part2_color_group_storage_boxes_normal(context,next.1,updated);}
            part2_cold_bind(|events|part2_color_group_storage_step_run(context,input,colors,events),
                |updated:Seq<Part2ColorSpecification>,rest|part2_color_group_storage_boxes_run(context,next.1,updated,rest),stepped,result);
        }
    }
    part2_decode_eta(|events|part2_color_group_storage_boxes_run(context,reader,colors,events),result);
}
pub(crate) open spec fn part2_color_group_storage_run(context:Part2ColorGroupStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2ColorSpecification>> {
    match part2_box_reader_from_input(context.input.1,context.limits) {
        Err(error)=>Some((Err(error),events)),
        Ok(reader)=>part2_color_group_storage_boxes_run(context,reader,Seq::empty(),events),
    }
}
pub closed spec fn part2_color_group_storage_result(context:Part2ColorGroupStorageContext,
    result:Result<Seq<Part2ColorSpecification>,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_color_group_storage_run(context,events),result)
}
pub(crate) proof fn part2_color_group_storage_normal(context:Part2ColorGroupStorageContext)
    ensures part2_color_group_storage_result(context,part2_parse_color_group(context.input,context.limits,context.base)),
{
    let result=part2_parse_color_group(context.input,context.limits,context.base);
    part2_cold_pure(result);
    if let Ok(reader)=part2_box_reader_from_input(context.input.1,context.limits) {
        part2_color_group_storage_boxes_normal(context,reader,Seq::empty());
    }
}
pub(crate) proof fn part2_color_group_storage_observed(context:Part2ColorGroupStorageContext,
    result:Result<Seq<Part2ColorSpecification>,crate::DecodeError>)
    requires part2_cold_framed(|events|part2_color_group_storage_run(context,events),result),
    ensures part2_color_group_storage_result(context,result),
{}
pub(crate) proof fn part2_color_group_storage_frames(context:Part2ColorGroupStorageContext,
    result:Result<Seq<Part2ColorSpecification>,crate::DecodeError>)
    requires part2_color_group_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_color_group_storage_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2ColorSpecification>>|
            (forall|events| #[trigger] other(events)==part2_color_group_storage_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_color_group_storage_run(context,events),result);
}
pub(crate) open spec fn part2_color_group_storage_advance_prefix(context:Part2ColorGroupStorageContext,
    reader:Part2BoxReaderState,colors:Seq<Part2ColorSpecification>,updated:Seq<Part2ColorSpecification>,
    prefix:Seq<Part2JpipSnapshotEvent>)->bool {
    forall|tail:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_color_group_storage_boxes_run(context,reader,colors,prefix+tail)
        ==part2_color_group_storage_boxes_run(context,part2_box_reader_next_ref(reader).1,updated,tail)
}
pub(crate) proof fn part2_color_group_storage_root_advance(context:Part2ColorGroupStorageContext,
    prefix:Seq<Part2JpipSnapshotEvent>,reader:Part2BoxReaderState,colors:Seq<Part2ColorSpecification>,
    input:Part2BoxReference,updated:Seq<Part2ColorSpecification>)->(extended:Seq<Part2JpipSnapshotEvent>)
    requires part2_cold_phase(|events|part2_color_group_storage_run(context,events),prefix,
            |events|part2_color_group_storage_boxes_run(context,reader,colors,events)),
        part2_box_reader_next_ref(reader).0==Some(Ok(input)),
        reader.position<part2_box_reader_next_ref(reader).1.position<=context.input.1.len(),
        part2_color_group_storage_step_value(context,input,colors)==Ok(updated),
    ensures part2_cold_phase(|events|part2_color_group_storage_run(context,events),extended,
        |events|part2_color_group_storage_boxes_run(context,part2_box_reader_next_ref(reader).1,updated,events)),
{
    part2_color_group_storage_step_normal(context,input,colors);
    let calls=part2_cold_witness(|events|part2_color_group_storage_step_run(context,input,colors,events),Ok(updated));
    reveal_with_fuel(part2_color_group_storage_boxes_run,1);
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_color_group_storage_boxes_run(context,reader,colors,calls+tail)
            ==part2_color_group_storage_boxes_run(context,part2_box_reader_next_ref(reader).1,updated,tail) by {
        part2_cold_prefix_at(|events|part2_color_group_storage_step_run(context,input,colors,events),calls,Ok(updated),tail);
    }
    assert(part2_color_group_storage_advance_prefix(context,reader,colors,updated,calls));
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_color_group_storage_run(context,(prefix+calls)+tail)
        ==part2_color_group_storage_boxes_run(context,part2_box_reader_next_ref(reader).1,updated,tail) by {
        assert((prefix+calls)+tail =~= prefix+(calls+tail));
        assert((|events|part2_color_group_storage_run(context,events))(prefix+(calls+tail))
            ==part2_color_group_storage_boxes_run(context,reader,colors,calls+tail));
    }
    prefix+calls
}
pub(crate) proof fn part2_color_group_storage_root_error(context:Part2ColorGroupStorageContext,
    prefix:Seq<Part2JpipSnapshotEvent>,reader:Part2BoxReaderState,colors:Seq<Part2ColorSpecification>,
    input:Part2BoxReference,error:crate::DecodeError)
    requires part2_cold_phase(|events|part2_color_group_storage_run(context,events),prefix,
            |events|part2_color_group_storage_boxes_run(context,reader,colors,events)),
        part2_box_reader_next_ref(reader).0==Some(Ok(input)),
        reader.position<part2_box_reader_next_ref(reader).1.position<=context.input.1.len(),
        input.0.0==crate::jp2::BoxType::COLOR_SPECIFICATION,
        part2_color_storage_result(Part2ColorStorageContext {input,base:context.base},Err(error)),
    ensures part2_color_group_storage_result(context,Err(error)),
{
    let child=Part2ColorStorageContext {input,base:context.base};
    part2_color_storage_frames(child,Err(error));
    part2_cold_bind(|events|part2_color_storage_run(child,events),
        |color:Part2ColorSpecification,rest|part2_color_group_storage_copied_run(context,input,colors,color,rest),Err(error),Err(error));
    part2_decode_eta(|events|part2_color_group_storage_step_run(context,input,colors,events),Err(error));
    part2_cold_bind(|events|part2_color_group_storage_step_run(context,input,colors,events),
        |updated:Seq<Part2ColorSpecification>,rest|part2_color_group_storage_boxes_run(context,part2_box_reader_next_ref(reader).1,updated,rest),
        Err(error),Err(error));
    reveal_with_fuel(part2_color_group_storage_boxes_run,1);
    part2_decode_eta(|events|part2_color_group_storage_boxes_run(context,reader,colors,events),Err(error));
    part2_cold_prefix_result(|events|part2_color_group_storage_run(context,events),
        |events|part2_color_group_storage_boxes_run(context,reader,colors,events),prefix,Err(error));
}
pub(crate) proof fn part2_color_group_storage_root_append_error(context:Part2ColorGroupAppendContext,
    prefix:Seq<Part2JpipSnapshotEvent>,reader:Part2BoxReaderState,error:crate::DecodeError)
    requires part2_cold_phase(|events|part2_color_group_storage_run(context.group,events),prefix,
            |events|part2_color_group_storage_boxes_run(context.group,reader,context.before,events)),
        part2_box_reader_next_ref(reader).0==Some(Ok(context.input)),
        reader.position<part2_box_reader_next_ref(reader).1.position<=context.group.input.1.len(),
        part2_color_group_append_admitted(context),
        part2_color_storage_result(Part2ColorStorageContext {input:context.input,base:context.group.base},Ok(context.parsed)),
        part2_color_group_append_capacity_result(context,Err(error)),
    ensures part2_color_group_storage_result(context.group,Err(error)),
{
    let group=context.group;let input=context.input;let colors=context.before;let parsed=context.parsed;
    let child=Part2ColorStorageContext {input,base:group.base};
    part2_color_group_append_capacity_frames(context,Err(error));
    part2_cold_bind(|events|part2_color_group_append_capacity_run(context,events),
        |_:(),rest|Some((part2_color_group_storage_accept(colors,parsed,group.limits),rest)),Err(error),Err(error));
    part2_decode_eta(|events|part2_color_group_storage_copied_run(group,input,colors,parsed,events),Err(error));
    part2_color_storage_frames(child,Ok(parsed));
    part2_cold_bind(|events|part2_color_storage_run(child,events),
        |color:Part2ColorSpecification,rest|part2_color_group_storage_copied_run(group,input,colors,color,rest),Ok(parsed),Err(error));
    part2_decode_eta(|events|part2_color_group_storage_step_run(group,input,colors,events),Err(error));
    part2_cold_bind(|events|part2_color_group_storage_step_run(group,input,colors,events),
        |updated:Seq<Part2ColorSpecification>,rest|part2_color_group_storage_boxes_run(group,part2_box_reader_next_ref(reader).1,updated,rest),
        Err(error),Err(error));
    reveal_with_fuel(part2_color_group_storage_boxes_run,1);
    part2_decode_eta(|events|part2_color_group_storage_boxes_run(group,reader,colors,events),Err(error));
    part2_cold_prefix_result(|events|part2_color_group_storage_run(group,events),
        |events|part2_color_group_storage_boxes_run(group,reader,colors,events),prefix,Err(error));
}
}
