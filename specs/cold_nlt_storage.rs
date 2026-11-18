//! Reached nonlinear scratch and target ownership from actual source/regions.
use super::*;
verus! {
pub struct Part2NltComponentStorageContext {
    pub source:Part1TypedComponentModel,
    pub number:u16,
    pub regions:Seq<Part2NonlinearRegion>,
    pub maximum_bytes:u64,
    pub maximum_work:u64,
    pub initial_work:u64,
}
pub enum Part2NltCapacityRole {Scratch,SignedSamples,UnsignedSamples}
pub(crate) open spec fn part2_nlt_component_region_state(context:Part2NltComponentStorageContext)
    ->Result<Part2NltScratch,crate::DecodeError> {
    part2_nlt_component_regions(context.source,context.number,context.regions,0,context.maximum_work,Part2NltScratch {
        output:Seq::new(part2_nlt_sample_count(context.source.samples),|_:int|None),
        target:None,work:context.initial_work})
}
pub(crate) open spec fn part2_nlt_capacity_count(context:Part2NltComponentStorageContext,role:Part2NltCapacityRole)->nat {
    match role {
        Part2NltCapacityRole::Scratch=>part2_nlt_sample_count(context.source.samples),
        _=>match part2_nlt_component_region_state(context) {
            Err(_)=>0,Ok(state)=>match state.target {
                None=>0,Some((_,signed))=>if !part1_image_byte_budget(state.output.len(),8,context.maximum_bytes).is_ok() {0}
                    else if (role==Part2NltCapacityRole::SignedSamples)==signed {state.output.len()}else{0},
            },
        },
    }
}
pub(crate) open spec fn part2_nlt_capacity_run(context:Part2NltComponentStorageContext,role:Part2NltCapacityRole,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_nlt_capacity_count(context,role);
    if count==0 {Some((Ok(()),events))}else if events.len()==0 {None}else{match events[0] {
        Part2JpipSnapshotEvent::NltCapacity {context:actual,role:actual_role,elements,succeeded}=>
            if actual!=context || actual_role!=role || elements!=count {None}
            else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}
pub closed spec fn part2_nlt_capacity_result(context:Part2NltComponentStorageContext,role:Part2NltCapacityRole,
    result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_nlt_capacity_run(context,role,events),result)
}
pub(crate) proof fn part2_nlt_capacity_observed(context:Part2NltComponentStorageContext,role:Part2NltCapacityRole,
    result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (result==Err(crate::DecodeError::AllocationFailed) && part2_nlt_capacity_count(context,role)>0),
    ensures part2_nlt_capacity_result(context,role,result),
{
    let count=part2_nlt_capacity_count(context,role);
    let prefix=if count==0 {Seq::empty()}else{
        seq![Part2JpipSnapshotEvent::NltCapacity {context,role,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_nlt_capacity_run(context,role,prefix+tail)==Some((result,tail)) by {
        if count==0 {assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_nlt_capacity_run(context,role,events),prefix,result));
}
pub(crate) proof fn part2_nlt_capacity_frames(context:Part2NltComponentStorageContext,role:Part2NltCapacityRole,
    result:Result<(),crate::DecodeError>)
    requires part2_nlt_capacity_result(context,role,result),
    ensures part2_cold_framed(|events|part2_nlt_capacity_run(context,role,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_nlt_capacity_run(context,role,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_nlt_capacity_run(context,role,events),result);}
pub(crate) open spec fn part2_nlt_component_after_scratch(context:Part2NltComponentStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Part1TypedComponentModel,u64)> {
    match part2_nlt_component_region_state(context) {
        Err(error)=>Some((Err(error),events)),
        Ok(state)=>match state.target {
            None=>Some((part2_nlt_finish_component(context.source,state,context.maximum_bytes),events)),
            Some((_,signed))=>match part1_image_byte_budget(state.output.len(),8,context.maximum_bytes) {
                Err(error)=>Some((Err(error),events)),
                Ok(())=>part2_jpip_snapshot_bind(part2_nlt_capacity_run(context,
                    if signed{Part2NltCapacityRole::SignedSamples}else{Part2NltCapacityRole::UnsignedSamples},events),
                    |_:(),rest|Some((part2_nlt_finish_component(context.source,state,context.maximum_bytes),rest))),
            },
        },
    }
}
pub(crate) open spec fn part2_nlt_component_storage_run(context:Part2NltComponentStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Part1TypedComponentModel,u64)> {
    part2_jpip_snapshot_bind(part2_nlt_capacity_run(context,Part2NltCapacityRole::Scratch,events),
        |_:(),rest|part2_nlt_component_after_scratch(context,rest))
}
pub(crate) open spec fn part2_nlt_component_storage_outcome(
    result:(Result<u64,crate::DecodeError>,Part1TypedComponentModel))->Result<(Part1TypedComponentModel,u64),crate::DecodeError> {
    match result.0 {Err(error)=>Err(error),Ok(work)=>Ok((result.1,work))}
}
pub closed spec fn part2_nlt_component_storage_result(context:Part2NltComponentStorageContext,
    result:(Result<u64,crate::DecodeError>,Part1TypedComponentModel))->bool {
    (result.0.is_err() ==> result.1==context.source) &&
        part2_cold_framed(|events|part2_nlt_component_storage_run(context,events),part2_nlt_component_storage_outcome(result))
}
pub(crate) proof fn part2_nlt_component_storage_normal(context:Part2NltComponentStorageContext)
    ensures part2_nlt_component_storage_result(context,part2_nlt_component_mutation(context.source,context.number,
        context.regions,context.maximum_bytes,context.maximum_work,context.initial_work)),
{
    reveal(part2_nlt_component_mutation);
    let result=part2_nlt_component(context.source,context.number,context.regions,
        context.maximum_bytes,context.maximum_work,context.initial_work);
    part2_cold_pure(result);
    if let Ok(state)=part2_nlt_component_region_state(context) {
        if let Some((_,signed))=state.target {
            if part1_image_byte_budget(state.output.len(),8,context.maximum_bytes).is_ok() {
                let role=if signed{Part2NltCapacityRole::SignedSamples}else{Part2NltCapacityRole::UnsignedSamples};
                part2_nlt_capacity_observed(context,role,Ok(()));part2_nlt_capacity_frames(context,role,Ok(()));
                part2_cold_pure(part2_nlt_finish_component(context.source,state,context.maximum_bytes));
                part2_cold_bind(|events|part2_nlt_capacity_run(context,role,events),
                    |_:(),rest|Some((part2_nlt_finish_component(context.source,state,context.maximum_bytes),rest)),Ok(()),result);
            }
        }
    }
    part2_decode_eta(|events|part2_nlt_component_after_scratch(context,events),result);
    part2_nlt_capacity_observed(context,Part2NltCapacityRole::Scratch,Ok(()));
    part2_nlt_capacity_frames(context,Part2NltCapacityRole::Scratch,Ok(()));
    part2_cold_bind(|events|part2_nlt_capacity_run(context,Part2NltCapacityRole::Scratch,events),
        |_:(),rest|part2_nlt_component_after_scratch(context,rest),Ok(()),result);
}
pub(crate) proof fn part2_nlt_component_scratch_refused(context:Part2NltComponentStorageContext,error:crate::DecodeError)
    requires part2_nlt_capacity_result(context,Part2NltCapacityRole::Scratch,Err(error)),
    ensures part2_nlt_component_storage_result(context,(Err(error),context.source)),
{
    part2_nlt_capacity_frames(context,Part2NltCapacityRole::Scratch,Err(error));
    part2_cold_bind(|events|part2_nlt_capacity_run(context,Part2NltCapacityRole::Scratch,events),
        |_:(),rest|part2_nlt_component_after_scratch(context,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_nlt_component_samples_refused(context:Part2NltComponentStorageContext,
    state:Part2NltScratch,signed:bool,error:crate::DecodeError)
    requires part2_nlt_component_region_state(context)==Ok(state),state.target.is_some(),
        state.target.get_Some_0().1==signed,
        part1_image_byte_budget(state.output.len(),8,context.maximum_bytes)==Ok(()),
        part2_nlt_capacity_result(context,Part2NltCapacityRole::Scratch,Ok(())),
        part2_nlt_capacity_result(context,
            if signed{Part2NltCapacityRole::SignedSamples}else{Part2NltCapacityRole::UnsignedSamples},Err(error)),
    ensures part2_nlt_component_storage_result(context,(Err(error),context.source)),
{
    let role=if signed{Part2NltCapacityRole::SignedSamples}else{Part2NltCapacityRole::UnsignedSamples};
    part2_nlt_capacity_frames(context,role,Err(error));
    part2_cold_bind(|events|part2_nlt_capacity_run(context,role,events),
        |_:(),rest|Some((part2_nlt_finish_component(context.source,state,context.maximum_bytes),rest)),Err(error),Err(error));
    part2_decode_eta(|events|part2_nlt_component_after_scratch(context,events),Err(error));
    part2_nlt_capacity_frames(context,Part2NltCapacityRole::Scratch,Ok(()));
    part2_cold_bind(|events|part2_nlt_capacity_run(context,Part2NltCapacityRole::Scratch,events),
        |_:(),rest|part2_nlt_component_after_scratch(context,rest),Ok(()),Err(error));
}
pub(crate) proof fn part2_nlt_component_storage_frames(context:Part2NltComponentStorageContext,
    result:(Result<u64,crate::DecodeError>,Part1TypedComponentModel))
    requires part2_nlt_component_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_nlt_component_storage_run(context,events),part2_nlt_component_storage_outcome(result)),
        result.0.is_err() ==> result.1==context.source,
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Part1TypedComponentModel,u64)>|
            (forall|events| #[trigger] other(events)==part2_nlt_component_storage_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,part2_nlt_component_storage_outcome(result)),
{part2_decode_eta(|events|part2_nlt_component_storage_run(context,events),part2_nlt_component_storage_outcome(result));}

pub struct Part2NltImageStorageContext {
    pub source:Part1DecodedTypedImage,
    pub regions:Seq<Part2NonlinearRegion>,
    pub maximum_bytes:u64,
    pub maximum_work:u64,
}
pub(crate) open spec fn part2_nlt_image_component_context(context:Part2NltImageStorageContext,
    image:Part1DecodedTypedImage,position:nat,work:u64)->Part2NltComponentStorageContext {
    Part2NltComponentStorageContext {source:image.1[position as int],number:position as u16,
        regions:context.regions,maximum_bytes:context.maximum_bytes,maximum_work:context.maximum_work,initial_work:work}
}
pub(crate) open spec fn part2_nlt_image_component_updated(image:Part1DecodedTypedImage,position:nat,
    component:Part1TypedComponentModel)->Part1DecodedTypedImage {
    (image.0,image.1.update(position as int,component),image.2)
}
#[verifier::opaque]
pub(crate) open spec fn part2_nlt_image_components_storage_run(context:Part2NltImageStorageContext,
    image:Part1DecodedTypedImage,position:nat,work:u64,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<(Result<(),crate::DecodeError>,Part1DecodedTypedImage)>
    decreases image.1.len()-position,
{
    if position>=image.1.len() {Some((Ok((Ok(()),image)),events))}
    else if position>u16::MAX {Some((Ok((Err(part1_transform_error(true)),image)),events))}
    else{part2_header_storage_resume(part2_nlt_component_storage_run(
        part2_nlt_image_component_context(context,image,position,work),events),
        |outcome:Result<(Part1TypedComponentModel,u64),crate::DecodeError>,rest|match outcome {
            Err(error)=>Some((Ok((Err(error),image)),rest)),
            Ok((component,next_work))=>part2_nlt_image_components_storage_run(context,
                part2_nlt_image_component_updated(image,position,component),position+1,next_work,rest),
        })}
}
pub(crate) open spec fn part2_nlt_image_storage_run(context:Part2NltImageStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Result<(),crate::DecodeError>,Part1DecodedTypedImage)> {
    part2_nlt_image_components_storage_run(context,context.source,0,0,events)
}
pub closed spec fn part2_nlt_image_storage_result(context:Part2NltImageStorageContext,
    result:(Result<(),crate::DecodeError>,Part1DecodedTypedImage))->bool {
    part2_cold_framed(|events|part2_nlt_image_storage_run(context,events),Ok(result))
}
pub(crate) proof fn part2_nlt_image_components_storage_normal(context:Part2NltImageStorageContext,
    image:Part1DecodedTypedImage,position:nat,work:u64)
    ensures part2_cold_framed(|events|part2_nlt_image_components_storage_run(context,image,position,work,events),
        Ok((part2_nlt_apply_components(image,position,context.regions,context.maximum_bytes,context.maximum_work,work).1,
            part2_nlt_apply_components(image,position,context.regions,context.maximum_bytes,context.maximum_work,work).0))),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Result<(),crate::DecodeError>,Part1DecodedTypedImage)>|
            (forall|events| #[trigger] other(events)==part2_nlt_image_components_storage_run(context,image,position,work,events)) ==>
                #[trigger] part2_cold_framed(other,Ok((
                    part2_nlt_apply_components(image,position,context.regions,context.maximum_bytes,context.maximum_work,work).1,
                    part2_nlt_apply_components(image,position,context.regions,context.maximum_bytes,context.maximum_work,work).0))),
    decreases image.1.len()-position,
{
    reveal_with_fuel(part2_nlt_image_components_storage_run,1);reveal_with_fuel(part2_nlt_apply_components,1);
    let ordinary=part2_nlt_apply_components(image,position,context.regions,context.maximum_bytes,context.maximum_work,work);
    let result=(ordinary.1,ordinary.0);
    part2_cold_pure(Ok(result));
    if position<image.1.len() && position<=u16::MAX {
        let child=part2_nlt_image_component_context(context,image,position,work);
        let parsed=part2_nlt_component(child.source,child.number,child.regions,child.maximum_bytes,child.maximum_work,child.initial_work);
        let mutation=part2_nlt_component_mutation(child.source,child.number,child.regions,child.maximum_bytes,child.maximum_work,child.initial_work);
        part2_nlt_component_storage_normal(child);part2_nlt_component_storage_frames(child,mutation);
        reveal(part2_nlt_component_mutation);
        assert(part2_nlt_component_storage_outcome(mutation)==parsed);
        if let Ok((component,next_work))=parsed {
            part2_nlt_image_components_storage_normal(context,part2_nlt_image_component_updated(image,position,component),
                position+1,next_work);
        }
        part2_header_storage_resume_frame(|events|part2_nlt_component_storage_run(child,events),
            |outcome:Result<(Part1TypedComponentModel,u64),crate::DecodeError>,rest|match outcome {
                Err(error)=>Some((Ok((Err(error),image)),rest)),
                Ok((component,next_work))=>part2_nlt_image_components_storage_run(context,
                    part2_nlt_image_component_updated(image,position,component),position+1,next_work,rest),
            },parsed,Ok(result));
    }
    part2_decode_eta(|events|part2_nlt_image_components_storage_run(context,image,position,work,events),Ok(result));
}
pub(crate) proof fn part2_nlt_image_storage_normal(context:Part2NltImageStorageContext)
    ensures part2_nlt_image_storage_result(context,part2_apply_nonlinear_regions(
        context.source,context.regions,context.maximum_bytes,context.maximum_work)),
{
    reveal(part2_apply_nonlinear_regions);
    part2_nlt_image_components_storage_normal(context,context.source,0,0);
}
pub(crate) proof fn part2_nlt_image_storage_frames(context:Part2NltImageStorageContext,
    result:(Result<(),crate::DecodeError>,Part1DecodedTypedImage))
    requires part2_nlt_image_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_nlt_image_storage_run(context,events),Ok(result)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Result<(),crate::DecodeError>,Part1DecodedTypedImage)>|
            (forall|events| #[trigger] other(events)==part2_nlt_image_storage_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,Ok(result)),
{part2_decode_eta(|events|part2_nlt_image_storage_run(context,events),Ok(result));}
pub(crate) proof fn part2_nlt_image_storage_observed(context:Part2NltImageStorageContext,
    result:(Result<(),crate::DecodeError>,Part1DecodedTypedImage))
    requires part2_cold_framed(|events|part2_nlt_image_storage_run(context,events),Ok(result)),
    ensures part2_nlt_image_storage_result(context,result),
{}
pub(crate) proof fn part2_nlt_image_storage_component_error(context:Part2NltImageStorageContext,
    prefix:Seq<Part2JpipSnapshotEvent>,image:Part1DecodedTypedImage,position:nat,work:u64,error:crate::DecodeError)
    requires position<image.1.len(),position<=u16::MAX,
        part2_cold_phase(|events|part2_nlt_image_storage_run(context,events),prefix,
            |events|part2_nlt_image_components_storage_run(context,image,position,work,events)),
        part2_nlt_component_storage_result(part2_nlt_image_component_context(context,image,position,work),
            (Err(error),image.1[position as int])),
    ensures part2_nlt_image_storage_result(context,(Err(error),image)),
{
    let child=part2_nlt_image_component_context(context,image,position,work);
    part2_nlt_component_storage_frames(child,(Err(error),image.1[position as int]));
    part2_cold_pure(Ok((Err::<(),crate::DecodeError>(error),image)));
    part2_header_storage_resume_frame(|events|part2_nlt_component_storage_run(child,events),
        |outcome:Result<(Part1TypedComponentModel,u64),crate::DecodeError>,rest|match outcome {
            Err(error)=>Some((Ok((Err(error),image)),rest)),
            Ok((component,next_work))=>part2_nlt_image_components_storage_run(context,
                part2_nlt_image_component_updated(image,position,component),position+1,next_work,rest),
        },Err(error),Ok((Err(error),image)));
    reveal_with_fuel(part2_nlt_image_components_storage_run,1);
    part2_decode_eta(|events|part2_nlt_image_components_storage_run(context,image,position,work,events),Ok((Err(error),image)));
    part2_cold_prefix_result(|events|part2_nlt_image_storage_run(context,events),
        |events|part2_nlt_image_components_storage_run(context,image,position,work,events),prefix,Ok((Err(error),image)));
}
pub(crate) proof fn part2_nlt_image_storage_advance(context:Part2NltImageStorageContext,
    prefix:Seq<Part2JpipSnapshotEvent>,image:Part1DecodedTypedImage,position:nat,work:u64,
    component:Part1TypedComponentModel,next_work:u64)->(extended:Seq<Part2JpipSnapshotEvent>)
    requires position<image.1.len(),position<=u16::MAX,
        part2_cold_phase(|events|part2_nlt_image_storage_run(context,events),prefix,
            |events|part2_nlt_image_components_storage_run(context,image,position,work,events)),
        part2_nlt_component_storage_result(part2_nlt_image_component_context(context,image,position,work),
            (Ok(next_work),component)),
    ensures part2_cold_phase(|events|part2_nlt_image_storage_run(context,events),extended,
        |events|part2_nlt_image_components_storage_run(context,part2_nlt_image_component_updated(image,position,component),
            position+1,next_work,events)),
{
    let child=part2_nlt_image_component_context(context,image,position,work);
    part2_nlt_component_storage_frames(child,(Ok(next_work),component));
    let calls=part2_cold_witness(|events|part2_nlt_component_storage_run(child,events),Ok((component,next_work)));
    reveal_with_fuel(part2_nlt_image_components_storage_run,1);
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_nlt_image_components_storage_run(context,image,position,work,calls+tail)
        ==part2_nlt_image_components_storage_run(context,part2_nlt_image_component_updated(image,position,component),
            position+1,next_work,tail) by {
        part2_cold_prefix_at(|events|part2_nlt_component_storage_run(child,events),calls,Ok((component,next_work)),tail);
    }
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_nlt_image_storage_run(context,(prefix+calls)+tail)
        ==part2_nlt_image_components_storage_run(context,part2_nlt_image_component_updated(image,position,component),
            position+1,next_work,tail) by {
        assert((prefix+calls)+tail =~= prefix+(calls+tail));
        assert((|events|part2_nlt_image_storage_run(context,events))(prefix+(calls+tail))
            ==part2_nlt_image_components_storage_run(context,image,position,work,calls+tail));
    }
    prefix+calls
}
pub(crate) proof fn part2_nlt_image_storage_boundary(context:Part2NltImageStorageContext,
    prefix:Seq<Part2JpipSnapshotEvent>,image:Part1DecodedTypedImage,position:nat,work:u64)
    requires position>=image.1.len() || position>u16::MAX,
        part2_cold_phase(|events|part2_nlt_image_storage_run(context,events),prefix,
            |events|part2_nlt_image_components_storage_run(context,image,position,work,events)),
    ensures part2_nlt_image_storage_result(context,
        (if position>=image.1.len(){Ok(())}else{Err(part1_transform_error(true))},image)),
{
    let result=(if position>=image.1.len(){Ok(())}else{Err(part1_transform_error(true))},image);
    part2_cold_pure(Ok(result));
    reveal_with_fuel(part2_nlt_image_components_storage_run,1);
    part2_decode_eta(|events|part2_nlt_image_components_storage_run(context,image,position,work,events),Ok(result));
    part2_cold_prefix_result(|events|part2_nlt_image_storage_run(context,events),
        |events|part2_nlt_image_components_storage_run(context,image,position,work,events),prefix,Ok(result));
}
}
