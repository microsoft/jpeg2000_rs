//! Reached centered-to-typed output ownership with original numerical results.
use super::*;
verus! {
pub enum Part2TypedCapacityContext {
    Palette {source:Part2TypedComponentOutput,palette:Part2PaletteModel,column:u8},
    Definition {source:Part2TypedComponentOutput,definition:ColorDefinition},
    DefinitionCopy {source:Part2TypedComponentOutput,target:Part2TypedComponentOutput},
    Output {context:Part2OutputStorageContext},
    Copy {source:Part2TypedComponentOutput},
    Image {source:Part1DecodedImageModel,maximum:u64},
    Samples {source:Part1DecodedComponentModel,maximum:u64},
}
pub(crate) open spec fn part2_typed_capacity_count(context:Part2TypedCapacityContext)->nat {
    match context {
        Part2TypedCapacityContext::Palette {source,..}=>part2_typed_sample_count(source.0.samples),
        Part2TypedCapacityContext::Definition {..}=>1,
        Part2TypedCapacityContext::DefinitionCopy {source,..}=>source.1.len(),
        Part2TypedCapacityContext::Output {context}=>part2_output_capacity_count(context),
        Part2TypedCapacityContext::Copy {source}=>part2_typed_sample_count(source.0.samples),
        Part2TypedCapacityContext::Image {source,..}=>source.4.len(),Part2TypedCapacityContext::Samples {source,..}=>source.4.len()}
}
pub(crate) open spec fn part2_typed_capacity_run(context:Part2TypedCapacityContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=part2_typed_capacity_count(context);
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0] {
        Part2Tier1StorageEvent::TypedOutputCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=count {None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) proof fn part2_typed_capacity_observed(context:Part2TypedCapacityContext,response:Result<(),crate::DecodeError>)
    requires response==Ok(()) || (response==Err(crate::DecodeError::AllocationFailed) && part2_typed_capacity_count(context)>0),
    ensures part2_tier1_storage_framed(|calls|part2_typed_capacity_run(context,calls),response),
{
    let count=part2_typed_capacity_count(context);
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::TypedOutputCapacity {context,elements:count,succeeded:response.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_typed_capacity_run(context,prefix+tail)==Some((response,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_typed_capacity_run(context,calls),prefix,response));
}
pub(crate) open spec fn part2_typed_samples_admit(source:Part1DecodedComponentModel,maximum:u64)->Result<(),crate::DecodeError> {
    if source.2.precision==0 || source.2.precision>38{Err(part1_image_error(false))}else{part1_image_byte_budget(source.4.len(),8,maximum)}
}
pub(crate) open spec fn part2_typed_samples_run(source:Part1DecodedComponentModel,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1TypedSampleSequence> {
    match part2_typed_samples_admit(source,maximum) {
        Err(error)=>Some((Err(error),calls)),
        Ok(())=>part2_tier1_storage_bind(part2_typed_capacity_run(Part2TypedCapacityContext::Samples {source,maximum},calls),
            |_:(),rest|Some((part1_decoded_component_typed_samples(source,maximum),rest))),
    }
}
pub closed spec fn part2_typed_samples_result(source:Part1DecodedComponentModel,maximum:u64,result:Result<Part1TypedSampleSequence,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_typed_samples_run(source,maximum,calls),result)
}
pub(crate) proof fn part2_typed_samples_normal(source:Part1DecodedComponentModel,maximum:u64)
    ensures part2_typed_samples_result(source,maximum,part1_decoded_component_typed_samples(source,maximum)),
{
    let result=part1_decoded_component_typed_samples(source,maximum);
    part2_tier1_storage_pure(result);
    if part2_typed_samples_admit(source,maximum).is_ok(){
        let context=Part2TypedCapacityContext::Samples {source,maximum};
        part2_typed_capacity_observed(context,Ok(()));
        part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(context,calls),
            |_:(),rest|Some((part1_decoded_component_typed_samples(source,maximum),rest)),Ok(()),result);
    }
}
pub(crate) proof fn part2_typed_samples_refused(source:Part1DecodedComponentModel,maximum:u64)
    requires part2_typed_samples_admit(source,maximum)==Ok(()),
        part2_tier1_storage_framed(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Samples {source,maximum},calls),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_typed_samples_result(source,maximum,Err(crate::DecodeError::AllocationFailed)),
{
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Samples {source,maximum},calls),
        |_:(),rest|Some((part1_decoded_component_typed_samples(source,maximum),rest)),Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_typed_samples_frames(source:Part1DecodedComponentModel,maximum:u64,result:Result<Part1TypedSampleSequence,crate::DecodeError>)
    requires part2_typed_samples_result(source,maximum,result),
    ensures part2_tier1_storage_framed(|calls|part2_typed_samples_run(source,maximum,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1TypedSampleSequence>|
            (forall|calls| #[trigger] other(calls)==part2_typed_samples_run(source,maximum,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{part2_tier1_storage_eta(|calls|part2_typed_samples_run(source,maximum,calls),result);}
pub type Part2TypedComponents=(Seq<Part1TypedComponentModel>,u64);
pub(crate) open spec fn part2_typed_components_next(components:Seq<Part1DecodedComponentModel>,maximum:u64,index:nat,before:Part2TypedComponents,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2TypedComponents> {
    let source=components[index as int];
    let charged=part1_accumulate_decoded_bytes(source.4.len(),before.1,maximum);
    match charged.0 {
        Err(error)=>Some((Err(error),calls)),
        Ok(())=>part2_tier1_storage_bind(part2_typed_samples_run(source,maximum,calls),
            |samples:Part1TypedSampleSequence,rest|Some((Ok((before.0.push(Part1TypedComponentModel {width:source.0,height:source.1,info:source.2,samples}),charged.1)),rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_typed_components_run(components:Seq<Part1DecodedComponentModel>,maximum:u64,count:nat,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2TypedComponents>
    decreases count,
{
    if count==0{Some((Ok((Seq::empty(),0)),calls))}else{
        part2_tier1_storage_bind(part2_typed_components_run(components,maximum,(count-1) as nat,calls),
            |before:Part2TypedComponents,rest|part2_typed_components_next(components,maximum,(count-1) as nat,before,rest))
    }
}
pub(crate) open spec fn part2_typed_image_run(source:Part1DecodedImageModel,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1DecodedTypedImage> {
    part2_tier1_storage_bind(part2_typed_capacity_run(Part2TypedCapacityContext::Image {source,maximum},calls),
        |_:(),rest|part2_tier1_storage_bind(part2_typed_components_run(source.4,maximum,source.4.len(),rest),
            |converted:Part2TypedComponents,tail|Some((Ok(((source.0,source.1,source.2,source.3),converted.0,Seq::new(converted.0.len(),|_:int|Seq::empty()))),tail))))
}
pub closed spec fn part2_typed_image_result(source:Part1DecodedImageModel,maximum:u64,result:Result<Part1DecodedTypedImage,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_typed_image_run(source,maximum,calls),result)
}
pub(crate) proof fn part2_typed_components_normal(components:Seq<Part1DecodedComponentModel>,maximum:u64,count:nat)
    requires count<=components.len(),
    ensures part2_tier1_storage_framed(|calls|part2_typed_components_run(components,maximum,count,calls),part1_decoded_typed_components(components,maximum,count)),
    decreases count,
{
    reveal_with_fuel(part2_typed_components_run,1);reveal_with_fuel(part1_decoded_typed_components,1);
    let result=part1_decoded_typed_components(components,maximum,count);
    if count==0{part2_tier1_storage_pure(result);}else{
        let prior=part1_decoded_typed_components(components,maximum,(count-1) as nat);
        part2_typed_components_normal(components,maximum,(count-1) as nat);
        if let Ok(before)=prior {
            let source=components[count-1];let charged=part1_accumulate_decoded_bytes(source.4.len(),before.1,maximum);
            if charged.0.is_err(){part2_tier1_storage_pure(result);}else{
                let samples=part1_decoded_component_typed_samples(source,maximum);
                part2_typed_samples_normal(source,maximum);part2_typed_samples_frames(source,maximum,samples);
                if samples.is_ok(){part2_tier1_storage_pure(result);}
                part2_tier1_storage_bind_frame(|calls|part2_typed_samples_run(source,maximum,calls),
                    |samples:Part1TypedSampleSequence,rest|Some((Ok((before.0.push(Part1TypedComponentModel {width:source.0,height:source.1,info:source.2,samples}),charged.1)),rest)),samples,result);
            }
            part2_tier1_storage_eta(|calls|part2_typed_components_next(components,maximum,(count-1) as nat,before,calls),result);
        }
        part2_tier1_storage_bind_frame(|calls|part2_typed_components_run(components,maximum,(count-1) as nat,calls),
            |before:Part2TypedComponents,rest|part2_typed_components_next(components,maximum,(count-1) as nat,before,rest),prior,result);
    }
}
pub(crate) proof fn part2_typed_components_error(components:Seq<Part1DecodedComponentModel>,maximum:u64,from:nat,to:nat,error:crate::DecodeError)
    requires from<=to,
        part2_tier1_storage_framed(|calls|part2_typed_components_run(components,maximum,from,calls),Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_typed_components_run(components,maximum,to,calls),Err(error)),
    decreases to-from,
{
    if from<to{
        reveal_with_fuel(part2_typed_components_run,1);
        part2_typed_components_error(components,maximum,from,(to-1) as nat,error);
        part2_tier1_storage_bind_frame(|calls|part2_typed_components_run(components,maximum,(to-1) as nat,calls),
            |before:Part2TypedComponents,rest|part2_typed_components_next(components,maximum,(to-1) as nat,before,rest),Err(error),Err(error));
    }
}
pub(crate) proof fn part2_typed_image_owner_refused(source:Part1DecodedImageModel,maximum:u64)
    requires part2_tier1_storage_framed(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Image {source,maximum},calls),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_typed_image_result(source,maximum,Err(crate::DecodeError::AllocationFailed)),
{
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Image {source,maximum},calls),
        |_:(),rest|part2_tier1_storage_bind(part2_typed_components_run(source.4,maximum,source.4.len(),rest),
            |converted:Part2TypedComponents,tail|Some((Ok(((source.0,source.1,source.2,source.3),converted.0,Seq::new(converted.0.len(),|_:int|Seq::empty()))),tail))),
        Err(crate::DecodeError::AllocationFailed),Err::<Part1DecodedTypedImage,_>(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_typed_image_component_error(source:Part1DecodedImageModel,maximum:u64,index:nat,before:Part2TypedComponents,error:crate::DecodeError)
    requires index<source.4.len(),part1_decoded_typed_components(source.4,maximum,index)==Ok(before),
        part1_accumulate_decoded_bytes(source.4[index as int].4.len(),before.1,maximum).0==Ok(()),
        part2_typed_samples_result(source.4[index as int],maximum,Err(error)),
    ensures part2_typed_image_result(source,maximum,Err(error)),
{
    reveal_with_fuel(part2_typed_components_run,1);
    let component=source.4[index as int];
    let charged=part1_accumulate_decoded_bytes(component.4.len(),before.1,maximum);
    part2_typed_samples_frames(component,maximum,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_typed_samples_run(component,maximum,calls),
        |samples:Part1TypedSampleSequence,rest|Some((Ok((before.0.push(Part1TypedComponentModel {width:component.0,height:component.1,info:component.2,samples}),charged.1)),rest)),
        Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_typed_components_next(source.4,maximum,index,before,calls),Err(error));
    part2_typed_components_normal(source.4,maximum,index);
    part2_tier1_storage_bind_frame(|calls|part2_typed_components_run(source.4,maximum,index,calls),
        |before:Part2TypedComponents,rest|part2_typed_components_next(source.4,maximum,index,before,rest),Ok(before),Err(error));
    assert(part2_tier1_storage_framed(|calls|part2_typed_components_run(source.4,maximum,index+1,calls),Err(error)));
    part2_typed_components_error(source.4,maximum,index+1,source.4.len(),error);
    part2_tier1_storage_bind_frame(|calls|part2_typed_components_run(source.4,maximum,source.4.len(),calls),
        |converted:Part2TypedComponents,tail|Some((Ok(((source.0,source.1,source.2,source.3),converted.0,Seq::new(converted.0.len(),|_:int|Seq::empty()))),tail)),Err(error),Err::<Part1DecodedTypedImage,_>(error));
    let context=Part2TypedCapacityContext::Image {source,maximum};
    part2_typed_capacity_observed(context,Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(context,calls),
        |_:(),rest|part2_tier1_storage_bind(part2_typed_components_run(source.4,maximum,source.4.len(),rest),
            |converted:Part2TypedComponents,tail|Some((Ok(((source.0,source.1,source.2,source.3),converted.0,Seq::new(converted.0.len(),|_:int|Seq::empty()))),tail))),Ok(()),Err::<Part1DecodedTypedImage,_>(error));
}
pub(crate) proof fn part2_typed_image_frames(source:Part1DecodedImageModel,maximum:u64,result:Result<Part1DecodedTypedImage,crate::DecodeError>)
    requires part2_typed_image_result(source,maximum,result),
    ensures part2_tier1_storage_framed(|calls|part2_typed_image_run(source,maximum,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1DecodedTypedImage>|
            (forall|calls| #[trigger] other(calls)==part2_typed_image_run(source,maximum,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{part2_tier1_storage_eta(|calls|part2_typed_image_run(source,maximum,calls),result);}
pub(crate) open spec fn part2_typed_image_calls_run(source:Part1DecodedImageModel,maximum:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage> {
    if events.len()==0{None}else{match events[0] {
        Part2JpipSnapshotEvent::TypedImageCalls {source:actual,maximum:cap,calls}=>if actual!=source || cap!=maximum{None}else{
            match part2_typed_image_run(source,maximum,calls){Some((result,rest))=>if rest.len()==0{Some((result,events.drop_first()))}else{None},None=>None}
        },
        _=>None,
    }}
}
pub(crate) proof fn part2_typed_image_calls_observed(source:Part1DecodedImageModel,maximum:u64,result:Result<Part1DecodedTypedImage,crate::DecodeError>)
    requires part2_typed_image_result(source,maximum,result),
    ensures part2_cold_framed(|events|part2_typed_image_calls_run(source,maximum,events),result),
{
    part2_typed_image_frames(source,maximum,result);
    let run=|calls|part2_typed_image_run(source,maximum,calls);
    let calls=choose|prefix| #[trigger] part2_tier1_storage_prefix(run,prefix,result);
    assert(calls+Seq::empty() =~= calls);
    assert(run(calls)==Some((result,Seq::empty())));
    let prefix=seq![Part2JpipSnapshotEvent::TypedImageCalls {source,maximum,calls}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_typed_image_calls_run(source,maximum,prefix+tail)==Some((result,tail)) by{
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|part2_typed_image_calls_run(source,maximum,events),prefix,result));
    part2_decode_eta(|events|part2_typed_image_calls_run(source,maximum,events),result);
}
pub(crate) open spec fn part2_typed_layout_nonlinear_value(image:Part1DecodedTypedImage,regions:Seq<Part2NonlinearRegion>,
    limits:&crate::ResourceLimits)->Result<Part1DecodedTypedImage,crate::DecodeError> {
    if regions.len()==0 {Ok(image)}else{
        let outcome=part2_apply_nonlinear_regions(image,regions,crate::limits::resource_decoded_bytes_limit(limits),
            crate::limits::resource_work_limit(limits));
        match outcome.0{Err(error)=>Err(error),Ok(())=>Ok(outcome.1)}
    }
}
pub(crate) open spec fn part2_typed_layout_nonlinear_run(image:Part1DecodedTypedImage,regions:Seq<Part2NonlinearRegion>,
    limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage> {
    if regions.len()==0 {Some((Ok(image),events))}
    else{part2_jpip_snapshot_bind(part2_nlt_image_storage_run(Part2NltImageStorageContext {
        source:image,regions,maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits),
        maximum_work:crate::limits::resource_work_limit(limits)},events),
        |outcome:(Result<(),crate::DecodeError>,Part1DecodedTypedImage),rest|
            Some((match outcome.0 {Err(error)=>Err(error),Ok(())=>Ok(outcome.1)},rest)))}
}
pub(crate) open spec fn part2_typed_layout_after_typed_run(input:Part2DecoderLayoutInput,image:Part1DecodedTypedImage,
    discard:u8,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage> {
    part2_jpip_snapshot_bind(part2_nlt_regions_storage_run(Part2NltRegionStorageContext {input,image,discard},events),
        |regions:Seq<Part2NonlinearRegion>,rest|part2_typed_layout_nonlinear_run(image,regions,limits,rest))
}
pub(crate) proof fn part2_typed_layout_nonlinear_normal(image:Part1DecodedTypedImage,regions:Seq<Part2NonlinearRegion>,limits:&crate::ResourceLimits)
    ensures part2_cold_framed(|events|part2_typed_layout_nonlinear_run(image,regions,limits,events),
        part2_typed_layout_nonlinear_value(image,regions,limits)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage>|
            (forall|events| #[trigger] other(events)==part2_typed_layout_nonlinear_run(image,regions,limits,events)) ==>
                #[trigger] part2_cold_framed(other,part2_typed_layout_nonlinear_value(image,regions,limits)),
{
    let context=Part2NltImageStorageContext {source:image,regions,maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits),
        maximum_work:crate::limits::resource_work_limit(limits)};
    let outcome=part2_apply_nonlinear_regions(image,regions,context.maximum_bytes,context.maximum_work);
    let result=if regions.len()==0{Ok(image)}else{match outcome.0{Err(error)=>Err(error),Ok(())=>Ok(outcome.1)}};
    part2_cold_pure(result);
    if regions.len()>0 {
        part2_nlt_image_storage_normal(context);part2_nlt_image_storage_frames(context,outcome);
        part2_cold_bind(|events|part2_nlt_image_storage_run(context,events),
            |outcome:(Result<(),crate::DecodeError>,Part1DecodedTypedImage),rest|
                Some((match outcome.0{Err(error)=>Err(error),Ok(())=>Ok(outcome.1)},rest)),Ok(outcome),result);
    }
    part2_decode_eta(|events|part2_typed_layout_nonlinear_run(image,regions,limits,events),result);
}
pub(crate) proof fn part2_typed_layout_after_typed_normal(input:Part2DecoderLayoutInput,image:Part1DecodedTypedImage,
    discard:u8,limits:&crate::ResourceLimits)
    ensures part2_cold_framed(|events|part2_typed_layout_after_typed_run(input,image,discard,limits,events),
            part2_typed_layout_after_typed(input,image,discard,limits)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage>|
            (forall|events| #[trigger] other(events)==part2_typed_layout_after_typed_run(input,image,discard,limits,events)) ==>
                #[trigger] part2_cold_framed(other,part2_typed_layout_after_typed(input,image,discard,limits)),
{
    let context=Part2NltRegionStorageContext {input,image,discard};
    let regions=part2_collect_nonlinear_regions_input(input,image,discard);
    part2_nlt_regions_storage_normal(context);part2_nlt_regions_storage_frames(context,regions);
    if let Ok(regions)=regions {part2_typed_layout_nonlinear_normal(image,regions,limits);}
    part2_cold_bind(|events|part2_nlt_regions_storage_run(context,events),
        |regions:Seq<Part2NonlinearRegion>,rest|part2_typed_layout_nonlinear_run(image,regions,limits,rest),
        regions,part2_typed_layout_after_typed(input,image,discard,limits));
    part2_decode_eta(|events|part2_typed_layout_after_typed_run(input,image,discard,limits,events),
        part2_typed_layout_after_typed(input,image,discard,limits));
}
pub(crate) open spec fn part2_typed_layout_run(input:Part2DecoderLayoutInput,source:Part1DecodedImageModel,discard:u8,limits:&crate::ResourceLimits,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage> {
    part2_jpip_snapshot_bind(part2_typed_image_calls_run(source,crate::limits::resource_decoded_bytes_limit(limits),events),
        |image:Part1DecodedTypedImage,rest|part2_typed_layout_after_typed_run(input,image,discard,limits,rest))
}
pub closed spec fn part2_typed_layout_result(input:Part2DecoderLayoutInput,source:Part1DecodedImageModel,discard:u8,limits:&crate::ResourceLimits,
    result:Result<Part1DecodedTypedImage,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_typed_layout_run(input,source,discard,limits,events),result)
}
pub(crate) proof fn part2_typed_layout_normal(input:Part2DecoderLayoutInput,source:Part1DecodedImageModel,discard:u8,limits:&crate::ResourceLimits)
    ensures part2_typed_layout_result(input,source,discard,limits,part2_typed_layout_input(input,source,discard,limits)),
{
    let maximum=crate::limits::resource_decoded_bytes_limit(limits);
    let converted=part1_decoded_image_typed(source,maximum);
    part2_typed_image_normal(source,maximum);part2_typed_image_calls_observed(source,maximum,converted);
    if let Ok(image)=converted{part2_typed_layout_after_typed_normal(input,image,discard,limits);}
    part2_cold_bind(|events|part2_typed_image_calls_run(source,maximum,events),
        |image:Part1DecodedTypedImage,rest|part2_typed_layout_after_typed_run(input,image,discard,limits,rest),converted,part2_typed_layout_input(input,source,discard,limits));
}
pub(crate) proof fn part2_typed_layout_conversion_error(input:Part2DecoderLayoutInput,source:Part1DecodedImageModel,discard:u8,limits:&crate::ResourceLimits,error:crate::DecodeError)
    requires part2_typed_image_result(source,crate::limits::resource_decoded_bytes_limit(limits),Err(error)),
    ensures part2_typed_layout_result(input,source,discard,limits,Err(error)),
{
    part2_typed_image_calls_observed(source,crate::limits::resource_decoded_bytes_limit(limits),Err(error));
    part2_cold_bind(|events|part2_typed_image_calls_run(source,crate::limits::resource_decoded_bytes_limit(limits),events),
        |image:Part1DecodedTypedImage,rest|part2_typed_layout_after_typed_run(input,image,discard,limits,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_typed_layout_regions_error(input:Part2DecoderLayoutInput,source:Part1DecodedImageModel,discard:u8,
    limits:&crate::ResourceLimits,image:Part1DecodedTypedImage,error:crate::DecodeError)
    requires part2_typed_image_result(source,crate::limits::resource_decoded_bytes_limit(limits),Ok(image)),
        part2_nlt_regions_storage_result(Part2NltRegionStorageContext {input,image,discard},Err(error)),
    ensures part2_typed_layout_result(input,source,discard,limits,Err(error)),
{
    let context=Part2NltRegionStorageContext {input,image,discard};
    part2_nlt_regions_storage_frames(context,Err(error));
    part2_cold_bind(|events|part2_nlt_regions_storage_run(context,events),
        |regions:Seq<Part2NonlinearRegion>,rest|part2_typed_layout_nonlinear_run(image,regions,limits,rest),Err(error),Err(error));
    part2_decode_eta(|events|part2_typed_layout_after_typed_run(input,image,discard,limits,events),Err(error));
    part2_typed_image_calls_observed(source,crate::limits::resource_decoded_bytes_limit(limits),Ok(image));
    part2_cold_bind(|events|part2_typed_image_calls_run(source,crate::limits::resource_decoded_bytes_limit(limits),events),
        |image:Part1DecodedTypedImage,rest|part2_typed_layout_after_typed_run(input,image,discard,limits,rest),Ok(image),Err(error));
}
pub(crate) proof fn part2_typed_layout_nonlinear_error(input:Part2DecoderLayoutInput,source:Part1DecodedImageModel,discard:u8,
    limits:&crate::ResourceLimits,image:Part1DecodedTypedImage,regions:Seq<Part2NonlinearRegion>,
    after:Part1DecodedTypedImage,error:crate::DecodeError)
    requires part2_typed_image_result(source,crate::limits::resource_decoded_bytes_limit(limits),Ok(image)),
        part2_nlt_regions_storage_result(Part2NltRegionStorageContext {input,image,discard},Ok(regions)),regions.len()>0,
        part2_nlt_image_storage_result(Part2NltImageStorageContext {source:image,regions,
            maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits),maximum_work:crate::limits::resource_work_limit(limits)},(Err(error),after)),
    ensures part2_typed_layout_result(input,source,discard,limits,Err(error)),
{
    let context=Part2NltImageStorageContext {source:image,regions,
        maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits),maximum_work:crate::limits::resource_work_limit(limits)};
    part2_nlt_image_storage_frames(context,(Err(error),after));
    part2_cold_pure(Err::<Part1DecodedTypedImage,crate::DecodeError>(error));
    part2_cold_bind(|events|part2_nlt_image_storage_run(context,events),
        |outcome:(Result<(),crate::DecodeError>,Part1DecodedTypedImage),rest|
            Some((match outcome.0{Err(error)=>Err(error),Ok(())=>Ok(outcome.1)},rest)),Ok((Err(error),after)),Err(error));
    part2_decode_eta(|events|part2_typed_layout_nonlinear_run(image,regions,limits,events),Err(error));
    let collected=Part2NltRegionStorageContext {input,image,discard};
    part2_nlt_regions_storage_frames(collected,Ok(regions));
    part2_cold_bind(|events|part2_nlt_regions_storage_run(collected,events),
        |regions:Seq<Part2NonlinearRegion>,rest|part2_typed_layout_nonlinear_run(image,regions,limits,rest),Ok(regions),Err(error));
    part2_decode_eta(|events|part2_typed_layout_after_typed_run(input,image,discard,limits,events),Err(error));
    part2_typed_image_calls_observed(source,crate::limits::resource_decoded_bytes_limit(limits),Ok(image));
    part2_cold_bind(|events|part2_typed_image_calls_run(source,crate::limits::resource_decoded_bytes_limit(limits),events),
        |image:Part1DecodedTypedImage,rest|part2_typed_layout_after_typed_run(input,image,discard,limits,rest),Ok(image),Err(error));
}
pub(crate) proof fn part2_typed_layout_frames(input:Part2DecoderLayoutInput,source:Part1DecodedImageModel,discard:u8,limits:&crate::ResourceLimits,
    result:Result<Part1DecodedTypedImage,crate::DecodeError>)
    requires part2_typed_layout_result(input,source,discard,limits,result),
    ensures part2_cold_framed(|events|part2_typed_layout_run(input,source,discard,limits,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage>|
            (forall|events| #[trigger] other(events)==part2_typed_layout_run(input,source,discard,limits,events)) ==> #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_typed_layout_run(input,source,discard,limits,events),result);}
pub(crate) proof fn part2_typed_image_normal(source:Part1DecodedImageModel,maximum:u64)
    ensures part2_typed_image_result(source,maximum,part1_decoded_image_typed(source,maximum)),
{
    let converted=part1_decoded_typed_components(source.4,maximum,source.4.len());let result=part1_decoded_image_typed(source,maximum);
    part2_typed_components_normal(source.4,maximum,source.4.len());
    if converted.is_ok(){part2_tier1_storage_pure(result);}
    part2_tier1_storage_bind_frame(|calls|part2_typed_components_run(source.4,maximum,source.4.len(),calls),
        |converted:Part2TypedComponents,tail|Some((Ok(((source.0,source.1,source.2,source.3),converted.0,Seq::new(converted.0.len(),|_:int|Seq::empty()))),tail)),converted,result);
    let context=Part2TypedCapacityContext::Image {source,maximum};
    part2_typed_capacity_observed(context,Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(context,calls),
        |_:(),rest|part2_tier1_storage_bind(part2_typed_components_run(source.4,maximum,source.4.len(),rest),
            |converted:Part2TypedComponents,tail|Some((Ok(((source.0,source.1,source.2,source.3),converted.0,Seq::new(converted.0.len(),|_:int|Seq::empty()))),tail))),Ok(()),result);
}
}
