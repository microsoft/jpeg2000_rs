//! Real ordered MCT collection/stage composition of spectral line responses.
use super::*;
verus! {
pub(crate) enum Part2MctViewSource {
    Decoded {source:Part1DecodedImageModel},
    Prepared {source:Seq<Part1AssemblyTile>},
}
pub(crate) open spec fn part2_mct_view_count(source:Part2MctViewSource)->nat {
    match source {Part2MctViewSource::Decoded {source}=>source.4.len(),Part2MctViewSource::Prepared {source}=>source.len()}
}
pub(crate) open spec fn part2_mct_view_run(source:Part2MctViewSource,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=part2_mct_view_count(source);
    if count==0 {Some((Ok(()),calls))}else if calls.len()==0 {None}else{
        match calls[0] {
            Part2Tier1StorageEvent::MctViewCapacity {source:actual,elements,succeeded}=>
                if actual!=source || elements!=count {None}else{
                    Some((if succeeded {Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
                },
            _=>None,
        }
    }
}
pub(crate) open spec fn part2_mct_view_result(source:Part2MctViewSource,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_view_run(source,calls),result)
}
pub(crate) proof fn part2_mct_view_observed(source:Part2MctViewSource,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_mct_view_count(source)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_mct_view_result(source,result),
{
    let count=part2_mct_view_count(source);
    let prefix=if count==0 {Seq::empty()}else{
        seq![Part2Tier1StorageEvent::MctViewCapacity {source,elements:count,succeeded:result.is_ok()}]
    };
    assert forall|tail:Seq<Part2Tier1StorageEvent>|
        part2_mct_view_run(source,prefix+tail)==Some((result,tail)) by {
        if count==0 {assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_mct_view_run(source,calls),prefix,result));
}
pub(crate) proof fn part2_mct_view_normal(source:Part2MctViewSource)
    ensures part2_mct_view_result(source,Ok(())),
{part2_mct_view_observed(source,Ok(()));}

pub(crate) open spec fn part2_mct_line_collection_run(before:Seq<Part2MctComponent>,collection:Part2MctCollection,work:u64,maximum_work:u64,maximum_bytes:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLineEffect> {
    if matches!(collection.3,crate::codestream::MctCollectionKind::Wavelet){part2_mct_line_wavelet_run(before,collection,work,maximum_work,maximum_bytes,calls)}
    else if matches!(collection.3,crate::codestream::MctCollectionKind::Decorrelation){
        part2_mct_decorrelation_storage_run(Part2MctRuntimeContext {components:before,collection,work,maximum_work,maximum_bytes},calls)
    }
    else{part2_mct_dependency_storage_run(
        Part2MctRuntimeContext {components:before,collection,work,maximum_work,maximum_bytes},calls)}
}
pub(crate) open spec fn part2_mct_line_collection_result(before:Seq<Part2MctComponent>,collection:Part2MctCollection,work:u64,maximum_work:u64,maximum_bytes:u64,result:Part2MctLineEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_line_collection_run(before,collection,work,maximum_work,maximum_bytes,calls),Ok(result))
}
pub(crate) open spec fn part2_mct_line_stage_next(before:Part2MctLineEffect,collections:Seq<Part2MctCollection>,maximum_work:u64,maximum_bytes:u64,index:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLineEffect> {
    if before.0.is_err(){Some((Ok(before),calls))}else if index>=collections.len(){Some((Ok((Err(part1_transform_error(false)),before.1,before.2)),calls))}
    else{part2_mct_line_collection_run(before.1,collections[index as int],before.2,maximum_work,maximum_bytes,calls)}
}
#[verifier::opaque]
pub(crate) open spec fn part2_mct_line_stage_run(before:Seq<Part2MctComponent>,collections:Seq<Part2MctCollection>,work:u64,maximum_work:u64,maximum_bytes:u64,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLineEffect>
    decreases count,
{
    if count==0{Some((Ok((Ok(()),before,work)),calls))}else{
        part2_tier1_storage_bind(part2_mct_line_stage_run(before,collections,work,maximum_work,maximum_bytes,(count-1) as nat,calls),
            |previous:Part2MctLineEffect,rest|part2_mct_line_stage_next(previous,collections,maximum_work,maximum_bytes,(count-1) as nat,rest))
    }
}
pub(crate) open spec fn part2_mct_line_stage_result(before:Seq<Part2MctComponent>,collections:Seq<Part2MctCollection>,work:u64,maximum_work:u64,maximum_bytes:u64,result:Part2MctLineEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_line_stage_run(before,collections,work,maximum_work,maximum_bytes,collections.len(),calls),Ok(result))
}
pub(crate) open spec fn part2_mct_line_transform_next(before:Part2MctLineEffect,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLineEffect> {
    if before.0.is_err(){Some((Ok(before),calls))}else if count>stages.len(){Some((Ok((Err(part1_transform_error(false)),before.1,before.2)),calls))}
    else{let stage=stages[stages.len()-count];part2_mct_line_stage_run(before.1,stage.1,before.2,maximum_work,maximum_bytes,stage.1.len(),calls)}
}
#[verifier::opaque]
pub(crate) open spec fn part2_mct_line_transform_run(before:Seq<Part2MctComponent>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLineEffect>
    decreases count,
{
    if count==0{Some((Ok((Ok(()),before,work)),calls))}else{
        part2_tier1_storage_bind(part2_mct_line_transform_run(before,stages,work,maximum_work,maximum_bytes,(count-1) as nat,calls),
            |previous:Part2MctLineEffect,rest|part2_mct_line_transform_next(previous,stages,maximum_work,maximum_bytes,count,rest))
    }
}
pub(crate) open spec fn part2_mct_line_transform_result(before:Seq<Part2MctComponent>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,result:Part2MctLineEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_line_transform_run(before,stages,work,maximum_work,maximum_bytes,stages.len(),calls),Ok(result))
}
pub(crate) proof fn part2_mct_line_collection_normal(before:Seq<Part2MctComponent>,collection:Part2MctCollection,work:u64,maximum_work:u64,maximum_bytes:u64)
    ensures part2_mct_line_collection_result(before,collection,work,maximum_work,maximum_bytes,part2_mct_collection(before,collection,work,maximum_work,maximum_bytes)),
{
    let result=part2_mct_collection(before,collection,work,maximum_work,maximum_bytes);
    if matches!(collection.3,crate::codestream::MctCollectionKind::Wavelet){
        part2_mct_line_wavelet_normal(before,collection,work,maximum_work,maximum_bytes);
        part2_tier1_storage_eta(|calls|part2_mct_line_wavelet_run(before,collection,work,maximum_work,maximum_bytes,calls),Ok(result));
    }else if matches!(collection.3,crate::codestream::MctCollectionKind::Decorrelation){
        let context=Part2MctRuntimeContext {components:before,collection,work,maximum_work,maximum_bytes};
        part2_mct_decorrelation_storage_normal(context);
        part2_tier1_storage_eta(|calls|part2_mct_decorrelation_storage_run(context,calls),Ok(result));
    }else{
        let context=Part2MctRuntimeContext {components:before,collection,work,maximum_work,maximum_bytes};
        part2_mct_dependency_storage_normal(context);
        part2_mct_dependency_storage_frames(context,result);
        part2_tier1_storage_eta(|calls|part2_mct_dependency_storage_run(context,calls),Ok(result));
    }
}
pub(crate) proof fn part2_mct_line_stage_normal(before:Seq<Part2MctComponent>,collections:Seq<Part2MctCollection>,work:u64,maximum_work:u64,maximum_bytes:u64,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_mct_line_stage_run(before,collections,work,maximum_work,maximum_bytes,count,calls),Ok(part2_mct_stage_prefix(before,collections,work,maximum_work,maximum_bytes,count))),
    decreases count,
{
    reveal(part2_mct_line_stage_run);reveal(part2_mct_stage_prefix);
    let result=part2_mct_stage_prefix(before,collections,work,maximum_work,maximum_bytes,count);
    if count==0{part2_tier1_storage_pure(Ok(result));}else{
        let previous=part2_mct_stage_prefix(before,collections,work,maximum_work,maximum_bytes,(count-1) as nat);
        part2_mct_line_stage_normal(before,collections,work,maximum_work,maximum_bytes,(count-1) as nat);
        if previous.0.is_err() || count-1>=collections.len(){part2_tier1_storage_pure(Ok(result));}else{
            part2_mct_line_collection_normal(previous.1,collections[count-1],previous.2,maximum_work,maximum_bytes);
            part2_tier1_storage_eta(|calls|part2_mct_line_collection_run(previous.1,collections[count-1],previous.2,maximum_work,maximum_bytes,calls),Ok(result));
        }
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_stage_run(before,collections,work,maximum_work,maximum_bytes,(count-1) as nat,calls),
            |previous:Part2MctLineEffect,rest|part2_mct_line_stage_next(previous,collections,maximum_work,maximum_bytes,(count-1) as nat,rest),Ok(previous),Ok(result));
    }
}
pub(crate) proof fn part2_mct_line_transform_normal(before:Seq<Part2MctComponent>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_mct_line_transform_run(before,stages,work,maximum_work,maximum_bytes,count,calls),Ok(part2_mct_transform_prefix(before,stages,work,maximum_work,maximum_bytes,count))),
    decreases count,
{
    reveal(part2_mct_line_transform_run);reveal(part2_mct_transform_prefix);
    let result=part2_mct_transform_prefix(before,stages,work,maximum_work,maximum_bytes,count);
    if count==0{part2_tier1_storage_pure(Ok(result));}else{
        let previous=part2_mct_transform_prefix(before,stages,work,maximum_work,maximum_bytes,(count-1) as nat);
        part2_mct_line_transform_normal(before,stages,work,maximum_work,maximum_bytes,(count-1) as nat);
        if previous.0.is_err() || count>stages.len(){part2_tier1_storage_pure(Ok(result));}else{
            let stage=stages[stages.len()-count];
            part2_mct_line_stage_normal(previous.1,stage.1,previous.2,maximum_work,maximum_bytes,stage.1.len());
            part2_tier1_storage_eta(|calls|part2_mct_line_stage_run(previous.1,stage.1,previous.2,maximum_work,maximum_bytes,stage.1.len(),calls),Ok(result));
        }
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_transform_run(before,stages,work,maximum_work,maximum_bytes,(count-1) as nat,calls),
            |previous:Part2MctLineEffect,rest|part2_mct_line_transform_next(previous,stages,maximum_work,maximum_bytes,count,rest),Ok(previous),Ok(result));
    }
}
pub(crate) proof fn part2_mct_line_stage_prefix_error(before:Seq<Part2MctComponent>,collections:Seq<Part2MctCollection>,work:u64,maximum_work:u64,maximum_bytes:u64,prefix:nat,count:nat,effect:Part2MctLineEffect)
    requires prefix<=count,effect.0.is_err(),part2_tier1_storage_framed(|calls|part2_mct_line_stage_run(before,collections,work,maximum_work,maximum_bytes,prefix,calls),Ok(effect)),
    ensures part2_tier1_storage_framed(|calls|part2_mct_line_stage_run(before,collections,work,maximum_work,maximum_bytes,count,calls),Ok(effect)),
    decreases count-prefix,
{
    if prefix<count{reveal(part2_mct_line_stage_run);
        part2_mct_line_stage_prefix_error(before,collections,work,maximum_work,maximum_bytes,prefix,(count-1) as nat,effect);part2_tier1_storage_pure(Ok(effect));
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_stage_run(before,collections,work,maximum_work,maximum_bytes,(count-1) as nat,calls),
            |previous:Part2MctLineEffect,rest|part2_mct_line_stage_next(previous,collections,maximum_work,maximum_bytes,(count-1) as nat,rest),Ok(effect),Ok(effect));
    }
}
pub(crate) proof fn part2_mct_line_stage_child_error(before:Seq<Part2MctComponent>,collections:Seq<Part2MctCollection>,work:u64,maximum_work:u64,maximum_bytes:u64,index:nat,current:Seq<Part2MctComponent>,current_work:u64,effect:Part2MctLineEffect)
    requires index<collections.len(),part2_mct_stage_prefix(before,collections,work,maximum_work,maximum_bytes,index)==(Ok(()),current,current_work),
        effect.0.is_err(),part2_mct_line_collection_result(current,collections[index as int],current_work,maximum_work,maximum_bytes,effect),
    ensures part2_mct_line_stage_result(before,collections,work,maximum_work,maximum_bytes,effect),
{
    reveal(part2_mct_line_stage_run);
    part2_mct_line_stage_normal(before,collections,work,maximum_work,maximum_bytes,index);
    part2_tier1_storage_eta(|calls|part2_mct_line_collection_run(current,collections[index as int],current_work,maximum_work,maximum_bytes,calls),Ok(effect));
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_stage_run(before,collections,work,maximum_work,maximum_bytes,index,calls),
        |previous:Part2MctLineEffect,rest|part2_mct_line_stage_next(previous,collections,maximum_work,maximum_bytes,index,rest),Ok((Ok(()),current,current_work)),Ok(effect));
    part2_mct_line_stage_prefix_error(before,collections,work,maximum_work,maximum_bytes,index+1,collections.len(),effect);
}
pub(crate) proof fn part2_mct_line_transform_prefix_error(before:Seq<Part2MctComponent>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,prefix:nat,count:nat,effect:Part2MctLineEffect)
    requires prefix<=count,effect.0.is_err(),part2_tier1_storage_framed(|calls|part2_mct_line_transform_run(before,stages,work,maximum_work,maximum_bytes,prefix,calls),Ok(effect)),
    ensures part2_tier1_storage_framed(|calls|part2_mct_line_transform_run(before,stages,work,maximum_work,maximum_bytes,count,calls),Ok(effect)),
    decreases count-prefix,
{
    if prefix<count{reveal(part2_mct_line_transform_run);
        part2_mct_line_transform_prefix_error(before,stages,work,maximum_work,maximum_bytes,prefix,(count-1) as nat,effect);part2_tier1_storage_pure(Ok(effect));
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_transform_run(before,stages,work,maximum_work,maximum_bytes,(count-1) as nat,calls),
            |previous:Part2MctLineEffect,rest|part2_mct_line_transform_next(previous,stages,maximum_work,maximum_bytes,count,rest),Ok(effect),Ok(effect));
    }
}
pub(crate) proof fn part2_mct_line_transform_child_error(before:Seq<Part2MctComponent>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,index:nat,current:Seq<Part2MctComponent>,current_work:u64,effect:Part2MctLineEffect)
    requires index<stages.len(),part2_mct_transform_prefix(before,stages,work,maximum_work,maximum_bytes,index)==(Ok(()),current,current_work),
        effect.0.is_err(),part2_mct_line_stage_result(current,stages[stages.len()-index-1].1,current_work,maximum_work,maximum_bytes,effect),
    ensures part2_mct_line_transform_result(before,stages,work,maximum_work,maximum_bytes,effect),
{
    reveal(part2_mct_line_transform_run);
    part2_mct_line_transform_normal(before,stages,work,maximum_work,maximum_bytes,index);
    let stage=stages[stages.len()-index-1];
    part2_tier1_storage_eta(|calls|part2_mct_line_stage_run(current,stage.1,current_work,maximum_work,maximum_bytes,stage.1.len(),calls),Ok(effect));
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_transform_run(before,stages,work,maximum_work,maximum_bytes,index,calls),
        |previous:Part2MctLineEffect,rest|part2_mct_line_transform_next(previous,stages,maximum_work,maximum_bytes,index+1,rest),Ok((Ok(()),current,current_work)),Ok(effect));
    part2_mct_line_transform_prefix_error(before,stages,work,maximum_work,maximum_bytes,index+1,stages.len(),effect);
}
pub(crate) proof fn part2_mct_line_collection_wavelet_observed(before:Seq<Part2MctComponent>,collection:Part2MctCollection,work:u64,maximum_work:u64,maximum_bytes:u64,result:Part2MctLineEffect)
    requires matches!(collection.3,crate::codestream::MctCollectionKind::Wavelet),part2_mct_line_wavelet_result(before,collection,work,maximum_work,maximum_bytes,result),
    ensures part2_mct_line_collection_result(before,collection,work,maximum_work,maximum_bytes,result),
{part2_tier1_storage_eta(|calls|part2_mct_line_wavelet_run(before,collection,work,maximum_work,maximum_bytes,calls),Ok(result));}
pub(crate) proof fn part2_mct_line_collection_decorrelation_observed(before:Seq<Part2MctComponent>,collection:Part2MctCollection,work:u64,maximum_work:u64,maximum_bytes:u64,result:Part2MctLineEffect)
    requires matches!(collection.3,crate::codestream::MctCollectionKind::Decorrelation),
        part2_mct_decorrelation_storage_result(Part2MctRuntimeContext {components:before,collection,work,maximum_work,maximum_bytes},result),
    ensures part2_mct_line_collection_result(before,collection,work,maximum_work,maximum_bytes,result),
{
    part2_tier1_storage_eta(|calls|part2_mct_decorrelation_storage_run(
        Part2MctRuntimeContext {components:before,collection,work,maximum_work,maximum_bytes},calls),Ok(result));
}
pub(crate) proof fn part2_mct_line_collection_dependency_observed(before:Seq<Part2MctComponent>,collection:Part2MctCollection,work:u64,maximum_work:u64,maximum_bytes:u64,result:Part2MctLineEffect)
    requires matches!(collection.3,crate::codestream::MctCollectionKind::Dependency),
        part2_mct_dependency_storage_result(Part2MctRuntimeContext {components:before,collection,work,maximum_work,maximum_bytes},result),
    ensures part2_mct_line_collection_result(before,collection,work,maximum_work,maximum_bytes,result),
{
    let context=Part2MctRuntimeContext {components:before,collection,work,maximum_work,maximum_bytes};
    part2_mct_dependency_storage_frames(context,result);
    part2_tier1_storage_eta(|calls|part2_mct_dependency_storage_run(context,calls),Ok(result));
}
pub(crate) open spec fn part2_mct_line_decoded_after_views(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Result<(),crate::DecodeError>,Part1DecodedImageModel)> {
    if before.4.len()>u16::MAX{Some((Ok((Err(part1_transform_error(true)),before)),calls))}
    else{part2_tier1_storage_bind(part2_mct_line_transform_run(part2_mct_decoded_inputs(before.4),stages,0,maximum_work,maximum_bytes,stages.len(),calls),
        |effect:Part2MctLineEffect,rest|Some((Ok((effect.0,part2_mct_decoded_result(before,effect.1))),rest)))}
}
pub(crate) open spec fn part2_mct_line_decoded_run(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Result<(),crate::DecodeError>,Part1DecodedImageModel)> {
    part2_tier1_storage_resume(part2_mct_view_run(Part2MctViewSource::Decoded {source:before},calls),
        |capacity:Result<(),crate::DecodeError>,rest|match capacity {
            Err(error)=>Some((Ok((Err(error),before)),rest)),
            Ok(())=>part2_mct_line_decoded_after_views(before,stages,maximum_work,maximum_bytes,rest),
        })
}
pub closed spec fn part2_mct_line_decoded_result(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64,result:(Result<(),crate::DecodeError>,Part1DecodedImageModel))->bool {
    part2_tier1_storage_framed(|calls|part2_mct_line_decoded_run(before,stages,maximum_work,maximum_bytes,calls),Ok(result))
}
pub(crate) proof fn part2_mct_line_decoded_after_views_normal(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64)
    ensures part2_tier1_storage_framed(|calls|part2_mct_line_decoded_after_views(before,stages,maximum_work,maximum_bytes,calls),
        Ok(part2_mct_decoded_image(before,stages,maximum_work,maximum_bytes))),
{
    let result=part2_mct_decoded_image(before,stages,maximum_work,maximum_bytes);
    part2_tier1_storage_pure(Ok(result));
    if before.4.len()<=u16::MAX{
        let input=part2_mct_decoded_inputs(before.4);
        part2_mct_line_transform_normal(input,stages,0,maximum_work,maximum_bytes,stages.len());
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_transform_run(input,stages,0,maximum_work,maximum_bytes,stages.len(),calls),
            |effect:Part2MctLineEffect,rest|Some((Ok((effect.0,part2_mct_decoded_result(before,effect.1))),rest)),
            Ok(part2_mct_transform(input,stages,0,maximum_work,maximum_bytes)),Ok(result));
    }
}
pub(crate) proof fn part2_mct_line_decoded_views_success(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64,
    result:(Result<(),crate::DecodeError>,Part1DecodedImageModel))
    requires part2_mct_view_result(Part2MctViewSource::Decoded {source:before},Ok(())),
        part2_tier1_storage_framed(|calls|part2_mct_line_decoded_after_views(before,stages,maximum_work,maximum_bytes,calls),Ok(result)),
    ensures part2_mct_line_decoded_result(before,stages,maximum_work,maximum_bytes,result),
{
    let source=Part2MctViewSource::Decoded {source:before};
    let next=|capacity:Result<(),crate::DecodeError>,rest|match capacity {
        Err(error)=>Some((Ok((Err(error),before)),rest)),
        Ok(())=>part2_mct_line_decoded_after_views(before,stages,maximum_work,maximum_bytes,rest),
    };
    part2_tier1_storage_eta(|calls|part2_mct_line_decoded_after_views(before,stages,maximum_work,maximum_bytes,calls),Ok(result));
    part2_tier1_resume_frame(|calls|part2_mct_view_run(source,calls),next,Ok(()),Ok(result));
}
pub(crate) proof fn part2_mct_line_decoded_normal(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64)
    ensures part2_mct_line_decoded_result(before,stages,maximum_work,maximum_bytes,part2_mct_decoded_image(before,stages,maximum_work,maximum_bytes)),
{
    part2_mct_view_normal(Part2MctViewSource::Decoded {source:before});
    part2_mct_line_decoded_after_views_normal(before,stages,maximum_work,maximum_bytes);
    part2_mct_line_decoded_views_success(before,stages,maximum_work,maximum_bytes,part2_mct_decoded_image(before,stages,maximum_work,maximum_bytes));
}
pub(crate) proof fn part2_mct_line_decoded_views_error(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64,error:crate::DecodeError)
    requires part2_mct_view_result(Part2MctViewSource::Decoded {source:before},Err(error)),
    ensures part2_mct_line_decoded_result(before,stages,maximum_work,maximum_bytes,(Err(error),before)),
{
    let source=Part2MctViewSource::Decoded {source:before};
    let next=|capacity:Result<(),crate::DecodeError>,rest|match capacity {
        Err(error)=>Some((Ok((Err(error),before)),rest)),
        Ok(())=>part2_mct_line_decoded_after_views(before,stages,maximum_work,maximum_bytes,rest),
    };
    part2_tier1_storage_pure(Ok((Err::<(),crate::DecodeError>(error),before)));
    part2_tier1_resume_frame(|calls|part2_mct_view_run(source,calls),next,Err(error),Ok((Err(error),before)));
}
pub(crate) proof fn part2_mct_line_decoded_observed(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64,effect:Part2MctLineEffect)
    requires before.4.len()<=u16::MAX,part2_mct_line_transform_result(part2_mct_decoded_inputs(before.4),stages,0,maximum_work,maximum_bytes,effect),
        part2_mct_view_result(Part2MctViewSource::Decoded {source:before},Ok(())),
    ensures part2_mct_line_decoded_result(before,stages,maximum_work,maximum_bytes,(effect.0,part2_mct_decoded_result(before,effect.1))),
{
    let input=part2_mct_decoded_inputs(before.4);
    part2_tier1_storage_pure(Ok((effect.0,part2_mct_decoded_result(before,effect.1))));
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_transform_run(input,stages,0,maximum_work,maximum_bytes,stages.len(),calls),
        |effect:Part2MctLineEffect,rest|Some((Ok((effect.0,part2_mct_decoded_result(before,effect.1))),rest)),Ok(effect),Ok((effect.0,part2_mct_decoded_result(before,effect.1))));
    part2_mct_line_decoded_views_success(before,stages,maximum_work,maximum_bytes,(effect.0,part2_mct_decoded_result(before,effect.1)));
}
pub(crate) open spec fn part2_mct_line_prepared_after_views(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionTileEffect> {
    let input=part2_mct_prepared_inputs(before,component_count,infos);
    match input.0{
        Err(error)=>Some((Ok((Err(error),before,work)),calls)),
        Ok(())=>part2_tier1_storage_bind(part2_mct_line_transform_run(input.1,stages,work,maximum_work,maximum_bytes,stages.len(),calls),
            |effect:Part2MctLineEffect,rest|Some((Ok((effect.0,part2_mct_prepared_result(before,effect.1),effect.2)),rest))),
    }
}
pub(crate) open spec fn part2_mct_line_prepared_run(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionTileEffect> {
    part2_tier1_storage_resume(part2_mct_view_run(Part2MctViewSource::Prepared {source:before},calls),
        |capacity:Result<(),crate::DecodeError>,rest|match capacity {
            Err(error)=>Some((Ok((Err(error),before,work)),rest)),
            Ok(())=>part2_mct_line_prepared_after_views(before,component_count,infos,stages,work,maximum_work,maximum_bytes,rest),
        })
}
pub(crate) open spec fn part2_mct_line_prepared_result(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,result:Part2ExtractionTileEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_line_prepared_run(before,component_count,infos,stages,work,maximum_work,maximum_bytes,calls),Ok(result))
}
pub(crate) proof fn part2_mct_line_prepared_after_views_normal(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64)
    ensures part2_tier1_storage_framed(|calls|part2_mct_line_prepared_after_views(before,component_count,infos,stages,work,maximum_work,maximum_bytes,calls),
        Ok(part2_mct_prepared_tiles(before,component_count,infos,stages,work,maximum_work,maximum_bytes))),
{
    let input=part2_mct_prepared_inputs(before,component_count,infos);
    let result=part2_mct_prepared_tiles(before,component_count,infos,stages,work,maximum_work,maximum_bytes);
    part2_tier1_storage_pure(Ok(result));
    if input.0.is_ok(){
        part2_mct_line_transform_normal(input.1,stages,work,maximum_work,maximum_bytes,stages.len());
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_transform_run(input.1,stages,work,maximum_work,maximum_bytes,stages.len(),calls),
            |effect:Part2MctLineEffect,rest|Some((Ok((effect.0,part2_mct_prepared_result(before,effect.1),effect.2)),rest)),
            Ok(part2_mct_transform(input.1,stages,work,maximum_work,maximum_bytes)),Ok(result));
    }
}
pub(crate) proof fn part2_mct_line_prepared_views_success(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,
    result:Part2ExtractionTileEffect)
    requires part2_mct_view_result(Part2MctViewSource::Prepared {source:before},Ok(())),
        part2_tier1_storage_framed(|calls|part2_mct_line_prepared_after_views(before,component_count,infos,stages,work,maximum_work,maximum_bytes,calls),Ok(result)),
    ensures part2_mct_line_prepared_result(before,component_count,infos,stages,work,maximum_work,maximum_bytes,result),
{
    let source=Part2MctViewSource::Prepared {source:before};
    let next=|capacity:Result<(),crate::DecodeError>,rest|match capacity {
        Err(error)=>Some((Ok((Err(error),before,work)),rest)),
        Ok(())=>part2_mct_line_prepared_after_views(before,component_count,infos,stages,work,maximum_work,maximum_bytes,rest),
    };
    part2_tier1_storage_eta(|calls|part2_mct_line_prepared_after_views(before,component_count,infos,stages,work,maximum_work,maximum_bytes,calls),Ok(result));
    part2_tier1_resume_frame(|calls|part2_mct_view_run(source,calls),next,Ok(()),Ok(result));
}
pub(crate) proof fn part2_mct_line_prepared_normal(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64)
    ensures part2_mct_line_prepared_result(before,component_count,infos,stages,work,maximum_work,maximum_bytes,part2_mct_prepared_tiles(before,component_count,infos,stages,work,maximum_work,maximum_bytes)),
{
    part2_mct_view_normal(Part2MctViewSource::Prepared {source:before});
    part2_mct_line_prepared_after_views_normal(before,component_count,infos,stages,work,maximum_work,maximum_bytes);
    part2_mct_line_prepared_views_success(before,component_count,infos,stages,work,maximum_work,maximum_bytes,
        part2_mct_prepared_tiles(before,component_count,infos,stages,work,maximum_work,maximum_bytes));
}
pub(crate) proof fn part2_mct_line_prepared_views_error(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,error:crate::DecodeError)
    requires part2_mct_view_result(Part2MctViewSource::Prepared {source:before},Err(error)),
    ensures part2_mct_line_prepared_result(before,component_count,infos,stages,work,maximum_work,maximum_bytes,(Err(error),before,work)),
{
    let source=Part2MctViewSource::Prepared {source:before};
    let next=|capacity:Result<(),crate::DecodeError>,rest|match capacity {
        Err(error)=>Some((Ok((Err(error),before,work)),rest)),
        Ok(())=>part2_mct_line_prepared_after_views(before,component_count,infos,stages,work,maximum_work,maximum_bytes,rest),
    };
    part2_tier1_storage_pure(Ok((Err::<(),crate::DecodeError>(error),before,work)));
    part2_tier1_resume_frame(|calls|part2_mct_view_run(source,calls),next,Err(error),Ok((Err(error),before,work)));
}
pub(crate) proof fn part2_mct_line_prepared_observed(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,effect:Part2MctLineEffect)
    requires part2_mct_prepared_inputs(before,component_count,infos).0.is_ok(),
        part2_mct_line_transform_result(part2_mct_prepared_inputs(before,component_count,infos).1,stages,work,maximum_work,maximum_bytes,effect),
        part2_mct_view_result(Part2MctViewSource::Prepared {source:before},Ok(())),
    ensures part2_mct_line_prepared_result(before,component_count,infos,stages,work,maximum_work,maximum_bytes,(effect.0,part2_mct_prepared_result(before,effect.1),effect.2)),
{
    let input=part2_mct_prepared_inputs(before,component_count,infos);
    part2_tier1_storage_pure(Ok((effect.0,part2_mct_prepared_result(before,effect.1),effect.2)));
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_transform_run(input.1,stages,work,maximum_work,maximum_bytes,stages.len(),calls),
        |effect:Part2MctLineEffect,rest|Some((Ok((effect.0,part2_mct_prepared_result(before,effect.1),effect.2)),rest)),Ok(effect),Ok((effect.0,part2_mct_prepared_result(before,effect.1),effect.2)));
    part2_mct_line_prepared_views_success(before,component_count,infos,stages,work,maximum_work,maximum_bytes,
        (effect.0,part2_mct_prepared_result(before,effect.1),effect.2));
}
pub(crate) open spec fn part2_mct_line_finish_after(effect:Part2ExtractionTileEffect,standard:(bool,bool))->Part2ExtractionTileEffect {
    match effect.0{Err(_)=>effect,Ok(())=>{
        let result=part1_prepared_standard_transform(effect.1,standard);(result.0,result.1,effect.2)
    }}
}
pub(crate) open spec fn part2_mct_line_finish_run(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum_bytes:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionTileEffect> {
    match mct{None=>Some((Ok(part2_mct_line_finish_after((Ok(()),before,work),standard)),calls)),
        Some(stages)=>part2_tier1_storage_bind(part2_mct_line_prepared_run(before,component_count,infos,stages,work,maximum_work,maximum_bytes,calls),
            |effect:Part2ExtractionTileEffect,rest|Some((Ok(part2_mct_line_finish_after(effect,standard)),rest))),
    }
}
pub(crate) open spec fn part2_mct_line_finish_result(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum_bytes:u64,result:Part2ExtractionTileEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_line_finish_run(before,component_count,infos,mct,standard,work,maximum_work,maximum_bytes,calls),Ok(result))
}
pub(crate) proof fn part2_mct_line_finish_normal(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum_bytes:u64)
    ensures part2_mct_line_finish_result(before,component_count,infos,mct,standard,work,maximum_work,maximum_bytes,part2_finish_prepared_tile(before,component_count,infos,mct,standard,work,maximum_work,maximum_bytes)),
{
    let result=part2_finish_prepared_tile(before,component_count,infos,mct,standard,work,maximum_work,maximum_bytes);
    part2_tier1_storage_pure(Ok(result));
    if let Some(stages)=mct{
        part2_mct_line_prepared_normal(before,component_count,infos,stages,work,maximum_work,maximum_bytes);
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_prepared_run(before,component_count,infos,stages,work,maximum_work,maximum_bytes,calls),
            |effect:Part2ExtractionTileEffect,rest|Some((Ok(part2_mct_line_finish_after(effect,standard)),rest)),
            Ok(part2_mct_prepared_tiles(before,component_count,infos,stages,work,maximum_work,maximum_bytes)),Ok(result));
    }
}
pub(crate) proof fn part2_mct_line_finish_observed(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,standard:(bool,bool),work:u64,maximum_work:u64,maximum_bytes:u64,effect:Part2ExtractionTileEffect)
    requires part2_mct_line_prepared_result(before,component_count,infos,stages,work,maximum_work,maximum_bytes,effect),
    ensures part2_mct_line_finish_result(before,component_count,infos,Some(stages),standard,work,maximum_work,maximum_bytes,part2_mct_line_finish_after(effect,standard)),
{
    part2_tier1_storage_pure(Ok(part2_mct_line_finish_after(effect,standard)));
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_prepared_run(before,component_count,infos,stages,work,maximum_work,maximum_bytes,calls),
        |effect:Part2ExtractionTileEffect,rest|Some((Ok(part2_mct_line_finish_after(effect,standard)),rest)),Ok(effect),Ok(part2_mct_line_finish_after(effect,standard)));
}
}
