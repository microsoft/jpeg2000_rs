//! Real ordered MCT collection/stage composition of spectral line responses.
use super::*;
verus! {
pub(crate) open spec fn part2_mct_line_collection_run(before:Seq<Part2MctComponent>,collection:Part2MctCollection,work:u64,maximum_work:u64,maximum_bytes:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLineEffect> {
    if matches!(collection.3,crate::codestream::MctCollectionKind::Wavelet){part2_mct_line_wavelet_run(before,collection,work,maximum_work,maximum_bytes,calls)}
    else{Some((Ok(part2_mct_collection(before,collection,work,maximum_work,maximum_bytes)),calls))}
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
    }else{part2_tier1_storage_pure(Ok(result));}
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
pub(crate) open spec fn part2_mct_line_decoded_run(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Result<(),crate::DecodeError>,Part1DecodedImageModel)> {
    if before.4.len()>u16::MAX{Some((Ok((Err(part1_transform_error(true)),before)),calls))}
    else{part2_tier1_storage_bind(part2_mct_line_transform_run(part2_mct_decoded_inputs(before.4),stages,0,maximum_work,maximum_bytes,stages.len(),calls),
        |effect:Part2MctLineEffect,rest|Some((Ok((effect.0,part2_mct_decoded_result(before,effect.1))),rest)))}
}
pub closed spec fn part2_mct_line_decoded_result(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64,result:(Result<(),crate::DecodeError>,Part1DecodedImageModel))->bool {
    part2_tier1_storage_framed(|calls|part2_mct_line_decoded_run(before,stages,maximum_work,maximum_bytes,calls),Ok(result))
}
pub(crate) proof fn part2_mct_line_decoded_normal(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64)
    ensures part2_mct_line_decoded_result(before,stages,maximum_work,maximum_bytes,part2_mct_decoded_image(before,stages,maximum_work,maximum_bytes)),
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
pub(crate) proof fn part2_mct_line_decoded_observed(before:Part1DecodedImageModel,stages:Seq<Part2MctStage>,maximum_work:u64,maximum_bytes:u64,effect:Part2MctLineEffect)
    requires before.4.len()<=u16::MAX,part2_mct_line_transform_result(part2_mct_decoded_inputs(before.4),stages,0,maximum_work,maximum_bytes,effect),
    ensures part2_mct_line_decoded_result(before,stages,maximum_work,maximum_bytes,(effect.0,part2_mct_decoded_result(before,effect.1))),
{
    let input=part2_mct_decoded_inputs(before.4);
    part2_tier1_storage_pure(Ok((effect.0,part2_mct_decoded_result(before,effect.1))));
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_transform_run(input,stages,0,maximum_work,maximum_bytes,stages.len(),calls),
        |effect:Part2MctLineEffect,rest|Some((Ok((effect.0,part2_mct_decoded_result(before,effect.1))),rest)),Ok(effect),Ok((effect.0,part2_mct_decoded_result(before,effect.1))));
}
pub(crate) open spec fn part2_mct_line_prepared_run(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionTileEffect> {
    let input=part2_mct_prepared_inputs(before,component_count,infos);
    match input.0{
        Err(error)=>Some((Ok((Err(error),before,work)),calls)),
        Ok(())=>part2_tier1_storage_bind(part2_mct_line_transform_run(input.1,stages,work,maximum_work,maximum_bytes,stages.len(),calls),
            |effect:Part2MctLineEffect,rest|Some((Ok((effect.0,part2_mct_prepared_result(before,effect.1),effect.2)),rest))),
    }
}
pub(crate) open spec fn part2_mct_line_prepared_result(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,result:Part2ExtractionTileEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_line_prepared_run(before,component_count,infos,stages,work,maximum_work,maximum_bytes,calls),Ok(result))
}
pub(crate) proof fn part2_mct_line_prepared_normal(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64)
    ensures part2_mct_line_prepared_result(before,component_count,infos,stages,work,maximum_work,maximum_bytes,part2_mct_prepared_tiles(before,component_count,infos,stages,work,maximum_work,maximum_bytes)),
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
pub(crate) proof fn part2_mct_line_prepared_observed(before:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,stages:Seq<Part2MctStage>,work:u64,maximum_work:u64,maximum_bytes:u64,effect:Part2MctLineEffect)
    requires part2_mct_prepared_inputs(before,component_count,infos).0.is_ok(),
        part2_mct_line_transform_result(part2_mct_prepared_inputs(before,component_count,infos).1,stages,work,maximum_work,maximum_bytes,effect),
    ensures part2_mct_line_prepared_result(before,component_count,infos,stages,work,maximum_work,maximum_bytes,(effect.0,part2_mct_prepared_result(before,effect.1),effect.2)),
{
    let input=part2_mct_prepared_inputs(before,component_count,infos);
    part2_tier1_storage_pure(Ok((effect.0,part2_mct_prepared_result(before,effect.1),effect.2)));
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_transform_run(input.1,stages,work,maximum_work,maximum_bytes,stages.len(),calls),
        |effect:Part2MctLineEffect,rest|Some((Ok((effect.0,part2_mct_prepared_result(before,effect.1),effect.2)),rest)),Ok(effect),Ok((effect.0,part2_mct_prepared_result(before,effect.1),effect.2)));
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
