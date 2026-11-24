//! Fresh raw LL and reconstructed-plane sample copies at their actual frontiers.
use super::*;
verus! {
pub enum Part2PrepareCopyRole {InitialLl,PreparedPlane}
#[verifier::opaque]
pub(crate) open spec fn part2_prepare_copy_capacity_run(role:Part2PrepareCopyRole,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::PrepareCopyCapacity {role:actual,elements,succeeded}=>
            if actual!=role || elements!=count{None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub enum Part2PrepareBandStage {Samples,Visited,Descriptor}
pub enum Part2PrepareWorkingContext {
    Owner {bands:Seq<crate::decode::SubbandGeometry>,selected:usize,fraction:u8,maximum:u64},
    Band {before:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,index:usize,fraction:u8,maximum:u64,stage:Part2PrepareBandStage},
}
pub(crate) open spec fn part2_prepare_working_count(context:Part2PrepareWorkingContext)->nat {
    match context {
        Part2PrepareWorkingContext::Owner {selected,..}=>selected as nat,
        Part2PrepareWorkingContext::Band {bands,index,stage,..}=>match stage {
            Part2PrepareBandStage::Descriptor=>1,
            _=>if index>=bands.len(){0}else{bands[index as int].width as nat*bands[index as int].height as nat},
        },
    }
}
pub(crate) open spec fn part2_prepare_working_capacity_run(context:Part2PrepareWorkingContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=part2_prepare_working_count(context);
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0] {
        Part2Tier1StorageEvent::PrepareWorkingCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=count {None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) open spec fn part2_prepare_working_capacity_result(context:Part2PrepareWorkingContext,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_prepare_working_capacity_run(context,calls),result)
}
pub(crate) proof fn part2_prepare_working_capacity_observed(context:Part2PrepareWorkingContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_prepare_working_count(context)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_prepare_working_capacity_result(context,result),
{
    let count=part2_prepare_working_count(context);
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::PrepareWorkingCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_prepare_working_capacity_run(context,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_prepare_working_capacity_run(context,calls),prefix,result));
}
pub(crate) open spec fn part2_prepare_band_rank(stage:Part2PrepareBandStage)->nat {
    match stage {Part2PrepareBandStage::Samples=>2,Part2PrepareBandStage::Visited=>1,Part2PrepareBandStage::Descriptor=>0}
}
pub(crate) open spec fn part2_prepare_band_stage_run(before:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,index:usize,fraction:u8,maximum:u64,
    stage:Part2PrepareBandStage,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareWorkingState>
    decreases part2_prepare_band_rank(stage),
{
    let ordinary=part1_prepare_append_band(before,bands,index,fraction,maximum);
    if ordinary.0.is_err(){Some((Ok(ordinary),calls))}else{
        part2_tier1_storage_resume(part2_prepare_working_capacity_run(
            Part2PrepareWorkingContext::Band {before,bands,index,fraction,maximum,stage},calls),
            |result:Result<(),crate::DecodeError>,rest|match result {
                Err(error)=>Some((Ok((Err(error),(before.0,ordinary.1.1))),rest)),
                Ok(())=>match stage {
                    Part2PrepareBandStage::Samples=>part2_prepare_band_stage_run(before,bands,index,fraction,maximum,Part2PrepareBandStage::Visited,rest),
                    Part2PrepareBandStage::Visited=>part2_prepare_band_stage_run(before,bands,index,fraction,maximum,Part2PrepareBandStage::Descriptor,rest),
                    Part2PrepareBandStage::Descriptor=>Some((Ok(ordinary),rest)),
                },
            })
    }
}
pub(crate) open spec fn part2_prepare_band_result(before:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,index:usize,fraction:u8,maximum:u64,result:Part1PrepareWorkingState)->bool {
    part2_tier1_storage_framed(|calls|part2_prepare_band_stage_run(before,bands,index,fraction,maximum,Part2PrepareBandStage::Samples,calls),Ok(result))
}
pub(crate) proof fn part2_prepare_band_stage_normal(before:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,index:usize,fraction:u8,maximum:u64,stage:Part2PrepareBandStage)
    ensures part2_tier1_storage_framed(|calls|part2_prepare_band_stage_run(before,bands,index,fraction,maximum,stage,calls),
        Ok(part1_prepare_append_band(before,bands,index,fraction,maximum))),
    decreases part2_prepare_band_rank(stage),
{
    let ordinary=part1_prepare_append_band(before,bands,index,fraction,maximum);
    if ordinary.0.is_err(){part2_tier1_storage_pure(Ok(ordinary));}else{
        let context=Part2PrepareWorkingContext::Band {before,bands,index,fraction,maximum,stage};
        part2_prepare_working_capacity_observed(context,Ok(()));
        match stage {
            Part2PrepareBandStage::Samples=>{part2_prepare_band_stage_normal(before,bands,index,fraction,maximum,Part2PrepareBandStage::Visited);
                part2_tier1_storage_eta(|calls|part2_prepare_band_stage_run(before,bands,index,fraction,maximum,Part2PrepareBandStage::Visited,calls),Ok(ordinary));},
            Part2PrepareBandStage::Visited=>{part2_prepare_band_stage_normal(before,bands,index,fraction,maximum,Part2PrepareBandStage::Descriptor);
                part2_tier1_storage_eta(|calls|part2_prepare_band_stage_run(before,bands,index,fraction,maximum,Part2PrepareBandStage::Descriptor,calls),Ok(ordinary));},
            Part2PrepareBandStage::Descriptor=>{part2_tier1_storage_pure(Ok(ordinary));},
        }
        part2_tier1_resume_frame(|calls|part2_prepare_working_capacity_run(context,calls),|result:Result<(),crate::DecodeError>,rest|match result {
            Err(error)=>Some((Ok((Err(error),(before.0,ordinary.1.1))),rest)),
            Ok(())=>match stage {
                Part2PrepareBandStage::Samples=>part2_prepare_band_stage_run(before,bands,index,fraction,maximum,Part2PrepareBandStage::Visited,rest),
                Part2PrepareBandStage::Visited=>part2_prepare_band_stage_run(before,bands,index,fraction,maximum,Part2PrepareBandStage::Descriptor,rest),
                Part2PrepareBandStage::Descriptor=>Some((Ok(ordinary),rest)),
            },
        },Ok(()),Ok(ordinary));
    }
}
pub(crate) proof fn part2_prepare_band_refused_at(before:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,index:usize,fraction:u8,maximum:u64,
    stage:Part2PrepareBandStage,refused:Part2PrepareBandStage)
    requires part1_prepare_append_band(before,bands,index,fraction,maximum).0==Ok(()),
        part2_prepare_band_rank(stage)>=part2_prepare_band_rank(refused),
        part2_prepare_working_capacity_result(Part2PrepareWorkingContext::Band {before,bands,index,fraction,maximum,stage:refused},Err(crate::DecodeError::AllocationFailed)),
    ensures part2_tier1_storage_framed(|calls|part2_prepare_band_stage_run(before,bands,index,fraction,maximum,stage,calls),
        Ok((Err(crate::DecodeError::AllocationFailed),(before.0,part1_prepare_append_band(before,bands,index,fraction,maximum).1.1)))),
    decreases part2_prepare_band_rank(stage),
{
    let ordinary=part1_prepare_append_band(before,bands,index,fraction,maximum);
    let effect=(Err(crate::DecodeError::AllocationFailed),(before.0,ordinary.1.1));
    let context=Part2PrepareWorkingContext::Band {before,bands,index,fraction,maximum,stage};
    let response=if stage==refused{Err(crate::DecodeError::AllocationFailed)}else{Ok(())};
    if stage==refused{part2_tier1_storage_pure(Ok(effect));}else{
        part2_prepare_working_capacity_observed(context,Ok(()));
        let next=if stage==Part2PrepareBandStage::Samples{Part2PrepareBandStage::Visited}else{Part2PrepareBandStage::Descriptor};
        part2_prepare_band_refused_at(before,bands,index,fraction,maximum,next,refused);
        part2_tier1_storage_eta(|calls|part2_prepare_band_stage_run(before,bands,index,fraction,maximum,next,calls),Ok(effect));
    }
    part2_tier1_resume_frame(|calls|part2_prepare_working_capacity_run(context,calls),|result:Result<(),crate::DecodeError>,rest|match result {
        Err(error)=>Some((Ok((Err(error),(before.0,ordinary.1.1))),rest)),
        Ok(())=>match stage {
            Part2PrepareBandStage::Samples=>part2_prepare_band_stage_run(before,bands,index,fraction,maximum,Part2PrepareBandStage::Visited,rest),
            Part2PrepareBandStage::Visited=>part2_prepare_band_stage_run(before,bands,index,fraction,maximum,Part2PrepareBandStage::Descriptor,rest),
            Part2PrepareBandStage::Descriptor=>Some((Ok(ordinary),rest)),
        },
    },response,Ok(effect));
}
#[verifier::opaque]
pub(crate) open spec fn part2_prepare_init_prefix_run(bands:Seq<crate::decode::SubbandGeometry>,fraction:u8,maximum:u64,count:nat,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareWorking>
    decreases count,
{
    if count==0{Some((Ok((Seq::empty(),0)),calls))}else{
        part2_tier1_storage_bind(part2_prepare_init_prefix_run(bands,fraction,maximum,(count-1) as nat,calls),
            |before:Part1PrepareWorking,rest|part2_tier1_storage_bind(
                part2_prepare_band_stage_run(before,bands,(count-1) as usize,fraction,maximum,Part2PrepareBandStage::Samples,rest),
                |effect:Part1PrepareWorkingState,tail|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(effect.1)},tail))))
    }
}
pub(crate) open spec fn part2_prepare_init_run(bands:Seq<crate::decode::SubbandGeometry>,selected:usize,fraction:u8,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareWorking> {
    part2_tier1_storage_bind(part2_prepare_working_capacity_run(Part2PrepareWorkingContext::Owner {bands,selected,fraction,maximum},calls),
        |_:(),rest|part2_prepare_init_prefix_run(bands,fraction,maximum,selected as nat,rest))
}
pub(crate) open spec fn part2_prepare_init_result(bands:Seq<crate::decode::SubbandGeometry>,selected:usize,fraction:u8,maximum:u64,result:Result<Part1PrepareWorking,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_prepare_init_run(bands,selected,fraction,maximum,calls),result)
}
pub(crate) proof fn part2_prepare_init_prefix_normal(bands:Seq<crate::decode::SubbandGeometry>,fraction:u8,maximum:u64,count:nat)
    requires count<=usize::MAX,
    ensures part2_tier1_storage_framed(|calls|part2_prepare_init_prefix_run(bands,fraction,maximum,count,calls),part1_prepare_init_prefix(bands,fraction,maximum,count)),
    decreases count,
{
    reveal_with_fuel(part2_prepare_init_prefix_run,1);reveal_with_fuel(part1_prepare_init_prefix,1);
    let result=part1_prepare_init_prefix(bands,fraction,maximum,count);
    if count==0{part2_tier1_storage_pure(result);}else{
        let prior=part1_prepare_init_prefix(bands,fraction,maximum,(count-1) as nat);
        part2_prepare_init_prefix_normal(bands,fraction,maximum,(count-1) as nat);
        part2_tier1_storage_eta(|calls|part2_prepare_init_prefix_run(bands,fraction,maximum,(count-1) as nat,calls),prior);
        if let Ok(before)=prior {
            let effect=part1_prepare_append_band(before,bands,(count-1) as usize,fraction,maximum);
            part2_prepare_band_stage_normal(before,bands,(count-1) as usize,fraction,maximum,Part2PrepareBandStage::Samples);
            assert(result==match effect.0{Err(error)=>Err(error),Ok(())=>Ok(effect.1)});
            part2_tier1_storage_pure(result);
            part2_tier1_storage_bind_frame(
                |calls|part2_prepare_band_stage_run(before,bands,(count-1) as usize,fraction,maximum,Part2PrepareBandStage::Samples,calls),
                |effect:Part1PrepareWorkingState,tail|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(effect.1)},tail)),Ok(effect),result);
        }
        part2_tier1_storage_bind_frame(|calls|part2_prepare_init_prefix_run(bands,fraction,maximum,(count-1) as nat,calls),
            |before:Part1PrepareWorking,rest|part2_tier1_storage_bind(
                part2_prepare_band_stage_run(before,bands,(count-1) as usize,fraction,maximum,Part2PrepareBandStage::Samples,rest),
                |effect:Part1PrepareWorkingState,tail|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(effect.1)},tail))),prior,result);
    }
}
pub(crate) proof fn part2_prepare_init_normal(bands:Seq<crate::decode::SubbandGeometry>,selected:usize,fraction:u8,maximum:u64)
    ensures part2_prepare_init_result(bands,selected,fraction,maximum,part1_prepare_init_prefix(bands,fraction,maximum,selected as nat)),
{
    let context=Part2PrepareWorkingContext::Owner {bands,selected,fraction,maximum};
    let result=part1_prepare_init_prefix(bands,fraction,maximum,selected as nat);
    part2_prepare_working_capacity_observed(context,Ok(()));
    part2_prepare_init_prefix_normal(bands,fraction,maximum,selected as nat);
    part2_tier1_storage_eta(|calls|part2_prepare_init_prefix_run(bands,fraction,maximum,selected as nat,calls),result);
    part2_tier1_storage_bind_frame(|calls|part2_prepare_working_capacity_run(context,calls),
        |_:(),rest|part2_prepare_init_prefix_run(bands,fraction,maximum,selected as nat,rest),Ok(()),result);
}
pub(crate) proof fn part2_prepare_init_owner_refused(bands:Seq<crate::decode::SubbandGeometry>,selected:usize,fraction:u8,maximum:u64)
    requires part2_prepare_working_capacity_result(Part2PrepareWorkingContext::Owner {bands,selected,fraction,maximum},Err(crate::DecodeError::AllocationFailed)),
    ensures part2_prepare_init_result(bands,selected,fraction,maximum,Err(crate::DecodeError::AllocationFailed)),
{
    part2_tier1_storage_bind_frame(
        |calls|part2_prepare_working_capacity_run(Part2PrepareWorkingContext::Owner {bands,selected,fraction,maximum},calls),
        |_:(),rest|part2_prepare_init_prefix_run(bands,fraction,maximum,selected as nat,rest),
        Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_prepare_init_prefix_error(bands:Seq<crate::decode::SubbandGeometry>,fraction:u8,maximum:u64,from:nat,to:nat,error:crate::DecodeError)
    requires from<=to<=usize::MAX,
        part2_tier1_storage_framed(|calls|part2_prepare_init_prefix_run(bands,fraction,maximum,from,calls),Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_prepare_init_prefix_run(bands,fraction,maximum,to,calls),Err(error)),
    decreases to-from,
{
    if from<to {
        reveal_with_fuel(part2_prepare_init_prefix_run,1);
        part2_prepare_init_prefix_error(bands,fraction,maximum,from,(to-1) as nat,error);
        part2_tier1_storage_bind_frame(|calls|part2_prepare_init_prefix_run(bands,fraction,maximum,(to-1) as nat,calls),
            |before:Part1PrepareWorking,rest|part2_tier1_storage_bind(
                part2_prepare_band_stage_run(before,bands,(to-1) as usize,fraction,maximum,Part2PrepareBandStage::Samples,rest),
                |effect:Part1PrepareWorkingState,tail|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(effect.1)},tail))),
            Err(error),Err(error));
    }
}
pub(crate) proof fn part2_prepare_init_band_error(bands:Seq<crate::decode::SubbandGeometry>,selected:usize,fraction:u8,maximum:u64,index:usize,
    before:Part1PrepareWorking,effect:Part1PrepareWorkingState)
    requires index<selected,part1_prepare_init_prefix(bands,fraction,maximum,index as nat)==Ok(before),
        part2_prepare_band_result(before,bands,index,fraction,maximum,effect),effect.0.is_err(),
    ensures part2_prepare_init_result(bands,selected,fraction,maximum,Err(effect.0.get_Err_0())),
{
    reveal_with_fuel(part2_prepare_init_prefix_run,1);
    let error=effect.0.get_Err_0();
    part2_prepare_init_prefix_normal(bands,fraction,maximum,index as nat);
    part2_tier1_storage_pure(Err::<Part1PrepareWorking,crate::DecodeError>(error));
    part2_tier1_storage_bind_frame(|calls|part2_prepare_band_stage_run(before,bands,index,fraction,maximum,Part2PrepareBandStage::Samples,calls),
        |effect:Part1PrepareWorkingState,tail|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(effect.1)},tail)),Ok(effect),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_prepare_init_prefix_run(bands,fraction,maximum,index as nat,calls),
        |before:Part1PrepareWorking,rest|part2_tier1_storage_bind(
            part2_prepare_band_stage_run(before,bands,index,fraction,maximum,Part2PrepareBandStage::Samples,rest),
            |effect:Part1PrepareWorkingState,tail|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(effect.1)},tail))),Ok(before),Err(error));
    assert(part2_tier1_storage_framed(|calls|part2_prepare_init_prefix_run(bands,fraction,maximum,index as nat+1,calls),Err(error)));
    part2_prepare_init_prefix_error(bands,fraction,maximum,index as nat+1,selected as nat,error);
    part2_tier1_storage_eta(|calls|part2_prepare_init_prefix_run(bands,fraction,maximum,selected as nat,calls),Err(error));
    let context=Part2PrepareWorkingContext::Owner {bands,selected,fraction,maximum};
    part2_prepare_working_capacity_observed(context,Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_prepare_working_capacity_run(context,calls),
        |_:(),rest|part2_prepare_init_prefix_run(bands,fraction,maximum,selected as nat,rest),Ok(()),Err(error));
}
pub(crate) open spec fn part2_prepared_views_run(source:Seq<Part1AssemblyTile>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<Part1AssemblyTile>> {
    if source.len()==0{Some((Ok(source),calls))}else if calls.len()==0{None}else{match calls[0] {
        Part2Tier1StorageEvent::PreparedViewsCapacity {source:actual,elements,succeeded}=>
            if actual!=source || elements!=source.len(){None}else{Some((if succeeded{Ok(source)}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) open spec fn part2_prepared_views_result(source:Seq<Part1AssemblyTile>,result:Result<Seq<Part1AssemblyTile>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_prepared_views_run(source,calls),result)
}
pub(crate) proof fn part2_prepared_views_observed(source:Seq<Part1AssemblyTile>,response:Result<(),crate::DecodeError>)
    requires response==Ok(()) || (source.len()>0 && response==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_prepared_views_result(source,match response{Err(error)=>Err(error),Ok(())=>Ok(source)}),
{
    let result=match response{Err(error)=>Err(error),Ok(())=>Ok(source)};
    let prefix=if source.len()==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::PreparedViewsCapacity {source,elements:source.len(),succeeded:response.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_prepared_views_run(source,prefix+tail)==Some((result,tail)) by{
        if source.len()==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_prepared_views_run(source,calls),prefix,result));
}
pub(crate) open spec fn part2_prepared_view_calls_run(source:Seq<Part1AssemblyTile>,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part1AssemblyTile>> {
    if source.len()==0{Some((Ok(source),events))}else if events.len()==0{None}else{match events[0] {
        Part2JpipSnapshotEvent::PreparedViewCalls {source:actual,calls}=>if actual!=source{None}else{
            match part2_prepared_views_run(source,calls){Some((result,rest))=>if rest.len()==0{Some((result,events.drop_first()))}else{None},None=>None}
        },
        _=>None,
    }}
}
pub(crate) proof fn part2_prepared_view_calls_observed(source:Seq<Part1AssemblyTile>,result:Result<Seq<Part1AssemblyTile>,crate::DecodeError>)
    requires part2_prepared_views_result(source,result),
    ensures part2_cold_framed(|events|part2_prepared_view_calls_run(source,events),result),
{
    let run=|calls|part2_prepared_views_run(source,calls);
    let calls=choose|prefix| #[trigger] part2_tier1_storage_prefix(run,prefix,result);
    assert(calls+Seq::empty() =~= calls);
    assert(run(calls)==Some((result,Seq::empty())));
    let prefix=if source.len()==0{Seq::empty()}else{seq![Part2JpipSnapshotEvent::PreparedViewCalls {source,calls}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_prepared_view_calls_run(source,prefix+tail)==Some((result,tail)) by{
        if source.len()==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_prepared_view_calls_run(source,events),prefix,result));
    part2_decode_eta(|events|part2_prepared_view_calls_run(source,events),result);
}
pub(crate) open spec fn part2_assemble_prepared_storage_run(size:Part1AssemblySize,source:Seq<Part1AssemblyTile>,selection:Option<([u32;4],u8)>,maximum:u64,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedImageModel> {
    part2_jpip_snapshot_bind(part2_prepared_view_calls_run(source,events),
        |views:Seq<Part1AssemblyTile>,rest|part2_assembly_calls_run(Part2AssemblyOwnerContext {size,tiles:views,selection,maximum},rest))
}
pub(crate) open spec fn part2_assemble_prepared_storage_result(size:Part1AssemblySize,source:Seq<Part1AssemblyTile>,selection:Option<([u32;4],u8)>,maximum:u64,
    result:Result<Part1DecodedImageModel,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_assemble_prepared_storage_run(size,source,selection,maximum,events),result)
}
pub(crate) open spec fn part2_owned_prepared_selected_run(
    size:Part1AssemblySize,source:Seq<Part1AssemblyTile>,region:[u32;4],discard:u8,maximum:u64,single_tile:bool,
    events:Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedImageModel> {
    if part2_owned_assembly_eligible(size,source,region,discard,maximum,single_tile) {
        part2_owned_assembly_storage_run(size,source,region,maximum,events)
    } else {
        part2_assemble_prepared_storage_run(size,source,Some((region,discard)),maximum,events)
    }
}
pub(crate) open spec fn part2_owned_prepared_selected_result(
    size:Part1AssemblySize,source:Seq<Part1AssemblyTile>,region:[u32;4],discard:u8,maximum:u64,single_tile:bool,
    result:Result<Part1DecodedImageModel,crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events|part2_owned_prepared_selected_run(size,source,region,discard,maximum,single_tile,events),result)
}
pub(crate) proof fn part2_owned_prepared_selected_observed(
    size:Part1AssemblySize,source:Seq<Part1AssemblyTile>,region:[u32;4],discard:u8,maximum:u64,single_tile:bool,
    result:Result<Part1DecodedImageModel,crate::DecodeError>,
)
    requires if part2_owned_assembly_eligible(size,source,region,discard,maximum,single_tile) {
        part2_owned_assembly_storage_result(size,source,region,maximum,result)
    } else {
        part2_assemble_prepared_storage_result(size,source,Some((region,discard)),maximum,result)
    },
    ensures part2_owned_prepared_selected_result(size,source,region,discard,maximum,single_tile,result),
{
    if part2_owned_assembly_eligible(size,source,region,discard,maximum,single_tile) {
        part2_decode_eta(|events|part2_owned_assembly_storage_run(size,source,region,maximum,events),result);
    } else {
        part2_decode_eta(|events|part2_assemble_prepared_storage_run(size,source,Some((region,discard)),maximum,events),result);
    }
}
pub(crate) proof fn part2_owned_prepared_selected_normal(
    size:Part1AssemblySize,source:Seq<Part1AssemblyTile>,region:[u32;4],discard:u8,maximum:u64,single_tile:bool,
)
    ensures part2_owned_prepared_selected_result(size,source,region,discard,maximum,single_tile,
        part2_assemble_prepared(size,source,Some((region,discard)),maximum)),
{
    if part2_owned_assembly_eligible(size,source,region,discard,maximum,single_tile) {
        part2_owned_assembly_value(size,source,region,maximum);
        part2_owned_assembly_capacity_observed(size,source,region,maximum,Ok(()));
    } else {
        part2_assemble_prepared_storage_normal(size,source,Some((region,discard)),maximum);
    }
    part2_owned_prepared_selected_observed(size,source,region,discard,maximum,single_tile,
        part2_assemble_prepared(size,source,Some((region,discard)),maximum));
}
pub(crate) proof fn part2_assemble_prepared_storage_normal(size:Part1AssemblySize,source:Seq<Part1AssemblyTile>,selection:Option<([u32;4],u8)>,maximum:u64)
    ensures part2_assemble_prepared_storage_result(size,source,selection,maximum,part2_assemble_prepared(size,source,selection,maximum)),
{
    let result=part2_assemble_prepared(size,source,selection,maximum);
    part2_prepared_views_observed(source,Ok(()));
    part2_prepared_view_calls_observed(source,Ok(source));
    let context=Part2AssemblyOwnerContext {size,tiles:source,selection,maximum};
    part2_assembly_storage_normal(context);part2_assembly_calls_observed(context,result);
    part2_decode_eta(|events|part2_assembly_calls_run(context,events),result);
    part2_cold_bind(|events|part2_prepared_view_calls_run(source,events),
        |views:Seq<Part1AssemblyTile>,rest|part2_assembly_calls_run(Part2AssemblyOwnerContext {size,tiles:views,selection,maximum},rest),Ok(source),result);
}
pub(crate) proof fn part2_assemble_prepared_views_refused(size:Part1AssemblySize,source:Seq<Part1AssemblyTile>,selection:Option<([u32;4],u8)>,maximum:u64,error:crate::DecodeError)
    requires part2_prepared_views_result(source,Err(error)),
    ensures part2_assemble_prepared_storage_result(size,source,selection,maximum,Err(error)),
{
    part2_prepared_view_calls_observed(source,Err(error));
    part2_cold_bind(|events|part2_prepared_view_calls_run(source,events),
        |views:Seq<Part1AssemblyTile>,rest|part2_assembly_calls_run(Part2AssemblyOwnerContext {size,tiles:views,selection,maximum},rest),Err(error),Err(error));
}
pub(crate) proof fn part2_assemble_prepared_output_observed(size:Part1AssemblySize,source:Seq<Part1AssemblyTile>,selection:Option<([u32;4],u8)>,maximum:u64,
    result:Result<Part1DecodedImageModel,crate::DecodeError>)
    requires part2_assembly_storage_result(Part2AssemblyOwnerContext {size,tiles:source,selection,maximum},result),
    ensures part2_assemble_prepared_storage_result(size,source,selection,maximum,result),
{
    let context=Part2AssemblyOwnerContext {size,tiles:source,selection,maximum};
    part2_prepared_views_observed(source,Ok(()));
    part2_prepared_view_calls_observed(source,Ok(source));
    part2_assembly_calls_observed(context,result);
    part2_decode_eta(|events|part2_assembly_calls_run(context,events),result);
    part2_cold_bind(|events|part2_prepared_view_calls_run(source,events),
        |views:Seq<Part1AssemblyTile>,rest|part2_assembly_calls_run(Part2AssemblyOwnerContext {size,tiles:views,selection,maximum},rest),Ok(source),result);
}
pub(crate) open spec fn part2_prepare_samples_run(role:Part2PrepareCopyRole,source:Seq<i64>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_prepare_copy_capacity_run(role,source.len(),calls),|_:(),rest|Some((Ok(source),rest)))
}
pub(crate) open spec fn part2_prepare_samples_result(role:Part2PrepareCopyRole,source:Seq<i64>,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_prepare_samples_run(role,source,calls),result)
}
pub(crate) proof fn part2_prepare_samples_observed(role:Part2PrepareCopyRole,source:Seq<i64>,result:Result<Seq<i64>,crate::DecodeError>)
    requires match result{Ok(values)=>values==source,Err(error)=>source.len()>0 && error==crate::DecodeError::AllocationFailed},
    ensures part2_prepare_samples_result(role,source,result),
{
    reveal(part2_prepare_copy_capacity_run);
    let prefix=if source.len()==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::PrepareCopyCapacity {role,elements:source.len(),succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_prepare_samples_run(role,source,prefix+tail)==Some((result,tail)) by{
        if source.len()==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_prepare_samples_run(role,source,calls),prefix,result));
}
pub(crate) open spec fn part2_prepare_initial_run(ll:Part1WorkingSubbandModel,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareFold> {
    part2_tier1_storage_bind(part2_prepare_samples_run(Part2PrepareCopyRole::InitialLl,ll.3,calls),
        |values:Seq<i64>,rest|Some((Ok((ll.0,ll.1,values,1usize)),rest)))
}
pub(crate) open spec fn part2_prepare_initial_result(ll:Part1WorkingSubbandModel,result:Result<Part1PrepareFold,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_prepare_initial_run(ll,calls),result)
}
pub(crate) proof fn part2_prepare_initial_observed(ll:Part1WorkingSubbandModel,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_prepare_samples_result(Part2PrepareCopyRole::InitialLl,ll.3,result),
    ensures part2_prepare_initial_result(ll,match result{Err(error)=>Err(error),Ok(values)=>Ok((ll.0,ll.1,values,1usize))}),
{
    let after=match result{Err(error)=>Err(error),Ok(values)=>Ok((ll.0,ll.1,values,1usize))};
    if result.is_ok(){part2_tier1_storage_pure(after);}
    part2_tier1_storage_bind_frame(|calls|part2_prepare_samples_run(Part2PrepareCopyRole::InitialLl,ll.3,calls),
        |values:Seq<i64>,rest|Some((Ok((ll.0,ll.1,values,1usize)),rest)),result,after);
}
pub(crate) proof fn part2_prepare_initial_normal(ll:Part1WorkingSubbandModel)
    ensures part2_prepare_initial_result(ll,Ok((ll.0,ll.1,ll.3,1usize))),
{
    part2_prepare_samples_observed(Part2PrepareCopyRole::InitialLl,ll.3,Ok(ll.3));
    part2_prepare_initial_observed(ll,Ok(ll.3));
}
pub(crate) open spec fn part2_prepare_plane_copy_run(plane:Part1ReconstructedPlane,first_detail:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareFold> {
    part2_tier1_storage_bind(part2_prepare_samples_run(Part2PrepareCopyRole::PreparedPlane,plane.3,calls),
        |values:Seq<i64>,rest|Some((Ok((plane.0,plane.1,values,first_detail)),rest)))
}
pub(crate) open spec fn part2_prepare_plane_copy_result(plane:Part1ReconstructedPlane,first_detail:usize,result:Result<Part1PrepareFold,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_prepare_plane_copy_run(plane,first_detail,calls),result)
}
pub(crate) proof fn part2_prepare_plane_copy_observed(plane:Part1ReconstructedPlane,first_detail:usize,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_prepare_samples_result(Part2PrepareCopyRole::PreparedPlane,plane.3,result),
    ensures part2_prepare_plane_copy_result(plane,first_detail,match result{Err(error)=>Err(error),Ok(values)=>Ok((plane.0,plane.1,values,first_detail))}),
{
    let after=match result{Err(error)=>Err(error),Ok(values)=>Ok((plane.0,plane.1,values,first_detail))};
    if result.is_ok(){part2_tier1_storage_pure(after);}
    part2_tier1_storage_bind_frame(|calls|part2_prepare_samples_run(Part2PrepareCopyRole::PreparedPlane,plane.3,calls),
        |values:Seq<i64>,rest|Some((Ok((plane.0,plane.1,values,first_detail)),rest)),result,after);
}
pub(crate) proof fn part2_prepare_plane_copy_normal(plane:Part1ReconstructedPlane,first_detail:usize)
    ensures part2_prepare_plane_copy_result(plane,first_detail,part1_prepare_copy_plane(plane,first_detail)),
{
    part2_prepare_samples_observed(Part2PrepareCopyRole::PreparedPlane,plane.3,Ok(plane.3));
    part2_prepare_plane_copy_observed(plane,first_detail,Ok(plane.3));
}
}
