//! Actual ordered component extraction calls and tile finishing frames.
use super::*;
verus! {
pub type Part2ExtractionComponentsEffect=(Result<(),crate::DecodeError>,Seq<Part1AssemblyTile>);
pub type Part2ExtractionTileEffect=(Result<(),crate::DecodeError>,Seq<Part1AssemblyTile>,u64);
pub struct Part2CoefficientReconstructionContext {pub prior:nat,pub components:nat,pub precincts:nat,pub work:u64,pub maximum:u64}
pub struct Part2PreparedComponentContext {
    pub before:Seq<Part1AssemblyTile>,pub plans:Seq<Part1PreparePlan>,pub precincts:Seq<Seq<Tier1RawPlane>>,
    pub styles:crate::codestream::ComponentCodingStyles,pub kernels:Seq<(u8,Part2RawKernel)>,pub maximum:u64,
    pub index:nat,pub value:Part1AssemblyTile,
}
pub(crate) open spec fn part2_prepared_component_capacity_run(context:Part2PreparedComponentContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    if calls.len()==0{None}else{match calls[0] {
        Part2Tier1StorageEvent::PreparedComponentCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=1 {None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) open spec fn part2_prepared_component_capacity_result(context:Part2PreparedComponentContext,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_prepared_component_capacity_run(context,calls),result)
}
pub(crate) proof fn part2_prepared_component_capacity_observed(context:Part2PreparedComponentContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || result==Err(crate::DecodeError::AllocationFailed),
    ensures part2_prepared_component_capacity_result(context,result),
{
    let prefix=seq![Part2Tier1StorageEvent::PreparedComponentCapacity {context,elements:1,succeeded:result.is_ok()}];
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_prepared_component_capacity_run(context,prefix+tail)==Some((result,tail)) by{
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_tier1_storage_prefix(|calls|part2_prepared_component_capacity_run(context,calls),prefix,result));
}
pub(crate) open spec fn part2_extraction_components_after_child(before:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,maximum:u64,index:nat,result:Result<Part1AssemblyTile,crate::DecodeError>,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionComponentsEffect> {
    match result {
        Err(error)=>Some((Ok((Err(error),before)),calls)),
        Ok(value)=>part2_tier1_storage_resume(part2_prepared_component_capacity_run(
            Part2PreparedComponentContext {before,plans,precincts,styles,kernels,maximum,index,value},calls),
            |reply:Result<(),crate::DecodeError>,rest|Some((Ok(match reply{Err(error)=>(Err(error),before),Ok(())=>(Ok(()),before.push(value))}),rest))),
    }
}
pub(crate) proof fn part2_extraction_components_after_child_normal(before:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,maximum:u64,index:nat,result:Result<Part1AssemblyTile,crate::DecodeError>)
    ensures part2_tier1_storage_framed(|calls|part2_extraction_components_after_child(before,plans,precincts,styles,kernels,maximum,index,result,calls),
        Ok(match result{Err(error)=>(Err(error),before),Ok(value)=>(Ok(()),before.push(value))})),
{
    let effect=match result{Err(error)=>(Err(error),before),Ok(value)=>(Ok(()),before.push(value))};
    part2_tier1_storage_pure(Ok(effect));
    if let Ok(value)=result {
        let context=Part2PreparedComponentContext {before,plans,precincts,styles,kernels,maximum,index,value};
        part2_prepared_component_capacity_observed(context,Ok(()));
        part2_tier1_resume_frame(|calls|part2_prepared_component_capacity_run(context,calls),
            |reply:Result<(),crate::DecodeError>,rest|Some((Ok(match reply{Err(error)=>(Err(error),before),Ok(())=>(Ok(()),before.push(value))}),rest)),
            Ok(()),Ok(effect));
    }
}
pub(crate) open spec fn part2_extraction_reconstruct_component_run(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1AssemblyTile> {
    match crate::codestream::component_coding_style_result(&styles,plan.component){
        Err(error)=>Some((Err(error),calls)),Ok(style)=>{
            let kernel=match style.transform{crate::codestream::WaveletTransform::Arbitrary(index)=>part2_kernel_registry_lookup(kernels,index),_=>None};
            part2_extraction_component_run(plan,precincts,crate::decode::prepare_style_view(style),kernel,maximum,calls)
        },
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_extraction_components_run(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,maximum:u64,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionComponentsEffect>
    decreases count,
{
    if count==0{Some((Ok((Ok(()),initial)),calls))}else{
        part2_tier1_storage_bind(part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,(count-1) as nat,calls),
            |before:Part2ExtractionComponentsEffect,rest|part2_extraction_components_next(before,plans,precincts,styles,kernels,maximum,(count-1) as nat,rest))
    }
}
pub(crate) open spec fn part2_extraction_components_next(before:Part2ExtractionComponentsEffect,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,maximum:u64,index:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionComponentsEffect> {
    if before.0.is_err(){Some((Ok(before),calls))}else if index>=plans.len(){Some((Ok((Err(part1_block_placement_error(false)),before.1)),calls))}
    else{part2_tier1_storage_resume(part2_extraction_reconstruct_component_run(plans[index as int],precincts,styles,kernels,maximum,calls),
        |result:Result<Part1AssemblyTile,crate::DecodeError>,rest|part2_extraction_components_after_child(before.1,plans,precincts,styles,kernels,maximum,index,result,rest))}
}
pub(crate) open spec fn part2_extraction_tile_finish(initial:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,
    mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum:u64,effect:Part2ExtractionComponentsEffect)->Part2ExtractionTileEffect {
    match effect.0{Err(error)=>(Err(error),effect.1,work),Ok(())=>{
        let finished=part2_finish_prepared_tile(effect.1.skip(initial.len() as int),component_count,infos,mct,standard,work,maximum_work,maximum);
        (finished.0,initial+finished.1,finished.2)
    }}
}
pub(crate) open spec fn part2_extraction_tile_finish_run(initial:Seq<Part1AssemblyTile>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,
    mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum:u64,effect:Part2ExtractionComponentsEffect,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionTileEffect> {
    match effect.0{Err(error)=>Some((Ok((Err(error),effect.1,work)),calls)),Ok(())=>{
        part2_tier1_storage_bind(part2_mct_line_finish_run(effect.1.skip(initial.len() as int),component_count,infos,mct,standard,work,maximum_work,maximum,calls),
            |finished:Part2ExtractionTileEffect,rest|Some((Ok((finished.0,initial+finished.1,finished.2)),rest)))
    }}
}
pub(crate) open spec fn part2_extraction_tile_run(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,
    mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionTileEffect> {
    part2_tier1_storage_bind(part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,plans.len(),calls),
        |effect:Part2ExtractionComponentsEffect,rest|part2_extraction_tile_finish_run(initial,component_count,infos,mct,standard,work,maximum_work,maximum,effect,rest))
}
pub(crate) open spec fn part2_extraction_tile_result(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,
    mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum:u64,result:Part2ExtractionTileEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_extraction_tile_run(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum,calls),Ok(result))
}
pub(crate) open spec fn part2_extraction_tile_context(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,work:u64,maximum:u64)->Part2CoefficientReconstructionContext {
    Part2CoefficientReconstructionContext {prior:initial.len(),components:plans.len(),precincts:precincts.len(),work,maximum}
}
pub(crate) open spec fn part2_extraction_tile_calls_run(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,
    mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ExtractionTileEffect> {
    if events.len()==0{None}else{match events[0]{
        Part2JpipSnapshotEvent::CoefficientReconstructionCalls {context,calls}=>if context!=part2_extraction_tile_context(initial,plans,precincts,work,maximum){None}else{
            match part2_extraction_tile_run(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum,calls){
                None=>None,Some((result,rest))=>if rest.len()!=0{None}else{Some((result,events.drop_first()))},
            }
        },
        _=>None,
    }}
}
pub(crate) proof fn part2_extraction_reconstruct_component_normal(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,maximum:u64)
    ensures part2_tier1_storage_framed(|calls|part2_extraction_reconstruct_component_run(plan,precincts,styles,kernels,maximum,calls),part2_reconstruct_component(plan,precincts,styles,kernels,maximum)),
{
    let result=part2_reconstruct_component(plan,precincts,styles,kernels,maximum);
    match crate::codestream::component_coding_style_result(&styles,plan.component){
        Err(_)=>{part2_tier1_storage_pure(result);},Ok(style)=>{
            let kernel=match style.transform{crate::codestream::WaveletTransform::Arbitrary(index)=>part2_kernel_registry_lookup(kernels,index),_=>None};
            part2_extraction_component_normal(plan,precincts,crate::decode::prepare_style_view(style),kernel,maximum);
            part2_tier1_storage_eta(|calls|part2_extraction_component_run(plan,precincts,crate::decode::prepare_style_view(style),kernel,maximum,calls),result);
        },
    }
}
pub(crate) proof fn part2_extraction_reconstruct_component_observed(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,maximum:u64,
    style:crate::codestream::CodingStyle,result:Result<Part1AssemblyTile,crate::DecodeError>)
    requires crate::codestream::component_coding_style_result(&styles,plan.component)==Ok(style),
        part2_extraction_component_result(plan,precincts,crate::decode::prepare_style_view(style),
            match style.transform{crate::codestream::WaveletTransform::Arbitrary(index)=>part2_kernel_registry_lookup(kernels,index),_=>None},maximum,result),
    ensures part2_tier1_storage_framed(|calls|part2_extraction_reconstruct_component_run(plan,precincts,styles,kernels,maximum,calls),result),
{
    let kernel=match style.transform{crate::codestream::WaveletTransform::Arbitrary(index)=>part2_kernel_registry_lookup(kernels,index),_=>None};
    part2_tier1_storage_eta(|calls|part2_extraction_component_run(plan,precincts,crate::decode::prepare_style_view(style),kernel,maximum,calls),result);
}
pub(crate) proof fn part2_extraction_components_normal(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,maximum:u64,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,count,calls),Ok(part2_reconstruct_components_prefix(initial,plans,precincts,styles,kernels,maximum,count))),
    decreases count,
{
    reveal(part2_extraction_components_run);reveal(part2_reconstruct_components_prefix);
    let result=part2_reconstruct_components_prefix(initial,plans,precincts,styles,kernels,maximum,count);
    if count==0{part2_tier1_storage_pure(Ok(result));}else{
        let before=part2_reconstruct_components_prefix(initial,plans,precincts,styles,kernels,maximum,(count-1) as nat);
        part2_extraction_components_normal(initial,plans,precincts,styles,kernels,maximum,(count-1) as nat);
        if before.0.is_err() || count-1>=plans.len(){part2_tier1_storage_pure(Ok(result));}
        else{
            let plan=plans[count-1];let value=part2_reconstruct_component(plan,precincts,styles,kernels,maximum);
            part2_extraction_reconstruct_component_normal(plan,precincts,styles,kernels,maximum);
            part2_extraction_components_after_child_normal(before.1,plans,precincts,styles,kernels,maximum,(count-1) as nat,value);
            part2_tier1_storage_eta(|calls|part2_extraction_components_after_child(before.1,plans,precincts,styles,kernels,maximum,(count-1) as nat,value,calls),Ok(result));
            part2_tier1_resume_frame(|calls|part2_extraction_reconstruct_component_run(plan,precincts,styles,kernels,maximum,calls),
                |value:Result<Part1AssemblyTile,crate::DecodeError>,rest|part2_extraction_components_after_child(before.1,plans,precincts,styles,kernels,maximum,(count-1) as nat,value,rest),value,Ok(result));
        }
        part2_tier1_storage_bind_frame(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,(count-1) as nat,calls),
            |before:Part2ExtractionComponentsEffect,rest|part2_extraction_components_next(before,plans,precincts,styles,kernels,maximum,(count-1) as nat,rest),Ok(before),Ok(result));
    }
}
pub(crate) proof fn part2_extraction_components_step(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,maximum:u64,index:nat,before:Seq<Part1AssemblyTile>,result:Result<Part1AssemblyTile,crate::DecodeError>)
    requires index<plans.len(),part2_reconstruct_components_prefix(initial,plans,precincts,styles,kernels,maximum,index)==(Ok(()),before),
        part2_tier1_storage_framed(|calls|part2_extraction_reconstruct_component_run(plans[index as int],precincts,styles,kernels,maximum,calls),result),
    ensures part2_tier1_storage_framed(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,index+1,calls),
        Ok(match result{Err(error)=>(Err(error),before),Ok(value)=>(Ok(()),before.push(value))})),
{
    reveal(part2_extraction_components_run);
    let effect=match result{Err(error)=>(Err(error),before),Ok(value)=>(Ok(()),before.push(value))};
    part2_extraction_components_normal(initial,plans,precincts,styles,kernels,maximum,index);
    part2_extraction_components_after_child_normal(before,plans,precincts,styles,kernels,maximum,index,result);
    part2_tier1_storage_eta(|calls|part2_extraction_components_after_child(before,plans,precincts,styles,kernels,maximum,index,result,calls),Ok(effect));
    part2_tier1_resume_frame(|calls|part2_extraction_reconstruct_component_run(plans[index as int],precincts,styles,kernels,maximum,calls),
        |value:Result<Part1AssemblyTile,crate::DecodeError>,rest|part2_extraction_components_after_child(before,plans,precincts,styles,kernels,maximum,index,value,rest),result,Ok(effect));
    part2_tier1_storage_bind_frame(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,index,calls),
        |value:Part2ExtractionComponentsEffect,rest|part2_extraction_components_next(value,plans,precincts,styles,kernels,maximum,index,rest),Ok((Ok(()),before)),Ok(effect));
}
pub(crate) proof fn part2_extraction_components_error(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,maximum:u64,prefix:nat,count:nat,effect:Part2ExtractionComponentsEffect)
    requires prefix<=count,effect.0.is_err(),part2_tier1_storage_framed(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,prefix,calls),Ok(effect)),
    ensures part2_tier1_storage_framed(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,count,calls),Ok(effect)),
    decreases count-prefix,
{
    if prefix<count{
        reveal(part2_extraction_components_run);
        part2_extraction_components_error(initial,plans,precincts,styles,kernels,maximum,prefix,(count-1) as nat,effect);
        part2_tier1_storage_pure(Ok(effect));
        part2_tier1_storage_bind_frame(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,(count-1) as nat,calls),
            |value:Part2ExtractionComponentsEffect,rest|part2_extraction_components_next(value,plans,precincts,styles,kernels,maximum,(count-1) as nat,rest),Ok(effect),Ok(effect));
    }
}
pub(crate) proof fn part2_extraction_components_publication_refused(initial:Seq<Part1AssemblyTile>,context:Part2PreparedComponentContext)
    requires context.index<context.plans.len(),
        part2_reconstruct_components_prefix(initial,context.plans,context.precincts,context.styles,context.kernels,context.maximum,context.index)==(Ok(()),context.before),
        part2_tier1_storage_framed(|calls|part2_extraction_reconstruct_component_run(context.plans[context.index as int],context.precincts,context.styles,context.kernels,context.maximum,calls),Ok(context.value)),
        part2_prepared_component_capacity_result(context,Err(crate::DecodeError::AllocationFailed)),
    ensures part2_tier1_storage_framed(|calls|part2_extraction_components_run(initial,context.plans,context.precincts,context.styles,context.kernels,context.maximum,context.plans.len(),calls),
        Ok((Err(crate::DecodeError::AllocationFailed),context.before))),
{
    reveal_with_fuel(part2_extraction_components_run,1);
    let before=context.before;let plans=context.plans;let precincts=context.precincts;let styles=context.styles;let kernels=context.kernels;
    let maximum=context.maximum;let index=context.index;let value=context.value;let error=crate::DecodeError::AllocationFailed;
    let effect=(Err(error),before);
    part2_tier1_storage_pure(Ok(effect));
    part2_tier1_resume_frame(|calls|part2_prepared_component_capacity_run(context,calls),
        |reply:Result<(),crate::DecodeError>,rest|Some((Ok(match reply{Err(error)=>(Err(error),before),Ok(())=>(Ok(()),before.push(value))}),rest)),
        Err(error),Ok(effect));
    part2_tier1_storage_eta(|calls|part2_extraction_components_after_child(before,plans,precincts,styles,kernels,maximum,index,Ok(value),calls),Ok(effect));
    part2_tier1_resume_frame(|calls|part2_extraction_reconstruct_component_run(plans[index as int],precincts,styles,kernels,maximum,calls),
        |result:Result<Part1AssemblyTile,crate::DecodeError>,rest|part2_extraction_components_after_child(before,plans,precincts,styles,kernels,maximum,index,result,rest),
        Ok(value),Ok(effect));
    part2_extraction_components_normal(initial,plans,precincts,styles,kernels,maximum,index);
    part2_tier1_storage_bind_frame(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,index,calls),
        |prior:Part2ExtractionComponentsEffect,rest|part2_extraction_components_next(prior,plans,precincts,styles,kernels,maximum,index,rest),Ok((Ok(()),before)),Ok(effect));
    assert(part2_tier1_storage_framed(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,index+1,calls),Ok(effect)));
    part2_extraction_components_error(initial,plans,precincts,styles,kernels,maximum,index+1,plans.len(),effect);
}
pub(crate) proof fn part2_extraction_tile_publication_refused(initial:Seq<Part1AssemblyTile>,context:Part2PreparedComponentContext,
    component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64)
    requires context.index<context.plans.len(),
        part2_reconstruct_components_prefix(initial,context.plans,context.precincts,context.styles,context.kernels,context.maximum,context.index)==(Ok(()),context.before),
        part2_tier1_storage_framed(|calls|part2_extraction_reconstruct_component_run(context.plans[context.index as int],context.precincts,context.styles,context.kernels,context.maximum,calls),Ok(context.value)),
        part2_prepared_component_capacity_result(context,Err(crate::DecodeError::AllocationFailed)),
    ensures part2_extraction_tile_result(initial,context.plans,context.precincts,context.styles,context.kernels,component_count,infos,mct,standard,work,maximum_work,context.maximum,
        (Err(crate::DecodeError::AllocationFailed),context.before,work)),
{
    part2_extraction_components_publication_refused(initial,context);
    let effect=(Err(crate::DecodeError::AllocationFailed),context.before);
    let result=(effect.0,effect.1,work);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(
        |calls|part2_extraction_components_run(initial,context.plans,context.precincts,context.styles,context.kernels,context.maximum,context.plans.len(),calls),
        |value:Part2ExtractionComponentsEffect,rest|part2_extraction_tile_finish_run(initial,component_count,infos,mct,standard,work,maximum_work,context.maximum,value,rest),Ok(effect),Ok(result));
}
pub(crate) proof fn part2_extraction_tile_normal(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,
    mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum:u64)
    ensures part2_extraction_tile_result(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum,
        part2_reconstruct_planned_tile(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum)),
{
    let before=part2_reconstruct_components_prefix(initial,plans,precincts,styles,kernels,maximum,plans.len());
    let result=part2_reconstruct_planned_tile(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum);
    part2_extraction_components_normal(initial,plans,precincts,styles,kernels,maximum,plans.len());part2_tier1_storage_pure(Ok(result));
    if before.0.is_ok(){
        let finished=part2_finish_prepared_tile(before.1.skip(initial.len() as int),component_count,infos,mct,standard,work,maximum_work,maximum);
        part2_mct_line_finish_normal(before.1.skip(initial.len() as int),component_count,infos,mct,standard,work,maximum_work,maximum);
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_finish_run(before.1.skip(initial.len() as int),component_count,infos,mct,standard,work,maximum_work,maximum,calls),
            |finished:Part2ExtractionTileEffect,rest|Some((Ok((finished.0,initial+finished.1,finished.2)),rest)),Ok(finished),Ok(result));
    }
    part2_tier1_storage_bind_frame(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,plans.len(),calls),
        |value:Part2ExtractionComponentsEffect,rest|part2_extraction_tile_finish_run(initial,component_count,infos,mct,standard,work,maximum_work,maximum,value,rest),Ok(before),Ok(result));
}
pub(crate) proof fn part2_extraction_tile_component_error(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,
    mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum:u64,index:nat,before:Seq<Part1AssemblyTile>,error:crate::DecodeError)
    requires index<plans.len(),part2_reconstruct_components_prefix(initial,plans,precincts,styles,kernels,maximum,index)==(Ok(()),before),
        part2_tier1_storage_framed(|calls|part2_extraction_reconstruct_component_run(plans[index as int],precincts,styles,kernels,maximum,calls),Err(error)),
    ensures part2_extraction_tile_result(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum,(Err(error),before,work)),
{
    let effect=(Err(error),before);
    part2_extraction_components_step(initial,plans,precincts,styles,kernels,maximum,index,before,Err(error));
    part2_extraction_components_error(initial,plans,precincts,styles,kernels,maximum,index+1,plans.len(),effect);
    part2_tier1_storage_pure(Ok::<Part2ExtractionTileEffect,crate::DecodeError>((Err(error),before,work)));
    part2_tier1_storage_bind_frame(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,plans.len(),calls),
        |value:Part2ExtractionComponentsEffect,rest|part2_extraction_tile_finish_run(initial,component_count,infos,mct,standard,work,maximum_work,maximum,value,rest),Ok(effect),Ok((Err(error),before,work)));
}
pub(crate) proof fn part2_extraction_tile_finish_observed(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,
    mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum:u64,before:Seq<Part1AssemblyTile>,finished:Part2ExtractionTileEffect)
    requires part2_reconstruct_components_prefix(initial,plans,precincts,styles,kernels,maximum,plans.len())==(Ok(()),before),
        part2_mct_line_finish_result(before.skip(initial.len() as int),component_count,infos,mct,standard,work,maximum_work,maximum,finished),
    ensures part2_extraction_tile_result(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum,(finished.0,initial+finished.1,finished.2)),
{
    let result=(finished.0,initial+finished.1,finished.2);
    part2_extraction_components_normal(initial,plans,precincts,styles,kernels,maximum,plans.len());
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_finish_run(before.skip(initial.len() as int),component_count,infos,mct,standard,work,maximum_work,maximum,calls),
        |finished:Part2ExtractionTileEffect,rest|Some((Ok((finished.0,initial+finished.1,finished.2)),rest)),Ok(finished),Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_extraction_components_run(initial,plans,precincts,styles,kernels,maximum,plans.len(),calls),
        |value:Part2ExtractionComponentsEffect,rest|part2_extraction_tile_finish_run(initial,component_count,infos,mct,standard,work,maximum_work,maximum,value,rest),Ok((Ok(()),before)),Ok(result));
}
pub(crate) proof fn part2_extraction_tile_calls_observed(initial:Seq<Part1AssemblyTile>,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,
    styles:crate::codestream::ComponentCodingStyles,kernels:Seq<(u8,Part2RawKernel)>,component_count:u16,infos:Seq<crate::codestream::ComponentInfo>,
    mct:Option<Seq<Part2MctStage>>,standard:(bool,bool),work:u64,maximum_work:u64,maximum:u64,result:Part2ExtractionTileEffect)
    requires part2_extraction_tile_result(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum,result),
    ensures part2_cold_framed(|events|part2_extraction_tile_calls_run(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum,events),Ok(result)),
{
    let raw=|calls|part2_extraction_tile_run(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum,calls);
    let calls=choose|calls| #[trigger] part2_tier1_storage_prefix(raw,calls,Ok(result));
    part2_tier1_storage_at(raw,calls,Ok(result),Seq::empty());assert(calls+Seq::empty() =~= calls);
    let prefix=seq![Part2JpipSnapshotEvent::CoefficientReconstructionCalls {context:part2_extraction_tile_context(initial,plans,precincts,work,maximum),calls}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_extraction_tile_calls_run(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum,prefix+tail)==Some((Ok(result),tail)) by{
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|part2_extraction_tile_calls_run(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum,events),prefix,Ok(result)));
    part2_decode_eta(|events|part2_extraction_tile_calls_run(initial,plans,precincts,styles,kernels,component_count,infos,mct,standard,work,maximum_work,maximum,events),Ok(result));
}
pub(crate) open spec fn part2_extraction_progression_finish(size:Part1AssemblySize,global:crate::codestream::CodingStyle,maximum:u64,effect:Part2ExtractionComponentsEffect)->Result<Part1DecodedImageModel,crate::DecodeError> {
    match effect.0{Err(error)=>Err(error),Ok(())=>{
        if !global.multiple_component_transform{part1_decode_prepared_image(size,effect.1,crate::decode::ComponentTransform::None,maximum)}
        else{match global.transform{
            crate::codestream::WaveletTransform::Reversible5x3=>part1_decode_prepared_image(size,effect.1,crate::decode::ComponentTransform::Reversible,maximum),
            crate::codestream::WaveletTransform::Irreversible9x7=>part1_decode_prepared_image(size,effect.1,crate::decode::ComponentTransform::Irreversible,maximum),
            crate::codestream::WaveletTransform::Arbitrary(_)=>Err(crate::DecodeError::MalformedInput {offset:0,kind:crate::MalformedKind::MissingRequiredStructure}),
        }}
    }}
}
pub(crate) open spec fn part2_extraction_progression_finish_run(size:Part1AssemblySize,global:crate::codestream::CodingStyle,maximum:u64,effect:Part2ExtractionComponentsEffect,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1DecodedImageModel> {
    if effect.0.is_err(){Some((Err(effect.0.get_Err_0()),calls))}else{
        part2_tier1_storage_bind(part2_prepared_views_run(effect.1,calls),
            |_:Seq<Part1AssemblyTile>,rest|Some((part2_extraction_progression_finish(size,global,maximum,effect),rest)))
    }
}
pub(crate) proof fn part2_extraction_progression_finish_normal(size:Part1AssemblySize,global:crate::codestream::CodingStyle,maximum:u64,effect:Part2ExtractionComponentsEffect)
    ensures part2_tier1_storage_framed(|calls|part2_extraction_progression_finish_run(size,global,maximum,effect,calls),part2_extraction_progression_finish(size,global,maximum,effect)),
{
    let result=part2_extraction_progression_finish(size,global,maximum,effect);
    part2_tier1_storage_pure(result);
    if effect.0.is_ok(){
        part2_prepared_views_observed(effect.1,Ok(()));
        part2_tier1_storage_bind_frame(|calls|part2_prepared_views_run(effect.1,calls),
            |_:Seq<Part1AssemblyTile>,rest|Some((part2_extraction_progression_finish(size,global,maximum,effect),rest)),Ok(effect.1),result);
    }
}
pub(crate) open spec fn part2_extraction_progression_run(size:Part1AssemblySize,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,styles:crate::codestream::ComponentCodingStyles,
    global:crate::codestream::CodingStyle,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1DecodedImageModel> {
    part2_tier1_storage_bind(part2_extraction_components_run(Seq::empty(),plans,precincts,styles,Seq::empty(),maximum,plans.len(),calls),
        |effect:Part2ExtractionComponentsEffect,rest|part2_extraction_progression_finish_run(size,global,maximum,effect,rest))
}
pub closed spec fn part2_coefficient_progression_result(size:Part1AssemblySize,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,styles:crate::codestream::ComponentCodingStyles,
    global:crate::codestream::CodingStyle,maximum:u64,result:Result<Part1DecodedImageModel,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_extraction_progression_run(size,plans,precincts,styles,global,maximum,calls),result)
}
pub(crate) proof fn part2_coefficient_progression_publication_refused(size:Part1AssemblySize,context:Part2PreparedComponentContext,global:crate::codestream::CodingStyle)
    requires context.kernels==Seq::<(u8,Part2RawKernel)>::empty(),context.index<context.plans.len(),
        part2_reconstruct_components_prefix(Seq::empty(),context.plans,context.precincts,context.styles,context.kernels,context.maximum,context.index)==(Ok(()),context.before),
        part2_tier1_storage_framed(|calls|part2_extraction_reconstruct_component_run(context.plans[context.index as int],context.precincts,context.styles,context.kernels,context.maximum,calls),Ok(context.value)),
        part2_prepared_component_capacity_result(context,Err(crate::DecodeError::AllocationFailed)),
    ensures part2_coefficient_progression_result(size,context.plans,context.precincts,context.styles,global,context.maximum,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_coefficient_progression_result);
    part2_extraction_components_publication_refused(Seq::empty(),context);
    let effect=(Err(crate::DecodeError::AllocationFailed),context.before);
    part2_tier1_storage_pure(Err::<Part1DecodedImageModel,crate::DecodeError>(crate::DecodeError::AllocationFailed));
    part2_tier1_storage_bind_frame(
        |calls|part2_extraction_components_run(Seq::empty(),context.plans,context.precincts,context.styles,Seq::empty(),context.maximum,context.plans.len(),calls),
        |value:Part2ExtractionComponentsEffect,rest|part2_extraction_progression_finish_run(size,global,context.maximum,value,rest),Ok(effect),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_coefficient_progression_normal(size:Part1AssemblySize,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,styles:crate::codestream::ComponentCodingStyles,
    global:crate::codestream::CodingStyle,maximum:u64)
    ensures part2_coefficient_progression_result(size,plans,precincts,styles,global,maximum,part1_progression_prepared_image(size,plans,precincts,styles,global,maximum)),
{
    reveal(part2_coefficient_progression_result);
    let effect=part2_reconstruct_components_prefix(Seq::empty(),plans,precincts,styles,Seq::empty(),maximum,plans.len());
    let result=part1_progression_prepared_image(size,plans,precincts,styles,global,maximum);
    part2_extraction_components_normal(Seq::empty(),plans,precincts,styles,Seq::empty(),maximum,plans.len());
    part2_extraction_progression_finish_normal(size,global,maximum,effect);
    part2_tier1_storage_eta(|calls|part2_extraction_progression_finish_run(size,global,maximum,effect,calls),result);
    part2_tier1_storage_bind_frame(|calls|part2_extraction_components_run(Seq::empty(),plans,precincts,styles,Seq::empty(),maximum,plans.len(),calls),
        |value:Part2ExtractionComponentsEffect,rest|part2_extraction_progression_finish_run(size,global,maximum,value,rest),Ok(effect),result);
}
pub(crate) proof fn part2_coefficient_progression_error(size:Part1AssemblySize,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,styles:crate::codestream::ComponentCodingStyles,
    global:crate::codestream::CodingStyle,maximum:u64,index:nat,before:Seq<Part1AssemblyTile>,error:crate::DecodeError)
    requires index<plans.len(),part2_reconstruct_components_prefix(Seq::empty(),plans,precincts,styles,Seq::empty(),maximum,index)==(Ok(()),before),
        part2_tier1_storage_framed(|calls|part2_extraction_reconstruct_component_run(plans[index as int],precincts,styles,Seq::empty(),maximum,calls),Err(error)),
    ensures part2_coefficient_progression_result(size,plans,precincts,styles,global,maximum,Err(error)),
{
    reveal(part2_coefficient_progression_result);
    let effect=(Err(error),before);
    part2_extraction_components_step(Seq::empty(),plans,precincts,styles,Seq::empty(),maximum,index,before,Err(error));
    part2_extraction_components_error(Seq::empty(),plans,precincts,styles,Seq::empty(),maximum,index+1,plans.len(),effect);
    part2_tier1_storage_pure(Err::<Part1DecodedImageModel,crate::DecodeError>(error));
    part2_tier1_storage_bind_frame(|calls|part2_extraction_components_run(Seq::empty(),plans,precincts,styles,Seq::empty(),maximum,plans.len(),calls),
        |value:Part2ExtractionComponentsEffect,rest|part2_extraction_progression_finish_run(size,global,maximum,value,rest),Ok(effect),Err(error));
}
pub(crate) proof fn part2_coefficient_progression_views_refused(size:Part1AssemblySize,plans:Seq<Part1PreparePlan>,precincts:Seq<Seq<Tier1RawPlane>>,styles:crate::codestream::ComponentCodingStyles,
    global:crate::codestream::CodingStyle,maximum:u64,prepared:Seq<Part1AssemblyTile>,error:crate::DecodeError)
    requires part2_reconstruct_components_prefix(Seq::empty(),plans,precincts,styles,Seq::empty(),maximum,plans.len())==(Ok(()),prepared),
        part2_prepared_views_result(prepared,Err(error)),
    ensures part2_coefficient_progression_result(size,plans,precincts,styles,global,maximum,Err(error)),
{
    reveal(part2_coefficient_progression_result);
    let effect=(Ok(()),prepared);
    part2_tier1_storage_bind_frame(|calls|part2_prepared_views_run(prepared,calls),
        |_:Seq<Part1AssemblyTile>,rest|Some((part2_extraction_progression_finish(size,global,maximum,effect),rest)),Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_extraction_progression_finish_run(size,global,maximum,effect,calls),Err(error));
    part2_extraction_components_normal(Seq::empty(),plans,precincts,styles,Seq::empty(),maximum,plans.len());
    part2_tier1_storage_bind_frame(|calls|part2_extraction_components_run(Seq::empty(),plans,precincts,styles,Seq::empty(),maximum,plans.len(),calls),
        |value:Part2ExtractionComponentsEffect,rest|part2_extraction_progression_finish_run(size,global,maximum,value,rest),Ok(effect),Err(error));
}
}
