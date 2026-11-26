use super::*;
verus! {

pub struct PrivateReconstructionContext {
    pub plan:Part1PreparePlan,pub precinct:Seq<PrivateHtPrecinctState>,
    pub style:Part1PrepareStyle,pub maximum:u64,
}

pub(crate) proof fn private_subband_prefix_positive(levels:u8,directions:Seq<crate::codestream::DecompositionDirection>,completed:nat)
    ensures match part1_subband_count_prefix(levels,directions,completed){Err(_)=>true,Ok(count)=>count>0},
    decreases completed,
{
    if completed>0{private_subband_prefix_positive(levels,directions,(completed-1) as nat);}
}

pub(crate) proof fn private_subband_count_positive(levels:u8,directions:Seq<crate::codestream::DecompositionDirection>,resolution:u8)
    ensures match part1_subband_count_through_resolution(levels,directions,resolution){Err(_)=>true,Ok(count)=>count>0},
{
    if resolution<=levels{private_subband_prefix_positive(levels,directions,resolution as nat);}
}

pub(crate) open spec fn private_place_run(working:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,
    precincts:Seq<Seq<Tier1RawPlane>>,placement:crate::decode::ProgressionCodeBlockPlacement,reversible:bool,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionWorkingEffect> {
    part2_extraction_place_run(working,bands,precincts,placement,reversible,maximum,calls)
}

pub(crate) open spec fn private_place_result(working:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,
    precincts:Seq<Seq<Tier1RawPlane>>,placement:crate::decode::ProgressionCodeBlockPlacement,reversible:bool,maximum:u64,
    result:Part2ExtractionWorkingEffect)->bool {
    part2_tier1_storage_framed(|calls|private_place_run(working,bands,precincts,placement,reversible,maximum,calls),Ok(result))
}

pub(crate) proof fn private_place_shared(working:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,
    precincts:Seq<Seq<Tier1RawPlane>>,placement:crate::decode::ProgressionCodeBlockPlacement,reversible:bool,maximum:u64,
    result:Part2ExtractionWorkingEffect)
    requires part2_extraction_place_result(working,bands,precincts,placement,reversible,maximum,result),
    ensures private_place_result(working,bands,precincts,placement,reversible,maximum,result),
{
    part2_tier1_storage_eta(|calls|part2_extraction_place_run(working,bands,precincts,placement,reversible,maximum,calls),Ok(result));
    assert forall|calls:Seq<Part2Tier1StorageEvent>|private_place_run(working,bands,precincts,placement,reversible,maximum,calls)
        ==part2_extraction_place_run(working,bands,precincts,placement,reversible,maximum,calls) by {}
}

pub(crate) proof fn private_place_normal(working:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,
    precincts:Seq<Seq<Tier1RawPlane>>,placement:crate::decode::ProgressionCodeBlockPlacement,reversible:bool,maximum:u64)
    ensures private_place_result(working,bands,precincts,placement,reversible,maximum,
        part1_prepare_placement(working,bands,precincts,placement,reversible,maximum)),
{
    part2_extraction_place_normal(working,bands,precincts,placement,reversible,maximum);
    private_place_shared(working,bands,precincts,placement,reversible,maximum,
        part1_prepare_placement(working,bands,precincts,placement,reversible,maximum));
}

#[verifier::opaque]
pub(crate) open spec fn private_placements_run(initial:Part1PrepareWorking,context:PrivateReconstructionContext,
    reversible:bool,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionWorkingEffect>
    decreases count,
{
    if count==0{Some((Ok((Ok(()),initial)),calls))}
    else{part2_tier1_storage_bind(private_placements_run(initial,context,reversible,(count-1) as nat,calls),
        |effect:Part2ExtractionWorkingEffect,rest|if effect.0.is_err(){Some((Ok(effect),rest))}
            else{private_place_run(effect.1,context.plan.subbands,private_ht_precinct_planes(context.precinct),
                context.plan.placements[count-1],reversible,context.maximum,rest)})}
}

pub(crate) open spec fn private_component_after_init(context:PrivateReconstructionContext,reversible:bool,initial:Part1PrepareWorking,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1AssemblyTile> {
    part2_tier1_storage_bind(private_placements_run(initial,context,reversible,context.plan.placements.len(),calls),
        |effect:Part2ExtractionWorkingEffect,rest|part2_extraction_component_finish_run(context.plan,context.style,None,reversible,context.maximum,effect,rest))
}

pub(crate) open spec fn private_component_run(context:PrivateReconstructionContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1AssemblyTile> {
    match part2_extraction_component_preflight(context.plan,context.style,None){
        Err(error)=>Some((Err(error),calls)),
        Ok((reversible,selected))=>part2_tier1_storage_bind(
            part2_prepare_init_run(context.plan.subbands,selected,part1_prepare_fraction(reversible),context.maximum,calls),
            |initial:Part1PrepareWorking,rest|private_component_after_init(context,reversible,initial,rest)),
    }
}

pub(crate) open spec fn private_component_result(context:PrivateReconstructionContext,result:Result<Part1AssemblyTile,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|private_component_run(context,calls),result)
}

pub(crate) proof fn private_placements_normal(initial:Part1PrepareWorking,context:PrivateReconstructionContext,reversible:bool,count:nat)
    ensures part2_tier1_storage_framed(|calls|private_placements_run(initial,context,reversible,count,calls),
        Ok(part1_prepare_placements(initial,context.plan,private_ht_precinct_planes(context.precinct),reversible,context.maximum,count))),
    decreases count,
{
    reveal(private_placements_run);reveal(part1_prepare_placements);
    let result=part1_prepare_placements(initial,context.plan,private_ht_precinct_planes(context.precinct),reversible,context.maximum,count);
    if count==0{part2_tier1_storage_pure(Ok(result));}else{
        let before=part1_prepare_placements(initial,context.plan,private_ht_precinct_planes(context.precinct),reversible,context.maximum,(count-1) as nat);
        private_placements_normal(initial,context,reversible,(count-1) as nat);
        if before.0.is_err(){part2_tier1_storage_pure(Ok(result));}else{
            private_place_normal(before.1,context.plan.subbands,private_ht_precinct_planes(context.precinct),
                context.plan.placements[count-1],reversible,context.maximum);
            part2_tier1_storage_eta(|calls|private_place_run(before.1,context.plan.subbands,private_ht_precinct_planes(context.precinct),
                context.plan.placements[count-1],reversible,context.maximum,calls),Ok(result));
        }
        part2_tier1_storage_bind_frame(|calls|private_placements_run(initial,context,reversible,(count-1) as nat,calls),
            |effect:Part2ExtractionWorkingEffect,rest|if effect.0.is_err(){Some((Ok(effect),rest))}
                else{private_place_run(effect.1,context.plan.subbands,private_ht_precinct_planes(context.precinct),
                    context.plan.placements[count-1],reversible,context.maximum,rest)},Ok(before),Ok(result));
    }
}

pub(crate) proof fn private_component_normal(context:PrivateReconstructionContext)
    ensures private_component_result(context,part2_prepare_component(context.plan,private_ht_precinct_planes(context.precinct),
        context.style,None,context.maximum)),
{
    reveal(part2_prepare_component);
    let result=part2_prepare_component(context.plan,private_ht_precinct_planes(context.precinct),context.style,None,context.maximum);
    match part2_extraction_component_preflight(context.plan,context.style,None){
        Err(_)=>{part2_tier1_storage_pure(result);},
        Ok((reversible,selected))=>{
            let initial=part1_prepare_init_prefix(context.plan.subbands,part1_prepare_fraction(reversible),context.maximum,selected as nat);
            part2_prepare_init_normal(context.plan.subbands,selected,part1_prepare_fraction(reversible),context.maximum);
            if let Ok(working)=initial{
                let effect=part1_prepare_placements(working,context.plan,private_ht_precinct_planes(context.precinct),reversible,context.maximum,context.plan.placements.len());
                private_placements_normal(working,context,reversible,context.plan.placements.len());
                part2_extraction_component_finish_normal(context.plan,context.style,None,reversible,context.maximum,effect);
                part2_tier1_storage_eta(|calls|part2_extraction_component_finish_run(context.plan,context.style,None,reversible,context.maximum,effect,calls),result);
                part2_tier1_storage_bind_frame(|calls|private_placements_run(working,context,reversible,context.plan.placements.len(),calls),
                    |placed:Part2ExtractionWorkingEffect,rest|part2_extraction_component_finish_run(context.plan,context.style,None,reversible,context.maximum,placed,rest),Ok(effect),result);
            }
            part2_tier1_storage_bind_frame(
                |calls|part2_prepare_init_run(context.plan.subbands,selected,part1_prepare_fraction(reversible),context.maximum,calls),
                |working:Part1PrepareWorking,rest|private_component_after_init(context,reversible,working,rest),initial,result);
        },
    }
}

pub(crate) proof fn private_component_init_error(context:PrivateReconstructionContext,reversible:bool,selected:usize,error:crate::DecodeError)
    requires part2_extraction_component_preflight(context.plan,context.style,None)==Ok((reversible,selected)),
        part2_prepare_init_result(context.plan.subbands,selected,part1_prepare_fraction(reversible),context.maximum,Err(error)),
    ensures private_component_result(context,Err(error)),
{
    part2_tier1_storage_bind_frame(
        |calls|part2_prepare_init_run(context.plan.subbands,selected,part1_prepare_fraction(reversible),context.maximum,calls),
        |initial:Part1PrepareWorking,rest|private_component_after_init(context,reversible,initial,rest),Err(error),Err(error));
}

pub(crate) proof fn private_placements_error(initial:Part1PrepareWorking,context:PrivateReconstructionContext,reversible:bool,
    prefix:nat,count:nat,effect:Part2ExtractionWorkingEffect)
    requires prefix<=count,effect.0.is_err(),
        part2_tier1_storage_framed(|calls|private_placements_run(initial,context,reversible,prefix,calls),Ok(effect)),
    ensures part2_tier1_storage_framed(|calls|private_placements_run(initial,context,reversible,count,calls),Ok(effect)),
    decreases count-prefix,
{
    if prefix<count{
        reveal(private_placements_run);
        private_placements_error(initial,context,reversible,prefix,(count-1) as nat,effect);
        part2_tier1_storage_pure(Ok(effect));
        part2_tier1_storage_bind_frame(|calls|private_placements_run(initial,context,reversible,(count-1) as nat,calls),
            |current:Part2ExtractionWorkingEffect,rest|if current.0.is_err(){Some((Ok(current),rest))}
                else{private_place_run(current.1,context.plan.subbands,private_ht_precinct_planes(context.precinct),
                    context.plan.placements[count-1],reversible,context.maximum,rest)},Ok(effect),Ok(effect));
    }
}

pub(crate) proof fn private_component_placed(context:PrivateReconstructionContext,reversible:bool,selected:usize,initial:Part1PrepareWorking,
    placed:Part2ExtractionWorkingEffect,result:Result<Part1AssemblyTile,crate::DecodeError>)
    requires part2_extraction_component_preflight(context.plan,context.style,None)==Ok((reversible,selected)),
        part1_prepare_init_prefix(context.plan.subbands,part1_prepare_fraction(reversible),context.maximum,selected as nat)==Ok(initial),
        part2_tier1_storage_framed(|calls|private_placements_run(initial,context,reversible,context.plan.placements.len(),calls),Ok(placed)),
        part2_tier1_storage_framed(|calls|part2_extraction_component_finish_run(context.plan,context.style,None,reversible,context.maximum,placed,calls),result),
    ensures private_component_result(context,result),
{
    part2_tier1_storage_eta(|calls|part2_extraction_component_finish_run(context.plan,context.style,None,reversible,context.maximum,placed,calls),result);
    part2_prepare_init_normal(context.plan.subbands,selected,part1_prepare_fraction(reversible),context.maximum);
    part2_tier1_storage_bind_frame(|calls|private_placements_run(initial,context,reversible,context.plan.placements.len(),calls),
        |effect:Part2ExtractionWorkingEffect,rest|part2_extraction_component_finish_run(context.plan,context.style,None,reversible,context.maximum,effect,rest),Ok(placed),result);
    part2_tier1_storage_bind_frame(
        |calls|part2_prepare_init_run(context.plan.subbands,selected,part1_prepare_fraction(reversible),context.maximum,calls),
        |working:Part1PrepareWorking,rest|private_component_after_init(context,reversible,working,rest),Ok(initial),result);
}

pub(crate) proof fn private_component_place_error(context:PrivateReconstructionContext,reversible:bool,selected:usize,initial:Part1PrepareWorking,
    index:nat,before:Part1PrepareWorking,effect:Part2ExtractionWorkingEffect)
    requires part2_extraction_component_preflight(context.plan,context.style,None)==Ok((reversible,selected)),
        part1_prepare_init_prefix(context.plan.subbands,part1_prepare_fraction(reversible),context.maximum,selected as nat)==Ok(initial),
        index<context.plan.placements.len(),effect.0.is_err(),
        part1_prepare_placements(initial,context.plan,private_ht_precinct_planes(context.precinct),reversible,context.maximum,index)==(Ok(()),before),
        private_place_result(before,context.plan.subbands,private_ht_precinct_planes(context.precinct),
            context.plan.placements[index as int],reversible,context.maximum,effect),
    ensures private_component_result(context,Err(effect.0.get_Err_0())),
{
    reveal(private_placements_run);
    private_placements_normal(initial,context,reversible,index);
    part2_tier1_storage_eta(|calls|private_place_run(before,context.plan.subbands,private_ht_precinct_planes(context.precinct),
        context.plan.placements[index as int],reversible,context.maximum,calls),Ok(effect));
    part2_tier1_storage_bind_frame(|calls|private_placements_run(initial,context,reversible,index,calls),
        |current:Part2ExtractionWorkingEffect,rest|if current.0.is_err(){Some((Ok(current),rest))}
            else{private_place_run(current.1,context.plan.subbands,private_ht_precinct_planes(context.precinct),
                context.plan.placements[index as int],reversible,context.maximum,rest)},Ok((Ok(()),before)),Ok(effect));
    private_placements_error(initial,context,reversible,index+1,context.plan.placements.len(),effect);
    part2_tier1_storage_pure(Err::<Part1AssemblyTile,crate::DecodeError>(effect.0.get_Err_0()));
    private_component_placed(context,reversible,selected,initial,effect,Err(effect.0.get_Err_0()));
}

pub(crate) proof fn private_component_folded(context:PrivateReconstructionContext,reversible:bool,selected:usize,
    initial:Part1PrepareWorking,working:Part1PrepareWorking,folded:Result<Part1PrepareFold,crate::DecodeError>)
    requires part2_extraction_component_preflight(context.plan,context.style,None)==Ok((reversible,selected)),
        part1_prepare_init_prefix(context.plan.subbands,part1_prepare_fraction(reversible),context.maximum,selected as nat)==Ok(initial),
        part1_prepare_placements(initial,context.plan,private_ht_precinct_planes(context.precinct),reversible,context.maximum,context.plan.placements.len())==(Ok(()),working),
        part1_prepare_coverage(working.0)==Ok(()),working.0.len()>0,
        part2_wavelet_reconstruct_result(working.0,context.plan,context.style,reversible,None,context.maximum,folded),
    ensures private_component_result(context,match folded{Err(error)=>Err(error),
        Ok(value)=>part1_prepare_finish(context.plan,part1_prepare_fraction(reversible),value)}),
{
    let result=match folded{Err(error)=>Err(error),Ok(value)=>part1_prepare_finish(context.plan,part1_prepare_fraction(reversible),value)};
    part2_wavelet_reconstruct_frames(working.0,context.plan,context.style,reversible,None,context.maximum,folded);
    if folded.is_ok(){part2_tier1_storage_pure(result);}
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_reconstruct_run(working.0,context.plan,context.style,reversible,None,context.maximum,calls),
        |value:Part1PrepareFold,rest|Some((part1_prepare_finish(context.plan,part1_prepare_fraction(reversible),value),rest)),folded,result);
    private_placements_normal(initial,context,reversible,context.plan.placements.len());
    private_component_placed(context,reversible,selected,initial,(Ok(()),working),result);
}
}
