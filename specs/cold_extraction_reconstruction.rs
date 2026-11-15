//! Actual extraction calls through placement/component/tile reconstruction.
use super::*;
verus! {
pub type Part2ExtractionWorkingEffect=(Result<(),crate::DecodeError>,Part1PrepareWorking);
pub(crate) open spec fn part2_extraction_place_admit(working:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,precincts:Seq<Seq<Tier1RawPlane>>,
    placement:crate::decode::ProgressionCodeBlockPlacement)->Result<Option<(crate::decode::SubbandGeometry,Tier1RawPlane)>,crate::DecodeError> {
    if placement.subband_index>=working.0.len(){Ok(None)}
    else if placement.subband_index>=bands.len() || placement.precinct_index>=precincts.len(){Err(part1_block_placement_error(false))}
    else if placement.decoder_index>=precincts[placement.precinct_index as int].len(){Err(part1_packet_header_error())}
    else{
        let geometry=bands[placement.subband_index as int];let plane=precincts[placement.precinct_index as int][placement.decoder_index as int];
        if placement.x as int+plane.width as int>u32::MAX{Err(part1_block_placement_error(true))}
        else if placement.x as int+plane.width as int>geometry.width{Err(part1_block_placement_error(false))}
        else if placement.y as int+plane.height as int>u32::MAX{Err(part1_block_placement_error(true))}
        else if placement.y as int+plane.height as int>geometry.height{Err(part1_block_placement_error(false))}
        else{Ok(Some((geometry,plane)))}
    }
}
pub(crate) open spec fn part2_extraction_place_after(working:Part1PrepareWorking,geometry:crate::decode::SubbandGeometry,placement:crate::decode::ProgressionCodeBlockPlacement,
    plane:Tier1RawPlane,reversible:bool,maximum:u64,coefficients:Result<Seq<Part1QuantizedCoefficient>,crate::DecodeError>)->Part2ExtractionWorkingEffect {
    match coefficients{
        Err(error)=>(Err(error),working),
        Ok(values)=>match part1_inverse_quantization(values,geometry.quantization_step.exponent,geometry.quantization_step.mantissa,geometry.dynamic_range,reversible,geometry.roi_shift,maximum){
            Err(error)=>(Err(error),working),
            Ok(quantized)=>if quantized.2!=part1_prepare_fraction(reversible) || placement.subband_index>=working.0.len(){(Err(part1_block_placement_error(false)),working)}
            else{let written=part1_quantized_block_rows(working.0[placement.subband_index as int],quantized.3,plane.width as u32,placement.x,placement.y,plane.height as nat);
                (written.0,(working.0.update(placement.subband_index as int,written.1),working.1))}
        },
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_extraction_place_run(working:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,precincts:Seq<Seq<Tier1RawPlane>>,
    placement:crate::decode::ProgressionCodeBlockPlacement,reversible:bool,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionWorkingEffect> {
    match part2_extraction_place_admit(working,bands,precincts,placement){
        Err(error)=>Some((Ok((Err(error),working)),calls)),Ok(None)=>Some((Ok((Ok(()),working)),calls)),
        Ok(Some((geometry,plane)))=>part2_tier1_storage_resume(part2_extraction_run(plane,true,calls),
            |result:Result<Seq<Part1QuantizedCoefficient>,crate::DecodeError>,rest|Some((Ok(part2_extraction_place_after(working,geometry,placement,plane,reversible,maximum,result)),rest))),
    }
}
pub(crate) open spec fn part2_extraction_place_result(working:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,precincts:Seq<Seq<Tier1RawPlane>>,
    placement:crate::decode::ProgressionCodeBlockPlacement,reversible:bool,maximum:u64,result:Part2ExtractionWorkingEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_extraction_place_run(working,bands,precincts,placement,reversible,maximum,calls),Ok(result))
}
#[verifier::opaque]
pub(crate) open spec fn part2_extraction_placements_run(initial:Part1PrepareWorking,plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,reversible:bool,maximum:u64,count:nat,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionWorkingEffect>
    decreases count,
{
    if count==0{Some((Ok((Ok(()),initial)),calls))}else{
        part2_tier1_storage_bind(part2_extraction_placements_run(initial,plan,precincts,reversible,maximum,(count-1) as nat,calls),
            |effect:Part2ExtractionWorkingEffect,rest|part2_extraction_placements_next(effect,plan,precincts,reversible,maximum,(count-1) as nat,rest))
    }
}
pub(crate) open spec fn part2_extraction_placements_next(effect:Part2ExtractionWorkingEffect,plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,reversible:bool,maximum:u64,index:nat,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionWorkingEffect> {
    if effect.0.is_err(){Some((Ok(effect),calls))}
    else{part2_extraction_place_run(effect.1,plan.subbands,precincts,plan.placements[index as int],reversible,maximum,calls)}
}
pub(crate) open spec fn part2_extraction_component_admit(plan:Part1PreparePlan,style:Part1PrepareStyle,kernel:Option<Part2RawKernel>,maximum:u64)->Result<(bool,Part1PrepareWorking),crate::DecodeError> {
    if plan.subbands.len()==0{Err(part1_block_placement_error(false))}else{match part2_prepare_reversible(style,kernel){
        Err(error)=>Err(error),Ok(reversible)=>match part1_subband_count_through_resolution(style.1,style.2,plan.resolution){
            Err(error)=>Err(error),Ok(selected)=>if selected>plan.subbands.len(){Err(part1_block_placement_error(false))}else{
                match part1_prepare_init_prefix(plan.subbands,part1_prepare_fraction(reversible),maximum,selected as nat){Err(error)=>Err(error),Ok(initial)=>Ok((reversible,initial))}
            },
        },
    }}
}
pub(crate) open spec fn part2_extraction_component_finish(plan:Part1PreparePlan,style:Part1PrepareStyle,kernel:Option<Part2RawKernel>,reversible:bool,maximum:u64,placed:Part2ExtractionWorkingEffect)
    ->Result<Part1AssemblyTile,crate::DecodeError> {
    match placed.0{
        Err(error)=>Err(error),Ok(())=>match part1_prepare_coverage(placed.1.0){
            Err(error)=>Err(error),Ok(())=>if placed.1.0.len()==0{Err(part1_block_placement_error(false))}else{
                let ll=placed.1.0[0];
                match part2_prepare_fold((ll.0,ll.1,ll.3,1usize),placed.1.0,plan.subbands,style,reversible,kernel,maximum,plan.resolution as nat){
                    Err(error)=>Err(error),Ok(folded)=>part1_prepare_finish(plan,part1_prepare_fraction(reversible),folded),
                }
            },
        },
    }
}
pub(crate) open spec fn part2_extraction_component_run(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,style:Part1PrepareStyle,kernel:Option<Part2RawKernel>,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1AssemblyTile> {
    match part2_extraction_component_admit(plan,style,kernel,maximum){
        Err(error)=>Some((Err(error),calls)),Ok((reversible,initial))=>part2_tier1_storage_bind(part2_extraction_placements_run(initial,plan,precincts,reversible,maximum,plan.placements.len(),calls),
            |placed:Part2ExtractionWorkingEffect,rest|Some((part2_extraction_component_finish(plan,style,kernel,reversible,maximum,placed),rest))),
    }
}
pub(crate) open spec fn part2_extraction_component_result(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,style:Part1PrepareStyle,kernel:Option<Part2RawKernel>,maximum:u64,result:Result<Part1AssemblyTile,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_extraction_component_run(plan,precincts,style,kernel,maximum,calls),result)
}
pub closed spec fn part2_coefficient_component_result(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,style:Part1PrepareStyle,maximum:u64,result:Result<Part1AssemblyTile,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_coefficient_component_run(plan,precincts,style,maximum,calls),result)
}
pub(crate) open spec fn part2_coefficient_component_run(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,style:Part1PrepareStyle,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1AssemblyTile> {
    part2_extraction_component_run(plan,precincts,style,None,maximum,calls)
}
pub(crate) proof fn part2_coefficient_component_observed(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,style:Part1PrepareStyle,maximum:u64,result:Result<Part1AssemblyTile,crate::DecodeError>)
    requires part2_extraction_component_result(plan,precincts,style,None,maximum,result),
    ensures part2_coefficient_component_result(plan,precincts,style,maximum,result),
{reveal(part2_coefficient_component_result);part2_tier1_storage_eta(|calls|part2_extraction_component_run(plan,precincts,style,None,maximum,calls),result);}
pub(crate) proof fn part2_coefficient_component_frames(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,style:Part1PrepareStyle,maximum:u64,result:Result<Part1AssemblyTile,crate::DecodeError>)
    requires part2_coefficient_component_result(plan,precincts,style,maximum,result),
    ensures part2_extraction_component_result(plan,precincts,style,None,maximum,result),
{reveal(part2_coefficient_component_result);part2_tier1_storage_eta(|calls|part2_coefficient_component_run(plan,precincts,style,maximum,calls),result);}
pub(crate) proof fn part2_coefficient_component_normal(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,style:Part1PrepareStyle,maximum:u64)
    ensures part2_coefficient_component_result(plan,precincts,style,maximum,part1_prepare_standard_component(plan,precincts,style,maximum)),
{
    reveal(part1_prepare_standard_component);
    part2_extraction_component_normal(plan,precincts,style,None,maximum);
    part2_coefficient_component_observed(plan,precincts,style,maximum,part1_prepare_standard_component(plan,precincts,style,maximum));
}
pub(crate) proof fn part2_extraction_place_normal(working:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,precincts:Seq<Seq<Tier1RawPlane>>,
    placement:crate::decode::ProgressionCodeBlockPlacement,reversible:bool,maximum:u64)
    ensures part2_extraction_place_result(working,bands,precincts,placement,reversible,maximum,part1_prepare_placement(working,bands,precincts,placement,reversible,maximum)),
{
    reveal(part2_extraction_place_run);reveal(part1_prepare_placement);
    let result=part1_prepare_placement(working,bands,precincts,placement,reversible,maximum);
    match part2_extraction_place_admit(working,bands,precincts,placement){
        Err(_)=>{part2_tier1_storage_pure(Ok(result));},Ok(None)=>{part2_tier1_storage_pure(Ok(result));},
        Ok(Some((geometry,plane)))=>{
            let coefficients=part1_prepare_collect_coefficients(plane);
            part2_extraction_normal(plane,true);part2_tier1_storage_pure(Ok(result));
            part2_tier1_resume_frame(|calls|part2_extraction_run(plane,true,calls),
                |value:Result<Seq<Part1QuantizedCoefficient>,crate::DecodeError>,rest|Some((Ok(part2_extraction_place_after(working,geometry,placement,plane,reversible,maximum,value)),rest)),coefficients,Ok(result));
        },
    }
}
pub(crate) proof fn part2_extraction_place_error(working:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,precincts:Seq<Seq<Tier1RawPlane>>,
    placement:crate::decode::ProgressionCodeBlockPlacement,reversible:bool,maximum:u64,geometry:crate::decode::SubbandGeometry,plane:Tier1RawPlane,error:crate::DecodeError)
    requires part2_extraction_place_admit(working,bands,precincts,placement)==Ok(Some((geometry,plane))),part2_extraction_result(plane,true,Err(error)),
    ensures part2_extraction_place_result(working,bands,precincts,placement,reversible,maximum,(Err(error),working)),
{
    reveal(part2_extraction_place_run);part2_tier1_storage_pure(Ok::<Part2ExtractionWorkingEffect,crate::DecodeError>((Err(error),working)));
    part2_tier1_resume_frame(|calls|part2_extraction_run(plane,true,calls),
        |value:Result<Seq<Part1QuantizedCoefficient>,crate::DecodeError>,rest|Some((Ok(part2_extraction_place_after(working,geometry,placement,plane,reversible,maximum,value)),rest)),Err(error),Ok((Err(error),working)));
}
pub(crate) proof fn part2_extraction_placements_normal(initial:Part1PrepareWorking,plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,reversible:bool,maximum:u64,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_extraction_placements_run(initial,plan,precincts,reversible,maximum,count,calls),Ok(part1_prepare_placements(initial,plan,precincts,reversible,maximum,count))),
    decreases count,
{
    reveal(part2_extraction_placements_run);reveal(part1_prepare_placements);
    let result=part1_prepare_placements(initial,plan,precincts,reversible,maximum,count);
    if count==0{part2_tier1_storage_pure(Ok(result));}else{
        let prefix=part1_prepare_placements(initial,plan,precincts,reversible,maximum,(count-1) as nat);
        part2_extraction_placements_normal(initial,plan,precincts,reversible,maximum,(count-1) as nat);
        if prefix.0.is_err(){part2_tier1_storage_pure(Ok(result));}
        else{
            part2_extraction_place_normal(prefix.1,plan.subbands,precincts,plan.placements[count-1],reversible,maximum);
            part2_tier1_storage_eta(|calls|part2_extraction_place_run(prefix.1,plan.subbands,precincts,plan.placements[count-1],reversible,maximum,calls),Ok(result));
        }
        part2_tier1_storage_bind_frame(|calls|part2_extraction_placements_run(initial,plan,precincts,reversible,maximum,(count-1) as nat,calls),
            |effect:Part2ExtractionWorkingEffect,rest|part2_extraction_placements_next(effect,plan,precincts,reversible,maximum,(count-1) as nat,rest),Ok(prefix),Ok(result));
    }
}
pub(crate) proof fn part2_extraction_placements_step(initial:Part1PrepareWorking,plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,reversible:bool,maximum:u64,index:nat,before:Part1PrepareWorking,effect:Part2ExtractionWorkingEffect)
    requires index<plan.placements.len(),part1_prepare_placements(initial,plan,precincts,reversible,maximum,index)==(Ok(()),before),
        part2_extraction_place_result(before,plan.subbands,precincts,plan.placements[index as int],reversible,maximum,effect),
    ensures part2_tier1_storage_framed(|calls|part2_extraction_placements_run(initial,plan,precincts,reversible,maximum,index+1,calls),Ok(effect)),
{
    reveal(part2_extraction_placements_run);
    part2_extraction_placements_normal(initial,plan,precincts,reversible,maximum,index);
    part2_tier1_storage_eta(|calls|part2_extraction_place_run(before,plan.subbands,precincts,plan.placements[index as int],reversible,maximum,calls),Ok(effect));
    part2_tier1_storage_bind_frame(|calls|part2_extraction_placements_run(initial,plan,precincts,reversible,maximum,index,calls),
        |value:Part2ExtractionWorkingEffect,rest|part2_extraction_placements_next(value,plan,precincts,reversible,maximum,index,rest),Ok((Ok(()),before)),Ok(effect));
}
pub(crate) proof fn part2_extraction_placements_error(initial:Part1PrepareWorking,plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,reversible:bool,maximum:u64,prefix:nat,count:nat,effect:Part2ExtractionWorkingEffect)
    requires prefix<=count,effect.0.is_err(),part2_tier1_storage_framed(|calls|part2_extraction_placements_run(initial,plan,precincts,reversible,maximum,prefix,calls),Ok(effect)),
    ensures part2_tier1_storage_framed(|calls|part2_extraction_placements_run(initial,plan,precincts,reversible,maximum,count,calls),Ok(effect)),
    decreases count-prefix,
{
    if prefix<count{
        reveal(part2_extraction_placements_run);
        part2_extraction_placements_error(initial,plan,precincts,reversible,maximum,prefix,(count-1) as nat,effect);
        part2_tier1_storage_pure(Ok(effect));
        part2_tier1_storage_bind_frame(|calls|part2_extraction_placements_run(initial,plan,precincts,reversible,maximum,(count-1) as nat,calls),
            |value:Part2ExtractionWorkingEffect,rest|part2_extraction_placements_next(value,plan,precincts,reversible,maximum,(count-1) as nat,rest),Ok(effect),Ok(effect));
    }
}
pub(crate) proof fn part2_extraction_component_normal(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,style:Part1PrepareStyle,kernel:Option<Part2RawKernel>,maximum:u64)
    ensures part2_extraction_component_result(plan,precincts,style,kernel,maximum,part2_prepare_component(plan,precincts,style,kernel,maximum)),
{
    reveal(part2_prepare_component);
    let result=part2_prepare_component(plan,precincts,style,kernel,maximum);
    match part2_extraction_component_admit(plan,style,kernel,maximum){
        Err(_)=>{part2_tier1_storage_pure(result);},
        Ok((reversible,initial))=>{
            let placed=part1_prepare_placements(initial,plan,precincts,reversible,maximum,plan.placements.len());
            part2_extraction_placements_normal(initial,plan,precincts,reversible,maximum,plan.placements.len());part2_tier1_storage_pure(result);
            part2_tier1_storage_bind_frame(|calls|part2_extraction_placements_run(initial,plan,precincts,reversible,maximum,plan.placements.len(),calls),
                |effect:Part2ExtractionWorkingEffect,rest|Some((part2_extraction_component_finish(plan,style,kernel,reversible,maximum,effect),rest)),Ok(placed),result);
        },
    }
}
pub(crate) proof fn part2_extraction_component_error(plan:Part1PreparePlan,precincts:Seq<Seq<Tier1RawPlane>>,style:Part1PrepareStyle,kernel:Option<Part2RawKernel>,maximum:u64,
    reversible:bool,initial:Part1PrepareWorking,index:nat,before:Part1PrepareWorking,effect:Part2ExtractionWorkingEffect)
    requires part2_extraction_component_admit(plan,style,kernel,maximum)==Ok((reversible,initial)),index<plan.placements.len(),effect.0.is_err(),
        part1_prepare_placements(initial,plan,precincts,reversible,maximum,index)==(Ok(()),before),
        part2_extraction_place_result(before,plan.subbands,precincts,plan.placements[index as int],reversible,maximum,effect),
    ensures part2_extraction_component_result(plan,precincts,style,kernel,maximum,Err(effect.0.get_Err_0())),
{
    part2_extraction_placements_step(initial,plan,precincts,reversible,maximum,index,before,effect);
    part2_extraction_placements_error(initial,plan,precincts,reversible,maximum,index+1,plan.placements.len(),effect);
    let result=Err::<Part1AssemblyTile,crate::DecodeError>(effect.0.get_Err_0());part2_tier1_storage_pure(result);
    part2_tier1_storage_bind_frame(|calls|part2_extraction_placements_run(initial,plan,precincts,reversible,maximum,plan.placements.len(),calls),
        |value:Part2ExtractionWorkingEffect,rest|Some((part2_extraction_component_finish(plan,style,kernel,reversible,maximum,value),rest)),Ok(effect),result);
}
}
