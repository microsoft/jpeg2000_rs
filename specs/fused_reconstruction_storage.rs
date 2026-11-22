//! Lifting one real fused-or-checked band operation into component storage traces.
use super::*;
verus! {
pub(crate) open spec fn part2_fused_position(x:u32,y:u32)->crate::decode::ProgressionCodeBlockPlacement {
    crate::decode::ProgressionCodeBlockPlacement{precinct_index:0,decoder_index:0,subband_index:0,x,y}
}
pub(crate) open spec fn part2_fused_band_result(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,
    geometry:crate::decode::SubbandGeometry,x:u32,y:u32,reversible:bool,maximum:u64,effect:Part1WorkingSubbandState)->bool {
    part2_extraction_place_result((seq![destination],0u64),seq![geometry],seq![seq![plane]],part2_fused_position(x,y),reversible,maximum,
        (effect.0,(seq![effect.1],0u64)))
}
pub(crate) proof fn part2_fused_band_normal(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,
    geometry:crate::decode::SubbandGeometry,x:u32,y:u32,reversible:bool,maximum:u64)
    ensures part2_fused_band_result(destination,plane,geometry,x,y,reversible,maximum,
        part2_fused_band_value(destination,plane,geometry,x,y,reversible,maximum)),
{
    let working=(seq![destination],0u64);
    let position=part2_fused_position(x,y);
    part2_extraction_place_normal(working,seq![geometry],seq![seq![plane]],position,reversible,maximum);
    reveal(part1_prepare_placement);
    let value=part1_prepare_place_plane(working,geometry,position,plane,reversible,maximum);
    assert(value.1.0.len()==1 && value.1.1==0);
    assert(value.1.0 =~=seq![value.1.0[0]]);
}
pub(crate) open spec fn part2_fused_lift_effect(working:Part1PrepareWorking,index:usize,effect:Part2ExtractionWorkingEffect)->Part2ExtractionWorkingEffect {
    (effect.0,(working.0.update(index as int,effect.1.0[0]),working.1))
}
pub(crate) proof fn part2_fused_quantized_lift(working:Part1PrepareWorking,geometry:crate::decode::SubbandGeometry,
    placement:crate::decode::ProgressionCodeBlockPlacement,plane:Tier1RawPlane,reversible:bool,quantized:Part1ReconstructionResult)
    requires placement.subband_index<working.0.len(),
    ensures part2_extraction_place_after_quantization(working,geometry,placement,plane,reversible,quantized)
        ==part2_fused_lift_effect(working,placement.subband_index,
            part2_extraction_place_after_quantization((seq![working.0[placement.subband_index as int]],0u64),geometry,
                part2_fused_position(placement.x,placement.y),plane,reversible,quantized)),
{
    assert(working.0.update(placement.subband_index as int,working.0[placement.subband_index as int]) =~=working.0);
}
pub(crate) proof fn part2_fused_run_lift(working:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,precincts:Seq<Seq<Tier1RawPlane>>,
    placement:crate::decode::ProgressionCodeBlockPlacement,geometry:crate::decode::SubbandGeometry,plane:Tier1RawPlane,reversible:bool,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)
    requires part2_extraction_place_admit(working,bands,precincts,placement)==Ok(Some((geometry,plane))),
        !part2_fused_placement_enabled(working,geometry,placement,plane,reversible,maximum),
    ensures part2_extraction_place_run(working,bands,precincts,placement,reversible,maximum,calls)
        ==part2_tier1_storage_bind(part2_extraction_place_run((seq![working.0[placement.subband_index as int]],0u64),
            seq![geometry],seq![seq![plane]],part2_fused_position(placement.x,placement.y),reversible,maximum,calls),
            |effect:Part2ExtractionWorkingEffect,rest|Some((Ok(part2_fused_lift_effect(working,placement.subband_index,effect)),rest))),
{
    reveal(part2_extraction_place_run);
    let destination=working.0[placement.subband_index as int];
    let local=(seq![destination],0u64);
    let position=part2_fused_position(placement.x,placement.y);
    assert(part2_extraction_place_admit(local,seq![geometry],seq![seq![plane]],position)==Ok(Some((geometry,plane))));
    assert(!part2_fused_placement_enabled(local,geometry,position,plane,reversible,maximum));
    assert(working.0.update(placement.subband_index as int,destination) =~=working.0);
    match part2_extraction_run(plane,true,calls){
        None=>{},Some((Err(_),_))=>{},Some((Ok(values),rest))=>{
            match part2_quantization_plane_run(values,geometry.quantization_step.exponent,geometry.quantization_step.mantissa,
                geometry.dynamic_range,reversible,geometry.roi_shift,maximum,rest){
                None=>{},Some((quantized,tail))=>{
                    part2_fused_quantized_lift(working,geometry,placement,plane,reversible,quantized);
                },
            }
        },
    }
}
pub(crate) proof fn part2_fused_allocation_lift(working:Part1PrepareWorking,bands:Seq<crate::decode::SubbandGeometry>,precincts:Seq<Seq<Tier1RawPlane>>,
    placement:crate::decode::ProgressionCodeBlockPlacement,geometry:crate::decode::SubbandGeometry,plane:Tier1RawPlane,reversible:bool,maximum:u64)
    requires part2_extraction_place_admit(working,bands,precincts,placement)==Ok(Some((geometry,plane))),
        !part2_fused_placement_enabled(working,geometry,placement,plane,reversible,maximum),
        part2_fused_band_result(working.0[placement.subband_index as int],plane,geometry,placement.x,placement.y,reversible,maximum,
            (Err(crate::DecodeError::AllocationFailed),working.0[placement.subband_index as int])),
    ensures part2_extraction_place_result(working,bands,precincts,placement,reversible,maximum,(Err(crate::DecodeError::AllocationFailed),working)),
{
    let destination=working.0[placement.subband_index as int];
    let local=(seq![destination],0u64);
    let position=part2_fused_position(placement.x,placement.y);
    let run=|calls|part2_extraction_place_run(local,seq![geometry],seq![seq![plane]],position,reversible,maximum,calls);
    let effect=(Err(crate::DecodeError::AllocationFailed),local);
    let prefix=choose|prefix|part2_tier1_storage_prefix(run,prefix,Ok(effect));
    assert(working.0.update(placement.subband_index as int,destination) =~=working.0);
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_extraction_place_run(working,bands,precincts,placement,reversible,maximum,prefix+tail)
        ==Some((Ok((Err(crate::DecodeError::AllocationFailed),working)),tail)) by{
        part2_tier1_storage_at(run,prefix,Ok(effect),tail);
        part2_fused_run_lift(working,bands,precincts,placement,geometry,plane,reversible,maximum,prefix+tail);
    }
    assert(part2_tier1_storage_prefix(|calls|part2_extraction_place_run(working,bands,precincts,placement,reversible,maximum,calls),
        prefix,Ok((Err(crate::DecodeError::AllocationFailed),working))));
}
}
