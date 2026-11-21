//! Native fused reconstruction experiment: bounded direct placement has no staging owner.
//! Complete native/Verus qualification remains a separate adoption gate.
use super::*;
verus! {
pub(crate) open spec fn part2_narrow_magnitude(coefficient:Tier1RawCoefficient)->Option<u64> {
    if !coefficient.significant{Some(0u64)}
    else if coefficient.limbs.len()!=6 || exists|i:int|1<=i<6 && #[trigger] coefficient.limbs[i]!=0{None}
    else{match coefficient.legacy_bitplane{
        Some(bitplane)=>if bitplane>64{None}else{
            let value=coefficient.limbs[0] as int+part1_tier1_midpoint_delta(bitplane) as int;
            if value>u64::MAX{None}else{Some(value as u64)}
        },
        None=>Some(coefficient.limbs[0]),
    }}
}
pub(crate) open spec fn part2_fused_maximum(step:i64,reversible:bool)->u64 {
    if reversible || step==0{i64::MAX as u64}else{(((i64::MAX as int)/(step as int)-1)/2) as u64}
}
pub(crate) open spec fn part2_fused_step(geometry:crate::decode::SubbandGeometry,reversible:bool)->Result<i64,crate::DecodeError> {
    if reversible{Ok(1)}else{part1_quantization_step(geometry.quantization_step.exponent,geometry.quantization_step.mantissa,geometry.dynamic_range)}
}
pub(crate) open spec fn part2_fused_eligible(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,
    geometry:crate::decode::SubbandGeometry,x:u32,y:u32,reversible:bool,maximum:u64)->bool {
    let count=(plane.width as int)*(plane.height as int);
    let area=(destination.0 as int)*(destination.1 as int);
    let step=part2_fused_step(geometry,reversible);
    count>0 && count<=usize::MAX && count==plane.coefficients.len()
    && destination.0==geometry.width && destination.1==geometry.height
    && 1<=geometry.dynamic_range<=38 && geometry.quantization_step.exponent<=31 && geometry.quantization_step.mantissa<=2047
    && count*8<=maximum && area<=usize::MAX && destination.3.len()==area && destination.4.len()==area
    && x as int+plane.width as int<=geometry.width && y as int+plane.height as int<=geometry.height
    && step.is_ok() && step.get_Ok_0()>=0
    && forall|row:int,column:int|0<=row<plane.height && 0<=column<plane.width ==> {
        let coefficient=#[trigger] plane.coefficients[row*(plane.width as int)+column];
        let value=part2_narrow_magnitude(coefficient);
        value.is_some()
        && part1_maxshift_restore(value.get_Some_0(),geometry.roi_shift)<=part2_fused_maximum(step.get_Ok_0(),reversible)
        && !destination.4[(y as int+row)*(destination.0 as int)+x as int+column]
    }
}
pub(crate) open spec fn part2_fused_placement_enabled(working:Part1PrepareWorking,geometry:crate::decode::SubbandGeometry,
    placement:crate::decode::ProgressionCodeBlockPlacement,plane:Tier1RawPlane,reversible:bool,maximum:u64)->bool {
    placement.subband_index<working.0.len()
        && part2_fused_eligible(working.0[placement.subband_index as int],plane,geometry,placement.x,placement.y,reversible,maximum)
}
pub(crate) open spec fn part2_fused_place_run(working:Part1PrepareWorking,geometry:crate::decode::SubbandGeometry,
    placement:crate::decode::ProgressionCodeBlockPlacement,plane:Tier1RawPlane,reversible:bool,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2ExtractionWorkingEffect> {
    Some((Ok(part1_prepare_place_plane(working,geometry,placement,plane,reversible,maximum)),calls))
}
pub(crate) open spec fn part2_fused_band_value(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,
    geometry:crate::decode::SubbandGeometry,x:u32,y:u32,reversible:bool,maximum:u64)->(Result<(),crate::DecodeError>,Part1WorkingSubbandModel) {
    let placement=crate::decode::ProgressionCodeBlockPlacement{precinct_index:0,decoder_index:0,subband_index:0,x,y};
    let result=part1_prepare_place_plane((seq![destination],0u64),geometry,placement,plane,reversible,maximum);
    (result.0,result.1.0[0])
}
pub(crate) proof fn part2_fused_no_staging_owner(working:Part1PrepareWorking,geometry:crate::decode::SubbandGeometry,
    placement:crate::decode::ProgressionCodeBlockPlacement,plane:Tier1RawPlane,reversible:bool,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)
    ensures part2_fused_place_run(working,geometry,placement,plane,reversible,maximum,calls)
        ==Some((Ok(part1_prepare_place_plane(working,geometry,placement,plane,reversible,maximum)),calls)),
{}
}
