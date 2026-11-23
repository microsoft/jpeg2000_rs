//! Joining direct bounded samples to the original collection and quantization model.
use super::*;
verus! {
pub(crate) open spec fn part2_fused_plane_valid(plane:Tier1RawPlane,shift:u8,step:i64,reversible:bool)->bool {
    plane.width>0 && plane.height>0 && plane.coefficients.len()==(plane.width as int)*(plane.height as int)
    && plane.coefficients.len()<=usize::MAX && step>=0
    && forall|i:int|0<=i<plane.coefficients.len() ==> #[trigger] plane.coefficients[i].limbs.len()==6
        && part2_narrow_magnitude(plane.coefficients[i]).is_some()
        && part1_maxshift_restore(part2_narrow_magnitude(plane.coefficients[i]).get_Some_0(),shift)<=part2_fused_maximum(step,reversible)
}
pub(crate) proof fn part2_fused_admit_plane(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,x:u32,y:u32,shift:u8,step:i64,reversible:bool)
    requires part2_fused_write_admit(destination,plane,x,y,shift,step,reversible),
    ensures part2_fused_plane_valid(plane,shift,step,reversible),
{
    part2_fused_geometry(destination,plane,x,y,shift,step,reversible);
    assert forall|i:int|0<=i<plane.coefficients.len() implies #[trigger] plane.coefficients[i].limbs.len()==6
        && part2_narrow_magnitude(plane.coefficients[i]).is_some()
        && part1_maxshift_restore(part2_narrow_magnitude(plane.coefficients[i]).get_Some_0(),shift)<=part2_fused_maximum(step,reversible) by{
        part2_fused_coordinates(i,plane.width as int,plane.height as int);
        assert(part2_fused_cell_valid(destination,plane,x,y,shift,step,reversible,i/(plane.width as int),i%(plane.width as int)));
    }
}
pub(crate) open spec fn part2_fused_coefficients(plane:Tier1RawPlane)->Seq<Part1QuantizedCoefficient>{
    Seq::new(plane.coefficients.len(),|i:int|{
        let value=tier1_raw_signed_coefficient(plane.coefficients[i]).get_Ok_0();(value.0,value.2)
    })
}
pub(crate) proof fn part2_fused_collect_row(plane:Tier1RawPlane,shift:u8,step:i64,reversible:bool,row:u16,count:nat)
    requires part2_fused_plane_valid(plane,shift,step,reversible),row<plane.height,count<=plane.width,
    ensures part1_prepare_coefficient_row(plane,row,part2_fused_coefficients(plane).take((row as int)*(plane.width as int)),count)
        ==Ok(part2_fused_coefficients(plane).take((row as int)*(plane.width as int)+count)),
    decreases count,
{
    reveal(part1_prepare_coefficient_row);
    let values=part2_fused_coefficients(plane);
    let start=(row as int)*(plane.width as int);
    if count>0{
        part2_fused_collect_row(plane,shift,step,reversible,row,(count-1) as nat);
        assert(0<=start+count-1<plane.coefficients.len()) by(nonlinear_arith)
            requires start==(row as int)*(plane.width as int),0<count<=plane.width,row<plane.height,
                plane.coefficients.len()==(plane.width as int)*(plane.height as int);
        part2_fused_original_coefficient(plane.coefficients[start+count-1],part2_narrow_magnitude(plane.coefficients[start+count-1]).get_Some_0());
        assert(part1_prepare_signed_cell(plane,(count-1) as u16,row)==Ok(values[start+count-1]));
        assert(values.take(start+count-1).push(values[start+count-1]) =~=values.take(start+count));
    }
}
pub(crate) proof fn part2_fused_collect_rows(plane:Tier1RawPlane,shift:u8,step:i64,reversible:bool,count:nat)
    requires part2_fused_plane_valid(plane,shift,step,reversible),count<=plane.height,
    ensures part1_prepare_coefficient_rows(plane,count)==Ok(part2_fused_coefficients(plane).take(count*(plane.width as int))),
    decreases count,
{
    reveal(part1_prepare_coefficient_rows);
    if count>0{
        part2_fused_collect_rows(plane,shift,step,reversible,(count-1) as nat);
        part2_fused_collect_row(plane,shift,step,reversible,(count-1) as u16,plane.width as nat);
        assert((count-1)*(plane.width as int)+plane.width==count*(plane.width as int)) by(nonlinear_arith);
    }else{assert(Seq::<Part1QuantizedCoefficient>::empty() =~=part2_fused_coefficients(plane).take(0));}
}
pub(crate) proof fn part2_fused_quantized_prefix(plane:Tier1RawPlane,shift:u8,step:i64,reversible:bool,count:nat)
    requires part2_fused_plane_valid(plane,shift,step,reversible),count<=plane.coefficients.len(),
    ensures part1_quantized_prefix(part2_fused_coefficients(plane),shift,step,reversible,count)==Ok(part2_fused_values(plane,shift,step,reversible).take(count as int)),
    decreases count,
{
    if count>0{
        part2_fused_quantized_prefix(plane,shift,step,reversible,(count-1) as nat);
        part2_fused_sample_equivalent(plane.coefficients[count-1],shift,step,reversible);
        let values=part2_fused_values(plane,shift,step,reversible);
        assert(values.take(count-1).push(values[count-1]) =~=values.take(count as int));
    }else{assert(Seq::<i64>::empty() =~=part2_fused_values(plane,shift,step,reversible).take(0));}
}
pub(crate) proof fn part2_fused_band_equivalent(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,
    geometry:crate::decode::SubbandGeometry,x:u32,y:u32,reversible:bool,maximum:u64)
    requires part2_fused_eligible(destination,plane,geometry,x,y,reversible,maximum),
    ensures part2_fused_band_value(destination,plane,geometry,x,y,reversible,maximum)==(Ok(()),
        part2_fused_rows(destination,part2_fused_values(plane,geometry.roi_shift,part2_fused_step(geometry,reversible).get_Ok_0(),reversible),plane.width as u32,x,y,plane.height as nat)),
{
    let step=part2_fused_step(geometry,reversible).get_Ok_0();
    assert(part2_fused_write_admit(destination,plane,x,y,geometry.roi_shift,step,reversible));
    part2_fused_admit_plane(destination,plane,x,y,geometry.roi_shift,step,reversible);
    part2_fused_collect_rows(plane,geometry.roi_shift,step,reversible,plane.height as nat);
    let coefficients=part2_fused_coefficients(plane);
    assert(coefficients.take((plane.height as int)*(plane.width as int)) =~=coefficients);
    assert(part1_prepare_collect_coefficients(plane)==Ok(coefficients));
    part2_fused_quantized_prefix(plane,geometry.roi_shift,step,reversible,plane.coefficients.len());
    let values=part2_fused_values(plane,geometry.roi_shift,step,reversible);
    assert(values.take(values.len() as int) =~=values);
    assert(plane.coefficients.len()<=u32::MAX) by(nonlinear_arith)
        requires plane.coefficients.len()==(plane.width as int)*(plane.height as int),0<=plane.width<=u16::MAX,0<=plane.height<=u16::MAX;
    assert(part1_inverse_quantization(coefficients,geometry.quantization_step.exponent,geometry.quantization_step.mantissa,
        geometry.dynamic_range,reversible,geometry.roi_shift,maximum)==Ok((coefficients.len() as u32,1u32,if reversible{0u8}else{16u8},values)));
    part2_fused_rows_scalar(destination,plane,x,y,geometry.roi_shift,step,reversible,plane.height as nat);
}
}
