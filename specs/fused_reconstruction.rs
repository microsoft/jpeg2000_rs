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
pub(crate) open spec fn part2_fused_shape(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,
    geometry:crate::decode::SubbandGeometry,x:u32,y:u32,reversible:bool,maximum:u64)->bool {
    let count=(plane.width as int)*(plane.height as int);
    let area=(destination.0 as int)*(destination.1 as int);
    let step=part2_fused_step(geometry,reversible);
    count>0 && count<=usize::MAX && count==plane.coefficients.len()
    && (forall|i:int|0<=i<plane.coefficients.len() ==> #[trigger] plane.coefficients[i].limbs.len()==6)
    && destination.0==geometry.width && destination.1==geometry.height
    && 1<=geometry.dynamic_range<=38 && geometry.quantization_step.exponent<=31 && geometry.quantization_step.mantissa<=2047
    && count*8<=maximum && area<=usize::MAX && destination.3.len()==area && destination.4.len()==area
    && x as int+plane.width as int<=geometry.width && y as int+plane.height as int<=geometry.height
    && step.is_ok() && step.get_Ok_0()>=0
}
pub(crate) open spec fn part2_fused_cell_valid(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,
    x:u32,y:u32,shift:u8,step:i64,reversible:bool,row:int,column:int)->bool {
        let coefficient=plane.coefficients[row*(plane.width as int)+column];
        let value=part2_narrow_magnitude(coefficient);
        value.is_some()
        && part1_maxshift_restore(value.get_Some_0(),shift)<=part2_fused_maximum(step,reversible)
        && !destination.4[(y as int+row)*(destination.0 as int)+x as int+column]
}
pub(crate) open spec fn part2_fused_eligible(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,
    geometry:crate::decode::SubbandGeometry,x:u32,y:u32,reversible:bool,maximum:u64)->bool {
    part2_fused_shape(destination,plane,geometry,x,y,reversible,maximum)
    && forall|row:int,column:int|0<=row<plane.height && 0<=column<plane.width ==>
        #[trigger] part2_fused_cell_valid(destination,plane,x,y,geometry.roi_shift,part2_fused_step(geometry,reversible).get_Ok_0(),reversible,row,column)
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
pub(crate) open spec fn part2_fused_sparse(value:u64)->Seq<u64>{
    Seq::new(6,|i:int|if i==0{value}else{0u64})
}
pub(crate) proof fn part2_fused_sparse_roi(value:u64,negative:bool,shift:u8)
    requires part1_maxshift_restore(value,shift)<=i64::MAX,
    ensures part1_roi_coefficient(part2_fused_sparse(value),negative,shift)
        ==Ok((if negative{-(part1_maxshift_restore(value,shift) as int)}else{part1_maxshift_restore(value,shift) as int}) as i64),
{
    let limbs=part2_fused_sparse(value);
    if value==0{
        assert(part1_magnitude_zero(limbs));
        if shift<64{assert(0u64<(1u64<<shift)) by(bit_vector) requires shift<64;}
    }else if shift==0{
        assert(value>>0u8==value) by(bit_vector);
    }else if shift>=64{
        let word=(shift/64) as int;
        let offset=(shift%64) as u32;
        let bit=1u64<<offset;
        assert(bit>0) by(bit_vector) requires offset<64,bit==1u64<<offset;
        assert(1<=word<6);
        assert(limbs[word]<part1_magnitude_bit(shift as u16)[word]);
        assert forall|j:int|word<j<6 implies limbs[j]==#[trigger] part1_magnitude_bit(shift as u16)[j] by{}
        assert(part1_magnitude_less(limbs,part1_magnitude_bit(shift as u16)));
    }else{
        let threshold=1u64<<shift;
        assert(part1_magnitude_bit(shift as u16) =~=part2_fused_sparse(threshold));
        assert(part1_magnitude_less(limbs,part1_magnitude_bit(shift as u16))==(value<threshold)) by{
            if value<threshold{
                assert(limbs[0]<part1_magnitude_bit(shift as u16)[0]);
            }else{
                assert forall|i:int|0<=i<6 implies !(limbs[i]<#[trigger] part1_magnitude_bit(shift as u16)[i]) by{}
            }
        }
        if value>=threshold{
            assert(part1_magnitude_shift(limbs,shift as u16) =~=part2_fused_sparse(value>>shift)) by{
                assert forall|i:int|0<=i<6 implies #[trigger] part1_magnitude_shift(limbs,shift as u16)[i]
                    ==part2_fused_sparse(value>>shift)[i] by{
                    if i==0{
                        assert((value>>shift)|(0u64<<((64-shift) as u32))==value>>shift) by(bit_vector)
                            requires 0<shift<64;
                    }else if i==5{
                        assert(0u64>>shift==0u64) by(bit_vector);
                    }else{
                        assert((0u64>>shift)|(0u64<<((64-shift) as u32))==0u64) by(bit_vector)
                            requires 0<shift<64;
                    }
                }
            }
        }
    }
}
pub(crate) proof fn part2_fused_sparse_value(value:u64)
    ensures part1_magnitude_value(part2_fused_sparse(value))==value as nat,
        tier1_value_limbs(value as nat)==part2_fused_sparse(value),
{
    reveal(vstd::arithmetic::power::pow);
    assert(pow2(0)==1);
    crate::proofs::production_impl::production_magnitude_sparse_prefix(part2_fused_sparse(value),0,value,6);
    vstd::arithmetic::mul::lemma_mul_basics(value as int);
    assert(part1_magnitude_value(part2_fused_sparse(value))==value as nat);
    crate::proofs::production_impl::production_tier1_value_limbs(part2_fused_sparse(value));
}
pub(crate) proof fn part2_fused_original_coefficient(coefficient:Tier1RawCoefficient,value:u64)
    requires coefficient.limbs.len()==6,part2_narrow_magnitude(coefficient)==Some(value),
    ensures tier1_raw_signed_coefficient(coefficient)==Ok((part2_fused_sparse(value),value as nat,coefficient.significant && coefficient.negative)),
{
    part2_fused_sparse_value(value);
    if coefficient.significant{
        assert(coefficient.limbs =~=part2_fused_sparse(coefficient.limbs[0]));
        part2_fused_sparse_value(coefficient.limbs[0]);
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(64,384);
    }else{
        assert(part2_fused_sparse(value) =~=Seq::new(6,|_:int|0u64));
    }
}
pub(crate) proof fn part2_fused_limit_bounds(value:u64,step:i64,reversible:bool)
    requires step>=0,value<=part2_fused_maximum(step,reversible),
    ensures value<=i64::MAX,
        !reversible && value>0 && step>0 ==> (2*(value as int)+1)*(step as int)<=i64::MAX,
{
    if !reversible && step>0{
        let quotient=(i64::MAX as int)/(step as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i64::MAX as int,step as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(i64::MAX as int,step as int);
        vstd::arithmetic::div_mod::lemma_div_by_self(step as int);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(step as int,i64::MAX as int,step as int);
        assert(quotient*(step as int)==(step as int)*quotient) by(nonlinear_arith);
        assert(1<=quotient<=i64::MAX) by(nonlinear_arith)
            requires quotient>=1,step>=1,quotient*(step as int)<=i64::MAX;
        assert((2*(value as int)+1)*(step as int)<=i64::MAX) by(nonlinear_arith)
            requires value as int<=(quotient-1)/2,step>0,quotient*(step as int)<=i64::MAX;
    }
}
pub(crate) open spec fn part2_fused_sample(coefficient:Tier1RawCoefficient,shift:u8,step:i64,reversible:bool)->i64 {
    let restored=part1_maxshift_restore(part2_narrow_magnitude(coefficient).get_Some_0(),shift);
    part1_dequantized_sample((if coefficient.significant && coefficient.negative{-(restored as int)}else{restored as int}) as i64,step,reversible).get_Ok_0()
}
pub(crate) proof fn part2_fused_sample_equivalent(coefficient:Tier1RawCoefficient,shift:u8,step:i64,reversible:bool)
    requires coefficient.limbs.len()==6,part2_narrow_magnitude(coefficient).is_some(),step>=0,
        part1_maxshift_restore(part2_narrow_magnitude(coefficient).get_Some_0(),shift)<=part2_fused_maximum(step,reversible),
    ensures tier1_raw_signed_coefficient(coefficient).is_ok(),
        part1_quantized_sample((tier1_raw_signed_coefficient(coefficient).get_Ok_0().0,
            tier1_raw_signed_coefficient(coefficient).get_Ok_0().2),shift,step,reversible)
            ==Ok(part2_fused_sample(coefficient,shift,step,reversible)),
        part1_dequantized_sample((if coefficient.significant && coefficient.negative{
            -(part1_maxshift_restore(part2_narrow_magnitude(coefficient).get_Some_0(),shift) as int)
        }else{part1_maxshift_restore(part2_narrow_magnitude(coefficient).get_Some_0(),shift) as int}) as i64,step,reversible).is_ok(),
{
    let value=part2_narrow_magnitude(coefficient).get_Some_0();
    let restored=part1_maxshift_restore(value,shift);
    part2_fused_original_coefficient(coefficient,value);
    part2_fused_limit_bounds(restored,step,reversible);
    part2_fused_sparse_roi(value,coefficient.significant && coefficient.negative,shift);
    if !reversible && restored>0{
        assert(0<=(2*(restored as int)+1)*(step as int)/2<=i64::MAX) by(nonlinear_arith)
            requires step>=0,(2*(restored as int)+1)*(step as int)<=i64::MAX;
    }
}
pub(crate) proof fn part2_fused_step_nonnegative(geometry:crate::decode::SubbandGeometry,reversible:bool)
    requires 1<=geometry.dynamic_range<=38,geometry.quantization_step.exponent<=31,geometry.quantization_step.mantissa<=2047,
    ensures part2_fused_step(geometry,reversible).is_ok(),part2_fused_step(geometry,reversible).get_Ok_0()>=0,
{
    if !reversible{
        let exponent=geometry.quantization_step.exponent;
        let range=geometry.dynamic_range;
        let base=((2048+geometry.quantization_step.mantissa as int)*65536/2048) as i64;
        assert(65536<=base<=131040);
        if range>=exponent{
            let shift=(range-exponent) as u8;
            let factor=1i64<<shift;
            assert(1<=factor<=274877906944) by(bit_vector)
                requires shift<=38,factor==1i64<<shift;
            assert(0<=(base as int)*(factor as int)<=i64::MAX) by(nonlinear_arith)
                requires 65536<=base<=131040,1<=factor<=274877906944;
        }else{
            let shift=(exponent-range) as u8;
            let divisor=1i64<<shift;
            assert(divisor>0) by(bit_vector) requires shift<=30,divisor==1i64<<shift;
            vstd::arithmetic::div_mod::lemma_div_is_ordered(0,base as int,divisor as int);
        }
    }
}
pub(crate) proof fn part2_fused_no_staging_owner(working:Part1PrepareWorking,geometry:crate::decode::SubbandGeometry,
    placement:crate::decode::ProgressionCodeBlockPlacement,plane:Tier1RawPlane,reversible:bool,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)
    ensures part2_fused_place_run(working,geometry,placement,plane,reversible,maximum,calls)
        ==Some((Ok(part1_prepare_place_plane(working,geometry,placement,plane,reversible,maximum)),calls)),
{}
}
