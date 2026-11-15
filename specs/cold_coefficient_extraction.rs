//! Fresh linear and coordinate-ordered signed-magnitude extraction owners.
use super::*;
verus! {
pub struct Part2CoefficientExtractionContext {pub width:u16,pub height:u16,pub coefficients:nat,pub coordinate:bool}
pub(crate) open spec fn part2_extraction_context(plane:Tier1RawPlane,coordinate:bool)->Part2CoefficientExtractionContext {
    Part2CoefficientExtractionContext {width:plane.width,height:plane.height,coefficients:plane.coefficients.len(),coordinate}
}
pub(crate) open spec fn part2_extraction_count(context:Part2CoefficientExtractionContext)->nat {
    if context.coordinate{context.width as nat*context.height as nat}else{context.coefficients}
}
#[verifier::opaque]
pub(crate) open spec fn part2_extraction_capacity_run(context:Part2CoefficientExtractionContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=part2_extraction_count(context);
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::CoefficientExtractionCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=count{None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) open spec fn part2_extraction_capacity_result(context:Part2CoefficientExtractionContext,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_extraction_capacity_run(context,calls),result)
}
pub(crate) proof fn part2_extraction_capacity_observed(context:Part2CoefficientExtractionContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_extraction_count(context)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_extraction_capacity_result(context,result),
{
    reveal(part2_extraction_capacity_run);
    let count=part2_extraction_count(context);
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::CoefficientExtractionCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_extraction_capacity_run(context,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_extraction_capacity_run(context,calls),prefix,result));
}
#[verifier::opaque]
pub(crate) open spec fn part2_linear_coefficients_prefix(coefficients:Seq<Tier1RawCoefficient>,count:nat)->Result<Seq<Part1QuantizedCoefficient>,crate::DecodeError>
    decreases count,
{
    if count==0{Ok(Seq::empty())}else{
        match part2_linear_coefficients_prefix(coefficients,(count-1) as nat){
            Err(error)=>Err(error),Ok(values)=>if count>coefficients.len(){Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}else{
                match tier1_raw_signed_coefficient(coefficients[count-1]){Err(error)=>Err(error),Ok(value)=>Ok(values.push((value.0,value.2)))}
            },
        }
    }
}
pub(crate) open spec fn part2_extraction_value(plane:Tier1RawPlane,coordinate:bool)->Result<Seq<Part1QuantizedCoefficient>,crate::DecodeError> {
    if coordinate{part1_prepare_collect_coefficients(plane)}else{part2_linear_coefficients_prefix(plane.coefficients,plane.coefficients.len())}
}
pub(crate) open spec fn part2_extraction_run(plane:Tier1RawPlane,coordinate:bool,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<Part1QuantizedCoefficient>> {
    if coordinate && plane.width as nat*plane.height as nat>usize::MAX{Some((part2_extraction_value(plane,coordinate),calls))}else{
        part2_tier1_storage_bind(part2_extraction_capacity_run(part2_extraction_context(plane,coordinate),calls),
            |_:(),rest|Some((part2_extraction_value(plane,coordinate),rest)))
    }
}
pub(crate) open spec fn part2_extraction_result(plane:Tier1RawPlane,coordinate:bool,result:Result<Seq<Part1QuantizedCoefficient>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_extraction_run(plane,coordinate,calls),result)
}
pub(crate) proof fn part2_extraction_normal(plane:Tier1RawPlane,coordinate:bool)
    ensures part2_extraction_result(plane,coordinate,part2_extraction_value(plane,coordinate)),
{
    let result=part2_extraction_value(plane,coordinate);
    part2_tier1_storage_pure(result);
    if !(coordinate && plane.width as nat*plane.height as nat>usize::MAX){
        let context=part2_extraction_context(plane,coordinate);
        part2_extraction_capacity_observed(context,Ok(()));
        part2_tier1_storage_bind_frame(|calls|part2_extraction_capacity_run(context,calls),|_:(),rest|Some((result,rest)),Ok(()),result);
    }
}
pub(crate) proof fn part2_extraction_refused(plane:Tier1RawPlane,coordinate:bool,error:crate::DecodeError)
    requires !(coordinate && plane.width as nat*plane.height as nat>usize::MAX),
        part2_extraction_capacity_result(part2_extraction_context(plane,coordinate),Err(error)),
    ensures part2_extraction_result(plane,coordinate,Err(error)),
{
    part2_tier1_storage_bind_frame(|calls|part2_extraction_capacity_run(part2_extraction_context(plane,coordinate),calls),
        |_:(),rest|Some((part2_extraction_value(plane,coordinate),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_linear_coefficients_error(coefficients:Seq<Tier1RawCoefficient>,prefix:nat,count:nat,error:crate::DecodeError)
    requires prefix<=count,part2_linear_coefficients_prefix(coefficients,prefix)==Err(error),
    ensures part2_linear_coefficients_prefix(coefficients,count)==Err(error),
    decreases count-prefix,
{
    if prefix<count{
        part2_linear_coefficients_error(coefficients,prefix,(count-1) as nat,error);
        reveal_with_fuel(part2_linear_coefficients_prefix,1);
    }
}
pub(crate) open spec fn part2_coefficient_collect_result(plane:Tier1RawPlane,result:Result<Seq<Part1QuantizedCoefficient>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_coefficient_collect_run(plane,calls),result)
}
pub(crate) open spec fn part2_coefficient_collect_run(plane:Tier1RawPlane,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<Part1QuantizedCoefficient>> {
    part2_extraction_run(plane,true,calls)
}
pub(crate) proof fn part2_coefficient_collect_normal(plane:Tier1RawPlane)
    ensures part2_coefficient_collect_result(plane,part1_prepare_collect_coefficients(plane)),
{part2_extraction_normal(plane,true);part2_tier1_storage_eta(|calls|part2_extraction_run(plane,true,calls),part1_prepare_collect_coefficients(plane));}
pub(crate) proof fn part2_coefficient_collect_frames(plane:Tier1RawPlane,result:Result<Seq<Part1QuantizedCoefficient>,crate::DecodeError>)
    requires part2_coefficient_collect_result(plane,result),
    ensures part2_extraction_result(plane,true,result),
{part2_tier1_storage_eta(|calls|part2_coefficient_collect_run(plane,calls),result);}
pub(crate) proof fn part2_coefficient_collect_observed(plane:Tier1RawPlane,result:Result<Seq<Part1QuantizedCoefficient>,crate::DecodeError>)
    requires part2_extraction_result(plane,true,result),
    ensures part2_coefficient_collect_result(plane,result),
{part2_tier1_storage_eta(|calls|part2_extraction_run(plane,true,calls),result);}
}
