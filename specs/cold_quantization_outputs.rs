//! Actual wide, quantized-sample and final code-block-copy owners.
use super::*;
verus! {
pub enum Part2QuantizationOwner {Wide, Samples, CodeBlockCopy, ConvertedSamples}
#[verifier::opaque]
pub(crate) open spec fn part2_quantization_capacity_run(owner:Part2QuantizationOwner,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::QuantizationCapacity {owner:actual,elements,succeeded}=>
            if actual!=owner || elements!=count{None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) open spec fn part2_quantization_capacity_result(owner:Part2QuantizationOwner,count:nat,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_quantization_capacity_run(owner,count,calls),result)
}
pub(crate) proof fn part2_quantization_capacity_observed(owner:Part2QuantizationOwner,count:nat,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (count>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_quantization_capacity_result(owner,count,result),
{
    reveal(part2_quantization_capacity_run);
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::QuantizationCapacity {owner,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_quantization_capacity_run(owner,count,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_quantization_capacity_run(owner,count,calls),prefix,result));
}
pub(crate) open spec fn part2_convert_samples_storage_admitted(plane:Part1ReconstructedPlane,precision:u8,maximum:u64)->bool {
    precision>0 && precision<=38 && plane.2<=62 && part1_quantization_budget(plane.3.len(),maximum).is_ok()
}
pub(crate) open spec fn part2_convert_samples_storage_run(plane:Part1ReconstructedPlane,precision:u8,signed:bool,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    let value=part1_convert_samples(plane,precision,signed,maximum);
    if !part2_convert_samples_storage_admitted(plane,precision,maximum){Some((value,calls))}else{
        part2_tier1_storage_bind(part2_quantization_capacity_run(Part2QuantizationOwner::ConvertedSamples,plane.3.len(),calls),
            |_:(),rest|Some((value,rest)))
    }
}
pub closed spec fn part2_convert_samples_storage_result(plane:Part1ReconstructedPlane,precision:u8,signed:bool,maximum:u64,
    result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_convert_samples_storage_run(plane,precision,signed,maximum,calls),result)
}
pub(crate) proof fn part2_convert_samples_storage_normal(plane:Part1ReconstructedPlane,precision:u8,signed:bool,maximum:u64)
    ensures part2_convert_samples_storage_result(plane,precision,signed,maximum,part1_convert_samples(plane,precision,signed,maximum)),
{
    reveal(part2_convert_samples_storage_result);
    let value=part1_convert_samples(plane,precision,signed,maximum);
    part2_tier1_storage_pure(value);
    if part2_convert_samples_storage_admitted(plane,precision,maximum) {
        part2_quantization_capacity_observed(Part2QuantizationOwner::ConvertedSamples,plane.3.len(),Ok(()));
        part2_tier1_storage_bind_frame(|calls|part2_quantization_capacity_run(Part2QuantizationOwner::ConvertedSamples,plane.3.len(),calls),
            |_:(),rest|Some((value,rest)),Ok(()),value);
    }
}
pub(crate) proof fn part2_convert_samples_storage_refused(plane:Part1ReconstructedPlane,precision:u8,signed:bool,maximum:u64,error:crate::DecodeError)
    requires part2_convert_samples_storage_admitted(plane,precision,maximum),
        part2_quantization_capacity_result(Part2QuantizationOwner::ConvertedSamples,plane.3.len(),Err(error)),
    ensures part2_convert_samples_storage_result(plane,precision,signed,maximum,Err(error)),
{
    reveal(part2_convert_samples_storage_result);
    part2_tier1_storage_bind_frame(|calls|part2_quantization_capacity_run(Part2QuantizationOwner::ConvertedSamples,plane.3.len(),calls),
        |_:(),rest|Some((part1_convert_samples(plane,precision,signed,maximum),rest)),Err(error),Err(error));
}
pub(crate) open spec fn part2_quantization_admit(count:nat,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,maximum:u64)->Result<i64,crate::DecodeError> {
    if dynamic_range==0 || dynamic_range>38 || mantissa>2047{Err(part1_transform_error(false))}
    else if exponent>31{Err(part1_transform_error(false))}
    else{match part1_quantization_budget(count,maximum){
        Err(error)=>Err(error),Ok(())=>if reversible{Ok(1i64)}else{part1_quantization_step(exponent,mantissa,dynamic_range)},
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_quantization_plane_run(coefficients:Seq<Part1QuantizedCoefficient>,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,shift:u8,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane> {
    match part2_quantization_admit(coefficients.len(),exponent,mantissa,dynamic_range,reversible,maximum){
        Err(error)=>Some((Err(error),calls)),Ok(_)=>part2_tier1_storage_bind(part2_quantization_capacity_run(Part2QuantizationOwner::Samples,coefficients.len(),calls),
            |_:(),rest|Some((part1_inverse_quantization(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum),rest))),
    }
}
pub closed spec fn part2_quantization_plane_result(coefficients:Seq<Part1QuantizedCoefficient>,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,shift:u8,maximum:u64,
    result:Part1ReconstructionResult)->bool {
    part2_tier1_storage_framed(|calls|part2_quantization_plane_run(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,calls),result)
}
pub(crate) proof fn part2_quantization_plane_normal(coefficients:Seq<Part1QuantizedCoefficient>,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,shift:u8,maximum:u64)
    ensures part2_quantization_plane_result(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,
        part1_inverse_quantization(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum)),
{
    reveal(part2_quantization_plane_result);reveal(part2_quantization_plane_run);
    let result=part1_inverse_quantization(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum);
    match part2_quantization_admit(coefficients.len(),exponent,mantissa,dynamic_range,reversible,maximum){
        Err(_)=>{part2_tier1_storage_pure(result);},Ok(_)=>{
            part2_quantization_capacity_observed(Part2QuantizationOwner::Samples,coefficients.len(),Ok(()));
            part2_tier1_storage_pure(result);
            part2_tier1_storage_bind_frame(|calls|part2_quantization_capacity_run(Part2QuantizationOwner::Samples,coefficients.len(),calls),
                |_:(),rest|Some((result,rest)),Ok(()),result);
        },
    }
}
pub(crate) proof fn part2_quantization_plane_refused(coefficients:Seq<Part1QuantizedCoefficient>,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,shift:u8,maximum:u64,error:crate::DecodeError)
    requires part2_quantization_admit(coefficients.len(),exponent,mantissa,dynamic_range,reversible,maximum).is_ok(),
        part2_quantization_capacity_result(Part2QuantizationOwner::Samples,coefficients.len(),Err(error)),
    ensures part2_quantization_plane_result(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,Err(error)),
{
    reveal(part2_quantization_plane_result);reveal(part2_quantization_plane_run);
    part2_tier1_storage_bind_frame(|calls|part2_quantization_capacity_run(Part2QuantizationOwner::Samples,coefficients.len(),calls),
        |_:(),rest|Some((part1_inverse_quantization(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_quantization_plane_frames(coefficients:Seq<Part1QuantizedCoefficient>,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,shift:u8,maximum:u64,result:Part1ReconstructionResult)
    requires part2_quantization_plane_result(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,result),
    ensures part2_tier1_storage_framed(|calls|part2_quantization_plane_run(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane>|
            (forall|calls| #[trigger] other(calls)==part2_quantization_plane_run(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{
    reveal(part2_quantization_plane_result);part2_tier1_storage_eta(|calls|part2_quantization_plane_run(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,calls),result);
}
pub(crate) open spec fn part2_integer_quantization_after_wide(coefficients:Seq<i64>,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,shift:u8,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane> {
    if exists|i:int|0<=i<coefficients.len() && coefficients[i]==i64::MIN{Some((Err(part1_transform_error(true)),calls))}
    else{part2_quantization_plane_run(part1_integer_coefficients(coefficients),exponent,mantissa,dynamic_range,reversible,shift,maximum,calls)}
}
#[verifier::opaque]
pub(crate) open spec fn part2_integer_quantization_run(coefficients:Seq<i64>,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,shift:u8,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane> {
    part2_tier1_storage_bind(part2_quantization_capacity_run(Part2QuantizationOwner::Wide,coefficients.len(),calls),
        |_:(),rest|part2_integer_quantization_after_wide(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,rest))
}
pub closed spec fn part2_integer_quantization_result(coefficients:Seq<i64>,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,shift:u8,maximum:u64,result:Part1ReconstructionResult)->bool {
    part2_tier1_storage_framed(|calls|part2_integer_quantization_run(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,calls),result)
}
pub(crate) proof fn part2_integer_quantization_normal(coefficients:Seq<i64>,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,shift:u8,maximum:u64)
    ensures part2_integer_quantization_result(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,
        part1_inverse_integer_quantization(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum)),
{
    reveal(part2_integer_quantization_result);reveal(part2_integer_quantization_run);
    let result=part1_inverse_integer_quantization(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum);
    part2_quantization_capacity_observed(Part2QuantizationOwner::Wide,coefficients.len(),Ok(()));
    if exists|i:int|0<=i<coefficients.len() && coefficients[i]==i64::MIN{part2_tier1_storage_pure(result);}
    else{
        part2_quantization_plane_normal(part1_integer_coefficients(coefficients),exponent,mantissa,dynamic_range,reversible,shift,maximum);
        part2_quantization_plane_frames(part1_integer_coefficients(coefficients),exponent,mantissa,dynamic_range,reversible,shift,maximum,result);
    }
    part2_tier1_storage_bind_frame(|calls|part2_quantization_capacity_run(Part2QuantizationOwner::Wide,coefficients.len(),calls),
        |_:(),rest|part2_integer_quantization_after_wide(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,rest),Ok(()),result);
}
pub(crate) proof fn part2_integer_quantization_refused(coefficients:Seq<i64>,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,shift:u8,maximum:u64,error:crate::DecodeError)
    requires part2_quantization_capacity_result(Part2QuantizationOwner::Wide,coefficients.len(),Err(error)),
    ensures part2_integer_quantization_result(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,Err(error)),
{
    reveal(part2_integer_quantization_result);reveal(part2_integer_quantization_run);
    part2_tier1_storage_bind_frame(|calls|part2_quantization_capacity_run(Part2QuantizationOwner::Wide,coefficients.len(),calls),
        |_:(),rest|part2_integer_quantization_after_wide(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_integer_quantization_child_observed(coefficients:Seq<i64>,exponent:u8,mantissa:u16,dynamic_range:u8,reversible:bool,shift:u8,maximum:u64,result:Part1ReconstructionResult)
    requires forall|i:int|0<=i<coefficients.len() ==> coefficients[i]!=i64::MIN,
        part2_quantization_plane_result(part1_integer_coefficients(coefficients),exponent,mantissa,dynamic_range,reversible,shift,maximum,result),
    ensures part2_integer_quantization_result(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,result),
{
    reveal(part2_integer_quantization_result);reveal(part2_integer_quantization_run);
    part2_quantization_capacity_observed(Part2QuantizationOwner::Wide,coefficients.len(),Ok(()));
    part2_quantization_plane_frames(part1_integer_coefficients(coefficients),exponent,mantissa,dynamic_range,reversible,shift,maximum,result);
    part2_tier1_storage_bind_frame(|calls|part2_quantization_capacity_run(Part2QuantizationOwner::Wide,coefficients.len(),calls),
        |_:(),rest|part2_integer_quantization_after_wide(coefficients,exponent,mantissa,dynamic_range,reversible,shift,maximum,rest),Ok(()),result);
}
#[verifier::opaque]
pub(crate) open spec fn part2_quantized_samples_copy_run(source:Seq<i64>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_quantization_capacity_run(Part2QuantizationOwner::CodeBlockCopy,source.len(),calls),
        |_:(),rest|Some((Ok(source),rest)))
}
pub(crate) open spec fn part2_quantized_samples_copy_result(source:Seq<i64>,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_quantized_samples_copy_run(source,calls),result)
}
pub(crate) proof fn part2_quantized_samples_copy_observed(source:Seq<i64>,result:Result<(),crate::DecodeError>)
    requires part2_quantization_capacity_result(Part2QuantizationOwner::CodeBlockCopy,source.len(),result),
    ensures part2_quantized_samples_copy_result(source,match result{Err(error)=>Err(error),Ok(())=>Ok(source)}),
{
    reveal(part2_quantized_samples_copy_run);
    let copied=match result{Err(error)=>Err(error),Ok(())=>Ok(source)};
    if result.is_ok(){part2_tier1_storage_pure(copied);}
    part2_tier1_storage_bind_frame(|calls|part2_quantization_capacity_run(Part2QuantizationOwner::CodeBlockCopy,source.len(),calls),
        |_:(),rest|Some((Ok(source),rest)),result,copied);
}
}
