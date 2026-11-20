//! Fresh horizontal assembly and zero-filled vertical sample planes.
use super::*;
verus! {
pub enum Part2WaveletPlaneOwner {Rows, Columns}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_capacity_run(owner:Part2WaveletPlaneOwner,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::WaveletPlaneCapacity {owner:actual,elements,succeeded}=>
            if actual!=owner || elements!=count{None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) open spec fn part2_wavelet_capacity_result(owner:Part2WaveletPlaneOwner,count:nat,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_capacity_run(owner,count,calls),result)
}
pub(crate) proof fn part2_wavelet_capacity_observed(owner:Part2WaveletPlaneOwner,count:nat,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (count>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_wavelet_capacity_result(owner,count,result),
{
    reveal(part2_wavelet_capacity_run);
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::WaveletPlaneCapacity {owner,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_wavelet_capacity_run(owner,count,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_wavelet_capacity_run(owner,count,calls),prefix,result));
}
pub(crate) open spec fn part2_wavelet_rows_value(low:Part1WaveletBand,high:Part1WaveletBand,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>)->Result<Seq<i64>,crate::DecodeError> {
    match kernel{None=>part1_horizontal_prefix(low,high,first,irreversible,low.1 as nat),
        Some(kernel)=>part2_atk_horizontal_prefix(low,high,first,kernel,low.1 as nat)}
}
pub(crate) open spec fn part2_wavelet_columns_value(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize)->Result<Seq<i64>,crate::DecodeError> {
    match kernel{None=>part1_vertical_prefix(low,high,height,first,irreversible,length,low.0 as nat),
        Some(kernel)=>part2_atk_vertical_prefix(low,high,height,first,kernel,length,low.0 as nat)}
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_rows_run(low:Part1WaveletBand,high:Part1WaveletBand,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,capacity:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Rows,capacity as nat,calls),
        |_:(),rest|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,low.1 as nat,rest))
}
pub(crate) open spec fn part2_wavelet_rows_result(low:Part1WaveletBand,high:Part1WaveletBand,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,capacity:usize,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_rows_run(low,high,first,irreversible,kernel,capacity,calls),result)
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_scalar_columns_run(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Columns,length as nat,calls),
        |_:(),rest|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,low.0 as nat,rest))
}
pub(crate) open spec fn part2_wavelet_scalar_columns_result(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_scalar_columns_run(low,high,height,first,irreversible,kernel,length,calls),result)
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_columns_run(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    if !irreversible && kernel.is_none() && rowwise_eligible(low,high,height,first,length) {
        rowwise_run(low,high,height,first,length,calls)
    }else if irreversible && kernel.is_none() && height>1 && rowwise_eligible(low,high,height,first,length){
        rowwise_fixed_run(low,high,height,first,length,calls)
    }else{
        part2_wavelet_scalar_columns_run(low,high,height,first,irreversible,kernel,length,calls)
    }
}
pub(crate) open spec fn part2_wavelet_columns_result(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_columns_run(low,high,height,first,irreversible,kernel,length,calls),result)
}
pub(crate) proof fn part2_wavelet_rows_normal(low:Part1WaveletBand,high:Part1WaveletBand,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,capacity:usize)
    ensures part2_wavelet_rows_result(low,high,first,irreversible,kernel,capacity,part2_wavelet_rows_value(low,high,first,irreversible,kernel)),
{
    reveal(part2_wavelet_rows_run);let result=part2_wavelet_rows_value(low,high,first,irreversible,kernel);
    part2_wavelet_capacity_observed(Part2WaveletPlaneOwner::Rows,capacity as nat,Ok(()));
    part2_wavelet_horizontal_lines_normal(low,high,first,irreversible,kernel,low.1 as nat);
    part2_tier1_storage_eta(|calls|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,low.1 as nat,calls),result);
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Rows,capacity as nat,calls),
        |_:(),rest|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,low.1 as nat,rest),Ok(()),result);
}
pub(crate) proof fn part2_wavelet_scalar_columns_normal(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize)
    ensures part2_wavelet_scalar_columns_result(low,high,height,first,irreversible,kernel,length,part2_wavelet_columns_value(low,high,height,first,irreversible,kernel,length)),
{
    reveal(part2_wavelet_scalar_columns_run);let result=part2_wavelet_columns_value(low,high,height,first,irreversible,kernel,length);
    part2_wavelet_capacity_observed(Part2WaveletPlaneOwner::Columns,length as nat,Ok(()));
    part2_wavelet_vertical_lines_normal(low,high,height,first,irreversible,kernel,length,low.0 as nat);
    part2_tier1_storage_eta(|calls|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,low.0 as nat,calls),result);
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Columns,length as nat,calls),
        |_:(),rest|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,low.0 as nat,rest),Ok(()),result);
}
pub(crate) proof fn part2_wavelet_columns_observed(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,result:Result<Seq<i64>,crate::DecodeError>)
    requires if !irreversible && kernel.is_none() && rowwise_eligible(low,high,height,first,length) {
        rowwise_result(low,high,height,first,length,result)
    }else if irreversible && kernel.is_none() && height>1 && rowwise_eligible(low,high,height,first,length){
        rowwise_fixed_result(low,high,height,first,length,result)
    }else{part2_wavelet_scalar_columns_result(low,high,height,first,irreversible,kernel,length,result)},
    ensures part2_wavelet_columns_result(low,high,height,first,irreversible,kernel,length,result),
{
    reveal(part2_wavelet_columns_run);
    if !irreversible && kernel.is_none() && rowwise_eligible(low,high,height,first,length) {
        part2_tier1_storage_eta(|calls|rowwise_run(low,high,height,first,length,calls),result);
    }else if irreversible && kernel.is_none() && height>1 && rowwise_eligible(low,high,height,first,length){
        part2_tier1_storage_eta(|calls|rowwise_fixed_run(low,high,height,first,length,calls),result);
    }else{
        part2_tier1_storage_eta(|calls|part2_wavelet_scalar_columns_run(low,high,height,first,irreversible,kernel,length,calls),result);
    }
}
pub(crate) proof fn part2_wavelet_columns_normal(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize)
    ensures part2_wavelet_columns_result(low,high,height,first,irreversible,kernel,length,part2_wavelet_columns_value(low,high,height,first,irreversible,kernel,length)),
{
    if !irreversible && kernel.is_none() && rowwise_eligible(low,high,height,first,length) {
        rowwise_equivalent(low,high,height,first,length);
        part2_wavelet_capacity_observed(Part2WaveletPlaneOwner::Columns,length as nat,Ok(()));
        rowwise_observed(low,high,height,first,length,Ok(()));
    }else if irreversible && kernel.is_none() && height>1 && rowwise_eligible(low,high,height,first,length){
        rowwise_fixed_equivalent(low,high,height,first,length);
        part2_wavelet_capacity_observed(Part2WaveletPlaneOwner::Columns,length as nat,Ok(()));
        rowwise_fixed_observed(low,high,height,first,length,Ok(()));
    }else{part2_wavelet_scalar_columns_normal(low,high,height,first,irreversible,kernel,length);}
    part2_wavelet_columns_observed(low,high,height,first,irreversible,kernel,length,part2_wavelet_columns_value(low,high,height,first,irreversible,kernel,length));
}
pub(crate) proof fn part2_wavelet_rows_refused(low:Part1WaveletBand,high:Part1WaveletBand,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,capacity:usize,error:crate::DecodeError)
    requires part2_wavelet_capacity_result(Part2WaveletPlaneOwner::Rows,capacity as nat,Err(error)),
    ensures part2_wavelet_rows_result(low,high,first,irreversible,kernel,capacity,Err(error)),
{
    reveal(part2_wavelet_rows_run);
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Rows,capacity as nat,calls),
        |_:(),rest|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,low.1 as nat,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_wavelet_scalar_columns_refused(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,error:crate::DecodeError)
    requires part2_wavelet_capacity_result(Part2WaveletPlaneOwner::Columns,length as nat,Err(error)),
    ensures part2_wavelet_scalar_columns_result(low,high,height,first,irreversible,kernel,length,Err(error)),
{
    reveal(part2_wavelet_scalar_columns_run);
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Columns,length as nat,calls),
        |_:(),rest|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,low.0 as nat,rest),Err(error),Err(error));
}
pub(crate) open spec fn part2_wavelet_horizontal_admit(low:Part1WaveletBand,high:Part1WaveletBand,width:u32,first:bool,maximum:u64)->Result<usize,crate::DecodeError> {
    match part1_horizontal_geometry(low,high,width,first){Err(error)=>Err(error),Ok(())=>match part1_transform_area(width,low.1){
        Err(error)=>Err(error),Ok(length)=>match part1_quantization_budget(length as nat,maximum){Err(error)=>Err(error),Ok(())=>Ok(length)},
    }}
}
pub(crate) open spec fn part2_wavelet_vertical_admit(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,maximum:u64)->Result<usize,crate::DecodeError> {
    match part1_vertical_geometry(low,high,height,first){Err(error)=>Err(error),Ok(())=>match part1_transform_area(low.0,height){
        Err(error)=>Err(error),Ok(length)=>match part1_quantization_budget(length as nat,maximum){Err(error)=>Err(error),Ok(())=>Ok(length)},
    }}
}
pub(crate) open spec fn part2_wavelet_level_admit(level:Part1WaveletLevel,maximum:u64)->Result<usize,crate::DecodeError> {
    match part1_validate_level(level){Err(error)=>Err(error),Ok(())=>match part1_transform_area(level.4,level.5){
        Err(error)=>Err(error),Ok(length)=>if !part1_wavelet_sample_count(level.4,level.5,length){Err(part1_transform_error(false))}
        else{match part1_quantization_budget(length as nat,maximum){Err(error)=>Err(error),Ok(())=>Ok(length)}},
    }}
}
pub(crate) open spec fn part2_wavelet_wrap(width:u32,height:u32,irreversible:bool,samples:Seq<i64>)->Part1ReconstructedPlane {
    (width,height,if irreversible{16u8}else{0u8},samples)
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_horizontal_run(low:Part1WaveletBand,high:Part1WaveletBand,width:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane> {
    match part2_wavelet_horizontal_admit(low,high,width,first,maximum){
        Err(error)=>Some((Err(error),calls)),Ok(capacity)=>part2_tier1_storage_bind(part2_wavelet_rows_run(low,high,first,irreversible,kernel,capacity,calls),
            |samples:Seq<i64>,rest|Some((Ok(part2_wavelet_wrap(width,low.1,irreversible,samples)),rest))),
    }
}
pub closed spec fn part2_wavelet_horizontal_result(low:Part1WaveletBand,high:Part1WaveletBand,width:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,result:Part1ReconstructionResult)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_horizontal_run(low,high,width,first,irreversible,kernel,maximum,calls),result)
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_vertical_run(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane> {
    match part2_wavelet_vertical_admit(low,high,height,first,maximum){
        Err(error)=>Some((Err(error),calls)),Ok(length)=>part2_tier1_storage_bind(part2_wavelet_columns_run(low,high,height,first,irreversible,kernel,length,calls),
            |samples:Seq<i64>,rest|Some((Ok(part2_wavelet_wrap(low.0,height,irreversible,samples)),rest))),
    }
}
pub closed spec fn part2_wavelet_vertical_result(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,result:Part1ReconstructionResult)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_vertical_run(low,high,height,first,irreversible,kernel,maximum,calls),result)
}
pub(crate) open spec fn part2_wavelet_level_after_low(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,low:Seq<i64>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane> {
    match part1_transform_area(level.4,level.2.1){
        Err(error)=>Some((Err(error),calls)),Ok(capacity)=>part2_tier1_storage_bind(part2_wavelet_rows_run(level.2,level.3,level.6,irreversible,kernel,capacity,calls),
            |high:Seq<i64>,rest|part2_wavelet_level_after_high(level,irreversible,kernel,length,low,high,rest)),
    }
}
pub(crate) open spec fn part2_wavelet_level_after_high(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,low:Seq<i64>,high:Seq<i64>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane> {
    part2_tier1_storage_bind(part2_wavelet_columns_run((level.4,level.0.1,low),(level.4,level.2.1,high),level.5,level.7,irreversible,kernel,length,calls),
        |samples:Seq<i64>,rest|Some((Ok(part2_wavelet_wrap(level.4,level.5,irreversible,samples)),rest)))
}
pub(crate) open spec fn part2_wavelet_level_rows_run(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane> {
    match part1_transform_area(level.4,level.0.1){
        Err(error)=>Some((Err(error),calls)),Ok(capacity)=>part2_tier1_storage_bind(part2_wavelet_rows_run(level.0,level.1,level.6,irreversible,kernel,capacity,calls),
            |low:Seq<i64>,rest|part2_wavelet_level_after_low(level,irreversible,kernel,length,low,rest)),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_level_run(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane> {
    match part2_wavelet_level_admit(level,maximum){Err(error)=>Some((Err(error),calls)),Ok(length)=>part2_wavelet_level_rows_run(level,irreversible,kernel,length,calls)}
}
pub closed spec fn part2_wavelet_level_result(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,result:Part1ReconstructionResult)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_level_run(level,irreversible,kernel,maximum,calls),result)
}
pub(crate) open spec fn part2_wavelet_horizontal_value(low:Part1WaveletBand,high:Part1WaveletBand,width:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64)->Part1ReconstructionResult {
    match kernel{None=>part1_inverse_horizontal(low,high,width,first,irreversible,maximum),Some(kernel)=>part2_atk_inverse_horizontal(low,high,width,first,irreversible,kernel,maximum)}
}
pub(crate) open spec fn part2_wavelet_vertical_value(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64)->Part1ReconstructionResult {
    match kernel{None=>part1_inverse_vertical(low,high,height,first,irreversible,maximum),Some(kernel)=>part2_atk_inverse_vertical(low,high,height,first,irreversible,kernel,maximum)}
}
pub(crate) open spec fn part2_wavelet_level_value(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64)->Part1ReconstructionResult {
    match kernel{None=>part1_inverse_level(level,irreversible,maximum),Some(kernel)=>part2_atk_inverse_level(level,irreversible,kernel,maximum)}
}
pub(crate) proof fn part2_wavelet_rows_frames(low:Part1WaveletBand,high:Part1WaveletBand,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,capacity:usize,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_wavelet_rows_result(low,high,first,irreversible,kernel,capacity,result),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_rows_run(low,high,first,irreversible,kernel,capacity,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>>|
            (forall|calls| #[trigger] other(calls)==part2_wavelet_rows_run(low,high,first,irreversible,kernel,capacity,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{part2_tier1_storage_eta(|calls|part2_wavelet_rows_run(low,high,first,irreversible,kernel,capacity,calls),result);}
pub(crate) proof fn part2_wavelet_columns_frames(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_wavelet_columns_result(low,high,height,first,irreversible,kernel,length,result),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_columns_run(low,high,height,first,irreversible,kernel,length,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>>|
            (forall|calls| #[trigger] other(calls)==part2_wavelet_columns_run(low,high,height,first,irreversible,kernel,length,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{part2_tier1_storage_eta(|calls|part2_wavelet_columns_run(low,high,height,first,irreversible,kernel,length,calls),result);}
pub(crate) proof fn part2_wavelet_horizontal_observed(low:Part1WaveletBand,high:Part1WaveletBand,width:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,capacity:usize,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_wavelet_horizontal_admit(low,high,width,first,maximum)==Ok(capacity),part2_wavelet_rows_result(low,high,first,irreversible,kernel,capacity,result),
    ensures part2_wavelet_horizontal_result(low,high,width,first,irreversible,kernel,maximum,
        match result{Err(error)=>Err(error),Ok(samples)=>Ok(part2_wavelet_wrap(width,low.1,irreversible,samples))}),
{
    reveal(part2_wavelet_horizontal_result);reveal(part2_wavelet_horizontal_run);
    part2_wavelet_rows_frames(low,high,first,irreversible,kernel,capacity,result);
    let output=match result{Err(error)=>Err(error),Ok(samples)=>Ok(part2_wavelet_wrap(width,low.1,irreversible,samples))};
    if result.is_ok(){part2_tier1_storage_pure(output);}
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_rows_run(low,high,first,irreversible,kernel,capacity,calls),
        |samples:Seq<i64>,rest|Some((Ok(part2_wavelet_wrap(width,low.1,irreversible,samples)),rest)),result,output);
}
pub(crate) proof fn part2_wavelet_vertical_observed(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,length:usize,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_wavelet_vertical_admit(low,high,height,first,maximum)==Ok(length),part2_wavelet_columns_result(low,high,height,first,irreversible,kernel,length,result),
    ensures part2_wavelet_vertical_result(low,high,height,first,irreversible,kernel,maximum,
        match result{Err(error)=>Err(error),Ok(samples)=>Ok(part2_wavelet_wrap(low.0,height,irreversible,samples))}),
{
    reveal(part2_wavelet_vertical_result);reveal(part2_wavelet_vertical_run);
    part2_wavelet_columns_frames(low,high,height,first,irreversible,kernel,length,result);
    let output=match result{Err(error)=>Err(error),Ok(samples)=>Ok(part2_wavelet_wrap(low.0,height,irreversible,samples))};
    if result.is_ok(){part2_tier1_storage_pure(output);}
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_columns_run(low,high,height,first,irreversible,kernel,length,calls),
        |samples:Seq<i64>,rest|Some((Ok(part2_wavelet_wrap(low.0,height,irreversible,samples)),rest)),result,output);
}
pub(crate) proof fn part2_wavelet_horizontal_normal(low:Part1WaveletBand,high:Part1WaveletBand,width:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64)
    ensures part2_wavelet_horizontal_result(low,high,width,first,irreversible,kernel,maximum,part2_wavelet_horizontal_value(low,high,width,first,irreversible,kernel,maximum)),
{
    reveal(part2_wavelet_horizontal_result);reveal(part2_wavelet_horizontal_run);
    let result=part2_wavelet_horizontal_value(low,high,width,first,irreversible,kernel,maximum);
    match part2_wavelet_horizontal_admit(low,high,width,first,maximum){
        Err(_)=>{part2_tier1_storage_pure(result);},Ok(capacity)=>{
            part2_wavelet_rows_normal(low,high,first,irreversible,kernel,capacity);
            part2_wavelet_horizontal_observed(low,high,width,first,irreversible,kernel,maximum,capacity,part2_wavelet_rows_value(low,high,first,irreversible,kernel));
        },
    }
}
pub(crate) proof fn part2_wavelet_vertical_normal(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64)
    ensures part2_wavelet_vertical_result(low,high,height,first,irreversible,kernel,maximum,part2_wavelet_vertical_value(low,high,height,first,irreversible,kernel,maximum)),
{
    reveal(part2_wavelet_vertical_result);reveal(part2_wavelet_vertical_run);
    let result=part2_wavelet_vertical_value(low,high,height,first,irreversible,kernel,maximum);
    match part2_wavelet_vertical_admit(low,high,height,first,maximum){
        Err(_)=>{part2_tier1_storage_pure(result);},Ok(length)=>{
            part2_wavelet_columns_normal(low,high,height,first,irreversible,kernel,length);
            part2_wavelet_vertical_observed(low,high,height,first,irreversible,kernel,maximum,length,part2_wavelet_columns_value(low,high,height,first,irreversible,kernel,length));
        },
    }
}
pub(crate) proof fn part2_wavelet_horizontal_frames(low:Part1WaveletBand,high:Part1WaveletBand,width:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,result:Part1ReconstructionResult)
    requires part2_wavelet_horizontal_result(low,high,width,first,irreversible,kernel,maximum,result),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_horizontal_run(low,high,width,first,irreversible,kernel,maximum,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane>|
            (forall|calls| #[trigger] other(calls)==part2_wavelet_horizontal_run(low,high,width,first,irreversible,kernel,maximum,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_wavelet_horizontal_result);part2_tier1_storage_eta(|calls|part2_wavelet_horizontal_run(low,high,width,first,irreversible,kernel,maximum,calls),result);}
pub(crate) proof fn part2_wavelet_vertical_frames(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,result:Part1ReconstructionResult)
    requires part2_wavelet_vertical_result(low,high,height,first,irreversible,kernel,maximum,result),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_vertical_run(low,high,height,first,irreversible,kernel,maximum,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane>|
            (forall|calls| #[trigger] other(calls)==part2_wavelet_vertical_run(low,high,height,first,irreversible,kernel,maximum,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_wavelet_vertical_result);part2_tier1_storage_eta(|calls|part2_wavelet_vertical_run(low,high,height,first,irreversible,kernel,maximum,calls),result);}
pub(crate) proof fn part2_wavelet_level_frames(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,result:Part1ReconstructionResult)
    requires part2_wavelet_level_result(level,irreversible,kernel,maximum,result),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_level_run(level,irreversible,kernel,maximum,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane>|
            (forall|calls| #[trigger] other(calls)==part2_wavelet_level_run(level,irreversible,kernel,maximum,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_wavelet_level_result);part2_tier1_storage_eta(|calls|part2_wavelet_level_run(level,irreversible,kernel,maximum,calls),result);}
pub(crate) open spec fn part2_wavelet_level_rows_value(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize)->Part1ReconstructionResult {
    match kernel{None=>part1_level_rows_and_columns(level,irreversible,length),Some(kernel)=>part2_atk_level_rows_and_columns(level,irreversible,kernel,length)}
}
pub(crate) proof fn part2_wavelet_level_after_high_normal(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,low:Seq<i64>,high:Seq<i64>)
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_level_after_high(level,irreversible,kernel,length,low,high,calls),
        match part2_wavelet_columns_value((level.4,level.0.1,low),(level.4,level.2.1,high),level.5,level.7,irreversible,kernel,length){
            Err(error)=>Err(error),Ok(samples)=>Ok(part2_wavelet_wrap(level.4,level.5,irreversible,samples))}),
{
    let result=part2_wavelet_columns_value((level.4,level.0.1,low),(level.4,level.2.1,high),level.5,level.7,irreversible,kernel,length);
    part2_wavelet_columns_normal((level.4,level.0.1,low),(level.4,level.2.1,high),level.5,level.7,irreversible,kernel,length);
    part2_wavelet_columns_frames((level.4,level.0.1,low),(level.4,level.2.1,high),level.5,level.7,irreversible,kernel,length,result);
    let output=match result{Err(error)=>Err(error),Ok(samples)=>Ok(part2_wavelet_wrap(level.4,level.5,irreversible,samples))};
    if result.is_ok(){part2_tier1_storage_pure(output);}
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_columns_run((level.4,level.0.1,low),(level.4,level.2.1,high),level.5,level.7,irreversible,kernel,length,calls),
        |samples:Seq<i64>,rest|Some((Ok(part2_wavelet_wrap(level.4,level.5,irreversible,samples)),rest)),result,output);
}
pub(crate) proof fn part2_wavelet_level_after_low_normal(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,low:Seq<i64>)
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_level_after_low(level,irreversible,kernel,length,low,calls),
        match part1_transform_area(level.4,level.2.1){Err(error)=>Err(error),Ok(_)=>match part2_wavelet_rows_value(level.2,level.3,level.6,irreversible,kernel){
            Err(error)=>Err(error),Ok(high)=>match part2_wavelet_columns_value((level.4,level.0.1,low),(level.4,level.2.1,high),level.5,level.7,irreversible,kernel,length){
                Err(error)=>Err(error),Ok(samples)=>Ok(part2_wavelet_wrap(level.4,level.5,irreversible,samples))}}}),
{
    let high=part2_wavelet_rows_value(level.2,level.3,level.6,irreversible,kernel);
    let output=match part1_transform_area(level.4,level.2.1){Err(error)=>Err(error),Ok(_)=>match high{Err(error)=>Err(error),Ok(high)=>match part2_wavelet_columns_value((level.4,level.0.1,low),(level.4,level.2.1,high),level.5,level.7,irreversible,kernel,length){
        Err(error)=>Err(error),Ok(samples)=>Ok(part2_wavelet_wrap(level.4,level.5,irreversible,samples))}}};
    match part1_transform_area(level.4,level.2.1){
        Err(_)=>{part2_tier1_storage_pure(output);},Ok(capacity)=>{
            part2_wavelet_rows_normal(level.2,level.3,level.6,irreversible,kernel,capacity);
            part2_wavelet_rows_frames(level.2,level.3,level.6,irreversible,kernel,capacity,high);
            if let Ok(value)=high{part2_wavelet_level_after_high_normal(level,irreversible,kernel,length,low,value);
                part2_tier1_storage_eta(|calls|part2_wavelet_level_after_high(level,irreversible,kernel,length,low,value,calls),output);}
            part2_tier1_storage_bind_frame(|calls|part2_wavelet_rows_run(level.2,level.3,level.6,irreversible,kernel,capacity,calls),
                |high:Seq<i64>,rest|part2_wavelet_level_after_high(level,irreversible,kernel,length,low,high,rest),high,output);
        },
    }
}
pub(crate) proof fn part2_wavelet_level_rows_normal(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize)
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_level_rows_run(level,irreversible,kernel,length,calls),part2_wavelet_level_rows_value(level,irreversible,kernel,length)),
{
    let low=part2_wavelet_rows_value(level.0,level.1,level.6,irreversible,kernel);
    let output=part2_wavelet_level_rows_value(level,irreversible,kernel,length);
    match part1_transform_area(level.4,level.0.1){
        Err(_)=>{part2_tier1_storage_pure(output);},Ok(capacity)=>{
            part2_wavelet_rows_normal(level.0,level.1,level.6,irreversible,kernel,capacity);
            part2_wavelet_rows_frames(level.0,level.1,level.6,irreversible,kernel,capacity,low);
            if let Ok(value)=low{part2_wavelet_level_after_low_normal(level,irreversible,kernel,length,value);
                part2_tier1_storage_eta(|calls|part2_wavelet_level_after_low(level,irreversible,kernel,length,value,calls),output);}
            part2_tier1_storage_bind_frame(|calls|part2_wavelet_rows_run(level.0,level.1,level.6,irreversible,kernel,capacity,calls),
                |low:Seq<i64>,rest|part2_wavelet_level_after_low(level,irreversible,kernel,length,low,rest),low,output);
        },
    }
}
pub(crate) proof fn part2_wavelet_level_normal(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64)
    ensures part2_wavelet_level_result(level,irreversible,kernel,maximum,part2_wavelet_level_value(level,irreversible,kernel,maximum)),
{
    reveal(part2_wavelet_level_result);reveal(part2_wavelet_level_run);
    let result=part2_wavelet_level_value(level,irreversible,kernel,maximum);
    match part2_wavelet_level_admit(level,maximum){Err(_)=>{part2_tier1_storage_pure(result);},Ok(length)=>{
        part2_wavelet_level_rows_normal(level,irreversible,kernel,length);
        part2_tier1_storage_eta(|calls|part2_wavelet_level_rows_run(level,irreversible,kernel,length,calls),result);
    }}
}
pub(crate) proof fn part2_wavelet_level_low_error(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,length:usize,capacity:usize,error:crate::DecodeError)
    requires part2_wavelet_level_admit(level,maximum)==Ok(length),part1_transform_area(level.4,level.0.1)==Ok(capacity),
        part2_wavelet_rows_result(level.0,level.1,level.6,irreversible,kernel,capacity,Err(error)),
    ensures part2_wavelet_level_result(level,irreversible,kernel,maximum,Err(error)),
{
    reveal(part2_wavelet_level_result);reveal(part2_wavelet_level_run);
    part2_wavelet_rows_frames(level.0,level.1,level.6,irreversible,kernel,capacity,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_rows_run(level.0,level.1,level.6,irreversible,kernel,capacity,calls),
        |low:Seq<i64>,rest|part2_wavelet_level_after_low(level,irreversible,kernel,length,low,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_wavelet_level_low_join(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,length:usize,low:Seq<i64>,low_capacity:usize,result:Part1ReconstructionResult)
    requires part2_wavelet_level_admit(level,maximum)==Ok(length),part2_wavelet_rows_value(level.0,level.1,level.6,irreversible,kernel)==Ok(low),
        part1_transform_area(level.4,level.0.1)==Ok(low_capacity),
        part2_tier1_storage_framed(|calls|part2_wavelet_level_after_low(level,irreversible,kernel,length,low,calls),result),
    ensures part2_wavelet_level_result(level,irreversible,kernel,maximum,result),
{
    reveal(part2_wavelet_level_result);reveal(part2_wavelet_level_run);
    part2_tier1_storage_eta(|calls|part2_wavelet_level_after_low(level,irreversible,kernel,length,low,calls),result);
    part2_wavelet_rows_normal(level.0,level.1,level.6,irreversible,kernel,low_capacity);
    part2_wavelet_rows_frames(level.0,level.1,level.6,irreversible,kernel,low_capacity,Ok(low));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_rows_run(level.0,level.1,level.6,irreversible,kernel,low_capacity,calls),
        |low:Seq<i64>,rest|part2_wavelet_level_after_low(level,irreversible,kernel,length,low,rest),Ok(low),result);
}
pub(crate) proof fn part2_wavelet_level_high_join(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,length:usize,low:Seq<i64>,high:Seq<i64>,low_capacity:usize,high_capacity:usize,result:Part1ReconstructionResult)
    requires part2_wavelet_level_admit(level,maximum)==Ok(length),
        part2_wavelet_rows_value(level.0,level.1,level.6,irreversible,kernel)==Ok(low),part2_wavelet_rows_value(level.2,level.3,level.6,irreversible,kernel)==Ok(high),
        part1_transform_area(level.4,level.0.1)==Ok(low_capacity),part1_transform_area(level.4,level.2.1)==Ok(high_capacity),
        part2_tier1_storage_framed(|calls|part2_wavelet_level_after_high(level,irreversible,kernel,length,low,high,calls),result),
    ensures part2_wavelet_level_result(level,irreversible,kernel,maximum,result),
{
    part2_tier1_storage_eta(|calls|part2_wavelet_level_after_high(level,irreversible,kernel,length,low,high,calls),result);
    part2_wavelet_rows_normal(level.2,level.3,level.6,irreversible,kernel,high_capacity);
    part2_wavelet_rows_frames(level.2,level.3,level.6,irreversible,kernel,high_capacity,Ok(high));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_rows_run(level.2,level.3,level.6,irreversible,kernel,high_capacity,calls),
        |high:Seq<i64>,rest|part2_wavelet_level_after_high(level,irreversible,kernel,length,low,high,rest),Ok(high),result);
    part2_tier1_storage_eta(|calls|part2_wavelet_level_after_low(level,irreversible,kernel,length,low,calls),result);
    part2_wavelet_level_low_join(level,irreversible,kernel,maximum,length,low,low_capacity,result);
}
pub(crate) proof fn part2_wavelet_level_high_error(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,length:usize,low:Seq<i64>,low_capacity:usize,capacity:usize,error:crate::DecodeError)
    requires part2_wavelet_level_admit(level,maximum)==Ok(length),part2_wavelet_rows_value(level.0,level.1,level.6,irreversible,kernel)==Ok(low),
        part1_transform_area(level.4,level.0.1)==Ok(low_capacity),
        part1_transform_area(level.4,level.2.1)==Ok(capacity),part2_wavelet_rows_result(level.2,level.3,level.6,irreversible,kernel,capacity,Err(error)),
    ensures part2_wavelet_level_result(level,irreversible,kernel,maximum,Err(error)),
{
    part2_wavelet_rows_frames(level.2,level.3,level.6,irreversible,kernel,capacity,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_rows_run(level.2,level.3,level.6,irreversible,kernel,capacity,calls),
        |high:Seq<i64>,rest|part2_wavelet_level_after_high(level,irreversible,kernel,length,low,high,rest),Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_wavelet_level_after_low(level,irreversible,kernel,length,low,calls),Err(error));
    part2_wavelet_level_low_join(level,irreversible,kernel,maximum,length,low,low_capacity,Err(error));
}
pub(crate) proof fn part2_wavelet_level_columns_error(level:Part1WaveletLevel,irreversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,length:usize,low:Seq<i64>,high:Seq<i64>,low_capacity:usize,high_capacity:usize,error:crate::DecodeError)
    requires part2_wavelet_level_admit(level,maximum)==Ok(length),
        part2_wavelet_rows_value(level.0,level.1,level.6,irreversible,kernel)==Ok(low),part2_wavelet_rows_value(level.2,level.3,level.6,irreversible,kernel)==Ok(high),
        part1_transform_area(level.4,level.0.1)==Ok(low_capacity),part1_transform_area(level.4,level.2.1)==Ok(high_capacity),
        part2_wavelet_columns_result((level.4,level.0.1,low),(level.4,level.2.1,high),level.5,level.7,irreversible,kernel,length,Err(error)),
    ensures part2_wavelet_level_result(level,irreversible,kernel,maximum,Err(error)),
{
    part2_wavelet_columns_frames((level.4,level.0.1,low),(level.4,level.2.1,high),level.5,level.7,irreversible,kernel,length,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_columns_run((level.4,level.0.1,low),(level.4,level.2.1,high),level.5,level.7,irreversible,kernel,length,calls),
        |samples:Seq<i64>,rest|Some((Ok(part2_wavelet_wrap(level.4,level.5,irreversible,samples)),rest)),Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_wavelet_level_after_high(level,irreversible,kernel,length,low,high,calls),Err(error));
    part2_wavelet_level_high_join(level,irreversible,kernel,maximum,length,low,high,low_capacity,high_capacity,Err(error));
}
}
