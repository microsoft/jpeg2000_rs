//! Actual fresh column-gather and parity-interleave line owners.
use super::*;
verus! {
pub enum Part2WaveletLineContext {Gather {width:u32,height:u32,column:u32},Interleave {low:nat,high:nat,first:bool}}
pub(crate) open spec fn part2_wavelet_line_count(context:Part2WaveletLineContext)->nat {
    match context{Part2WaveletLineContext::Gather {height,..}=>height as nat,Part2WaveletLineContext::Interleave {low,high,..}=>low+high}
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_line_capacity_run(context:Part2WaveletLineContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=part2_wavelet_line_count(context);
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::WaveletLineCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=count{None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) open spec fn part2_wavelet_line_capacity_result(context:Part2WaveletLineContext,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_line_capacity_run(context,calls),result)
}
pub(crate) proof fn part2_wavelet_line_capacity_observed(context:Part2WaveletLineContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_wavelet_line_count(context)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_wavelet_line_capacity_result(context,result),
{
    reveal(part2_wavelet_line_capacity_run);
    let count=part2_wavelet_line_count(context);
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::WaveletLineCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_wavelet_line_capacity_run(context,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_wavelet_line_capacity_run(context,calls),prefix,result));
}
pub(crate) open spec fn part2_wavelet_interleave_admit(low:nat,high:nat,first:bool)->Result<(),crate::DecodeError> {
    let length=low+high;
    let expected=if first{length/2+length%2}else{length/2};
    if length>usize::MAX{Err(part1_transform_error(true))}
    else if low!=expected || high!=length-expected{Err(part1_transform_error(false))}
    else{Ok(())}
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_interleave_run(low:Seq<i64>,high:Seq<i64>,first:bool,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    match part2_wavelet_interleave_admit(low.len(),high.len(),first){
        Err(error)=>Some((Err(error),calls)),Ok(())=>part2_tier1_storage_bind(
            part2_wavelet_line_capacity_run(Part2WaveletLineContext::Interleave {low:low.len(),high:high.len(),first},calls),
            |_:(),rest|Some((part1_interleaved(low,high,first),rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_interleave_result(low:Seq<i64>,high:Seq<i64>,first:bool,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_interleave_run(low,high,first,calls),result)
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_gather_run(band:Part1WaveletBand,column:u32,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    if column>=band.0 || band.1>usize::MAX{Some((part1_collect_column(band,column),calls))}
    else{part2_tier1_storage_bind(part2_wavelet_line_capacity_run(Part2WaveletLineContext::Gather {width:band.0,height:band.1,column},calls),
        |_:(),rest|Some((part1_collect_column(band,column),rest)))}
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_gather_result(band:Part1WaveletBand,column:u32,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_gather_run(band,column,calls),result)
}
pub(crate) proof fn part2_wavelet_interleave_normal(low:Seq<i64>,high:Seq<i64>,first:bool)
    ensures part2_wavelet_interleave_result(low,high,first,part1_interleaved(low,high,first)),
{
    reveal(part2_wavelet_interleave_result);reveal(part2_wavelet_interleave_run);let result=part1_interleaved(low,high,first);
    match part2_wavelet_interleave_admit(low.len(),high.len(),first){
        Err(_)=>{part2_tier1_storage_pure(result);},Ok(())=>{
            let context=Part2WaveletLineContext::Interleave {low:low.len(),high:high.len(),first};
            part2_wavelet_line_capacity_observed(context,Ok(()));part2_tier1_storage_pure(result);
            part2_tier1_storage_bind_frame(|calls|part2_wavelet_line_capacity_run(context,calls),|_:(),rest|Some((result,rest)),Ok(()),result);
        },
    }
}
pub(crate) proof fn part2_wavelet_gather_normal(band:Part1WaveletBand,column:u32)
    ensures part2_wavelet_gather_result(band,column,part1_collect_column(band,column)),
{
    reveal(part2_wavelet_gather_result);reveal(part2_wavelet_gather_run);let result=part1_collect_column(band,column);
    if column>=band.0 || band.1>usize::MAX{part2_tier1_storage_pure(result);}else{
        let context=Part2WaveletLineContext::Gather {width:band.0,height:band.1,column};
        part2_wavelet_line_capacity_observed(context,Ok(()));part2_tier1_storage_pure(result);
        part2_tier1_storage_bind_frame(|calls|part2_wavelet_line_capacity_run(context,calls),|_:(),rest|Some((result,rest)),Ok(()),result);
    }
}
pub(crate) proof fn part2_wavelet_interleave_refused(low:Seq<i64>,high:Seq<i64>,first:bool,error:crate::DecodeError)
    requires part2_wavelet_interleave_admit(low.len(),high.len(),first)==Ok(()),
        part2_wavelet_line_capacity_result(Part2WaveletLineContext::Interleave {low:low.len(),high:high.len(),first},Err(error)),
    ensures part2_wavelet_interleave_result(low,high,first,Err(error)),
{
    reveal(part2_wavelet_interleave_result);reveal(part2_wavelet_interleave_run);
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_line_capacity_run(Part2WaveletLineContext::Interleave {low:low.len(),high:high.len(),first},calls),
        |_:(),rest|Some((part1_interleaved(low,high,first),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_wavelet_gather_refused(band:Part1WaveletBand,column:u32,error:crate::DecodeError)
    requires column<band.0,band.1<=usize::MAX,
        part2_wavelet_line_capacity_result(Part2WaveletLineContext::Gather {width:band.0,height:band.1,column},Err(error)),
    ensures part2_wavelet_gather_result(band,column,Err(error)),
{
    reveal(part2_wavelet_gather_result);reveal(part2_wavelet_gather_run);
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_line_capacity_run(Part2WaveletLineContext::Gather {width:band.0,height:band.1,column},calls),
        |_:(),rest|Some((part1_collect_column(band,column),rest)),Err(error),Err(error));
}
pub(crate) open spec fn part2_wavelet_sequence_value(low:Seq<i64>,high:Seq<i64>,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>)->Result<Seq<i64>,crate::DecodeError> {
    match kernel{Some(kernel)=>part2_inverse_arbitrary(low,high,first,kernel),None=>part1_inverse_sequence(low,high,first,irreversible)}
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_sequence_run(low:Seq<i64>,high:Seq<i64>,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_wavelet_interleave_run(low,high,first,calls),
        |_:Seq<i64>,rest|Some((part2_wavelet_sequence_value(low,high,first,irreversible,kernel),rest)))
}
pub closed spec fn part2_wavelet_sequence_result(low:Seq<i64>,high:Seq<i64>,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_sequence_run(low,high,first,irreversible,kernel,calls),result)
}
pub(crate) proof fn part2_wavelet_sequence_normal(low:Seq<i64>,high:Seq<i64>,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>)
    ensures part2_wavelet_sequence_result(low,high,first,irreversible,kernel,part2_wavelet_sequence_value(low,high,first,irreversible,kernel)),
{
    reveal(part2_wavelet_sequence_result);reveal(part2_wavelet_sequence_run);
    let result=part2_wavelet_sequence_value(low,high,first,irreversible,kernel);
    part2_wavelet_interleave_normal(low,high,first);part2_wavelet_interleave_frames(low,high,first,part1_interleaved(low,high,first));
    if part1_interleaved(low,high,first).is_ok(){part2_tier1_storage_pure(result);}
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_interleave_run(low,high,first,calls),
        |_:Seq<i64>,rest|Some((result,rest)),part1_interleaved(low,high,first),result);
}
pub(crate) proof fn part2_wavelet_sequence_interleave_error(low:Seq<i64>,high:Seq<i64>,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,error:crate::DecodeError)
    requires part2_wavelet_interleave_result(low,high,first,Err(error)),
    ensures part2_wavelet_sequence_result(low,high,first,irreversible,kernel,Err(error)),
{
    reveal(part2_wavelet_sequence_result);reveal(part2_wavelet_sequence_run);
    part2_wavelet_interleave_frames(low,high,first,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_interleave_run(low,high,first,calls),
        |_:Seq<i64>,rest|Some((part2_wavelet_sequence_value(low,high,first,irreversible,kernel),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_wavelet_sequence_frames(low:Seq<i64>,high:Seq<i64>,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_wavelet_sequence_result(low,high,first,irreversible,kernel,result),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_sequence_run(low,high,first,irreversible,kernel,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>>|
            (forall|calls| #[trigger] other(calls)==part2_wavelet_sequence_run(low,high,first,irreversible,kernel,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_wavelet_sequence_result);part2_tier1_storage_eta(|calls|part2_wavelet_sequence_run(low,high,first,irreversible,kernel,calls),result);}
pub(crate) proof fn part2_wavelet_sequence_kernel_observed(low:Seq<i64>,high:Seq<i64>,first:bool,irreversible:bool,kernel:Part2RawKernel,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_wavelet_sequence_result(low,high,first,!kernel.0,Some(kernel),result),
    ensures part2_wavelet_sequence_result(low,high,first,irreversible,Some(kernel),result),
{
    reveal(part2_wavelet_sequence_result);reveal(part2_wavelet_sequence_run);
    part2_tier1_storage_eta(|calls|part2_wavelet_sequence_run(low,high,first,!kernel.0,Some(kernel),calls),result);
}
pub(crate) proof fn part2_wavelet_interleave_frames(low:Seq<i64>,high:Seq<i64>,first:bool,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_wavelet_interleave_result(low,high,first,result),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_interleave_run(low,high,first,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>>|
            (forall|calls| #[trigger] other(calls)==part2_wavelet_interleave_run(low,high,first,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_wavelet_interleave_result);part2_tier1_storage_eta(|calls|part2_wavelet_interleave_run(low,high,first,calls),result);}
pub(crate) proof fn part2_wavelet_gather_frames(band:Part1WaveletBand,column:u32,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_wavelet_gather_result(band,column,result),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_gather_run(band,column,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>>|
            (forall|calls| #[trigger] other(calls)==part2_wavelet_gather_run(band,column,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_wavelet_gather_result);part2_tier1_storage_eta(|calls|part2_wavelet_gather_run(band,column,calls),result);}
}
