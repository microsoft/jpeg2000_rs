//! Actual spectral inverse-line children, preserving source and cursor order.
use super::*;
verus! {
pub(crate) open spec fn part2_mct_line_step_admit(previous:(usize,Seq<i64>),source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,index:nat)->Result<(usize,Seq<i64>,bool),crate::DecodeError> {
    let cursor=previous.0;
    if index>=high.len(){Err(part1_transform_error(false))}
    else if cursor as nat+high[index as int] as nat>usize::MAX{Err(part1_transform_error(true))}
    else{let end=(cursor as nat+high[index as int] as nat) as usize;
        if cursor>end || end>source.len(){Err(part1_transform_error(false))}
        else if index>=first.len(){Err(part1_transform_error(false))}
        else{Ok((end,source.subrange(cursor as int,end as int),first[index as int]))}
    }
}
pub(crate) open spec fn part2_mct_line_step_run(previous:(usize,Seq<i64>),source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,index:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(usize,Seq<i64>)> {
    match part2_mct_line_step_admit(previous,source,high,first,index){
        Err(error)=>Some((Err(error),calls)),Ok((end,input,parity))=>part2_tier1_storage_bind(part2_wavelet_sequence_run(previous.1,input,parity,!reversible,None,calls),
            |values:Seq<i64>,rest|Some((Ok((end,values)),rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_mct_line_steps_run(source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,low:usize,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(usize,Seq<i64>)>
    decreases count,
{
    if count==0{Some((if low>source.len(){Err(part1_transform_error(false))}else{Ok((low,source.take(low as int)))},calls))}
    else if count>high.len(){Some((Err(part1_transform_error(false)),calls))}
    else{part2_tier1_storage_bind(part2_mct_line_steps_run(source,high,first,reversible,low,(count-1) as nat,calls),
        |previous:(usize,Seq<i64>),rest|part2_mct_line_step_run(previous,source,high,first,reversible,(high.len()-count) as nat,rest))}
}
pub(crate) open spec fn part2_mct_line_finish(previous:(usize,Seq<i64>),count:usize)->Result<Seq<i64>,crate::DecodeError> {
    if previous.0!=count || previous.1.len()!=count{Err(part1_transform_error(false))}else{Ok(previous.1)}
}
pub(crate) open spec fn part2_mct_line_reconstruction_after_capacity_run(source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,low:usize,count:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_mct_line_steps_run(source,high,first,reversible,low,high.len(),calls),
        |previous:(usize,Seq<i64>),rest|Some((part2_mct_line_finish(previous,count),rest)))
}
pub(crate) open spec fn part2_mct_line_reconstruction_run(source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,low:usize,count:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_mct_runtime_capacity_run(
        Part2MctRuntimeCapacity::WaveletReconstruction {source,high,first,reversible,low,count},calls),
        |_:(),rest|part2_mct_line_reconstruction_after_capacity_run(source,high,first,reversible,low,count,rest))
}
pub(crate) open spec fn part2_mct_line_reconstruction_result(source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,low:usize,count:usize,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_line_reconstruction_run(source,high,first,reversible,low,count,calls),result)
}
pub(crate) proof fn part2_mct_line_reconstruction_after_capacity_frames(source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,low:usize,count:usize,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_tier1_storage_framed(|calls|part2_mct_line_reconstruction_after_capacity_run(source,high,first,reversible,low,count,calls),result),
    ensures part2_mct_line_reconstruction_result(source,high,first,reversible,low,count,result),
{
    let capacity=Part2MctRuntimeCapacity::WaveletReconstruction {source,high,first,reversible,low,count};
    part2_mct_runtime_capacity_normal(capacity);
    part2_tier1_storage_eta(|calls|part2_mct_line_reconstruction_after_capacity_run(source,high,first,reversible,low,count,calls),result);
    part2_tier1_storage_bind_frame(|calls|part2_mct_runtime_capacity_run(capacity,calls),
        |_:(),rest|part2_mct_line_reconstruction_after_capacity_run(source,high,first,reversible,low,count,rest),Ok(()),result);
}
pub(crate) proof fn part2_mct_line_reconstruction_capacity_error(source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,low:usize,count:usize,error:crate::DecodeError)
    requires part2_mct_runtime_capacity_result(Part2MctRuntimeCapacity::WaveletReconstruction {source,high,first,reversible,low,count},Err(error)),
    ensures part2_mct_line_reconstruction_result(source,high,first,reversible,low,count,Err(error)),
{
    let capacity=Part2MctRuntimeCapacity::WaveletReconstruction {source,high,first,reversible,low,count};
    part2_tier1_storage_bind_frame(|calls|part2_mct_runtime_capacity_run(capacity,calls),
        |_:(),rest|part2_mct_line_reconstruction_after_capacity_run(source,high,first,reversible,low,count,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_mct_line_step_normal(previous:(usize,Seq<i64>),source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,index:nat)
    ensures part2_tier1_storage_framed(|calls|part2_mct_line_step_run(previous,source,high,first,reversible,index,calls),
        part2_mct_wavelet_reconstruction_step(Ok(previous),source,high,first,reversible,index)),
{
    let result=part2_mct_wavelet_reconstruction_step(Ok(previous),source,high,first,reversible,index);
    match part2_mct_line_step_admit(previous,source,high,first,index){
        Err(_)=>{part2_tier1_storage_pure(result);},Ok((end,input,parity))=>{
            let values=part1_inverse_sequence(previous.1,input,parity,!reversible);
            part2_wavelet_sequence_normal(previous.1,input,parity,!reversible,None);
            part2_wavelet_sequence_frames(previous.1,input,parity,!reversible,None,values);
            if values.is_ok(){part2_tier1_storage_pure(result);}
            part2_tier1_storage_bind_frame(|calls|part2_wavelet_sequence_run(previous.1,input,parity,!reversible,None,calls),
                |values:Seq<i64>,rest|Some((Ok((end,values)),rest)),values,result);
        },
    }
}
pub(crate) proof fn part2_mct_line_steps_normal(source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,low:usize,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_mct_line_steps_run(source,high,first,reversible,low,count,calls),
        part2_mct_wavelet_reconstruction_steps(source,high,first,reversible,low,count)),
    decreases count,
{
    reveal(part2_mct_line_steps_run);reveal(part2_mct_wavelet_reconstruction_steps);
    let result=part2_mct_wavelet_reconstruction_steps(source,high,first,reversible,low,count);
    if count==0 || count>high.len(){part2_tier1_storage_pure(result);}else{
        let previous=part2_mct_wavelet_reconstruction_steps(source,high,first,reversible,low,(count-1) as nat);
        part2_mct_line_steps_normal(source,high,first,reversible,low,(count-1) as nat);
        if let Ok(value)=previous{part2_mct_line_step_normal(value,source,high,first,reversible,(high.len()-count) as nat);
            part2_tier1_storage_eta(|calls|part2_mct_line_step_run(value,source,high,first,reversible,(high.len()-count) as nat,calls),result);}
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_steps_run(source,high,first,reversible,low,(count-1) as nat,calls),
            |previous:(usize,Seq<i64>),rest|part2_mct_line_step_run(previous,source,high,first,reversible,(high.len()-count) as nat,rest),previous,result);
    }
}
pub(crate) proof fn part2_mct_line_reconstruction_normal(source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,low:usize,count:usize)
    ensures part2_mct_line_reconstruction_result(source,high,first,reversible,low,count,part2_mct_wavelet_reconstruction(source,high,first,reversible,low,count)),
{
    let previous=part2_mct_wavelet_reconstruction_steps(source,high,first,reversible,low,high.len());
    let result=part2_mct_wavelet_reconstruction(source,high,first,reversible,low,count);
    part2_mct_line_steps_normal(source,high,first,reversible,low,high.len());
    if previous.is_ok(){part2_tier1_storage_pure(result);}
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_steps_run(source,high,first,reversible,low,high.len(),calls),
        |previous:(usize,Seq<i64>),rest|Some((part2_mct_line_finish(previous,count),rest)),previous,result);
    part2_mct_line_reconstruction_after_capacity_frames(source,high,first,reversible,low,count,
        part2_mct_wavelet_reconstruction(source,high,first,reversible,low,count));
}
pub(crate) proof fn part2_mct_line_prefix_error(source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,low:usize,prefix:nat,count:nat,error:crate::DecodeError)
    requires prefix<=count,count<=high.len(),part2_tier1_storage_framed(|calls|part2_mct_line_steps_run(source,high,first,reversible,low,prefix,calls),Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_mct_line_steps_run(source,high,first,reversible,low,count,calls),Err(error)),
    decreases count-prefix,
{
    if prefix<count{reveal(part2_mct_line_steps_run);
        part2_mct_line_prefix_error(source,high,first,reversible,low,prefix,(count-1) as nat,error);
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_steps_run(source,high,first,reversible,low,(count-1) as nat,calls),
            |previous:(usize,Seq<i64>),rest|part2_mct_line_step_run(previous,source,high,first,reversible,(high.len()-count) as nat,rest),Err(error),Err(error));
    }
}
pub(crate) proof fn part2_mct_line_child_error(source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,low:usize,count:usize,processed:nat,previous:(usize,Seq<i64>),end:usize,input:Seq<i64>,parity:bool,error:crate::DecodeError)
    requires processed<high.len(),part2_mct_wavelet_reconstruction_steps(source,high,first,reversible,low,processed)==Ok(previous),
        part2_mct_line_step_admit(previous,source,high,first,(high.len()-processed-1) as nat)==Ok((end,input,parity)),
        part2_wavelet_sequence_result(previous.1,input,parity,!reversible,None,Err(error)),
    ensures part2_mct_line_reconstruction_result(source,high,first,reversible,low,count,Err(error)),
{
    reveal(part2_mct_line_steps_run);
    part2_wavelet_sequence_frames(previous.1,input,parity,!reversible,None,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_sequence_run(previous.1,input,parity,!reversible,None,calls),
        |values:Seq<i64>,rest|Some((Ok((end,values)),rest)),Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_mct_line_step_run(previous,source,high,first,reversible,(high.len()-processed-1) as nat,calls),Err(error));
    part2_mct_line_steps_normal(source,high,first,reversible,low,processed);
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_steps_run(source,high,first,reversible,low,processed,calls),
        |previous:(usize,Seq<i64>),rest|part2_mct_line_step_run(previous,source,high,first,reversible,(high.len()-processed-1) as nat,rest),Ok(previous),Err(error));
    part2_mct_line_prefix_error(source,high,first,reversible,low,processed+1,high.len(),error);
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_steps_run(source,high,first,reversible,low,high.len(),calls),
        |previous:(usize,Seq<i64>),rest|Some((part2_mct_line_finish(previous,count),rest)),Err(error),Err(error));
    part2_mct_line_reconstruction_after_capacity_frames(source,high,first,reversible,low,count,Err(error));
}
pub type Part2MctLinePixelEffect=(Result<(),crate::DecodeError>,Seq<Part2MctComponent>,Seq<i64>);
pub(crate) open spec fn part2_mct_line_pixel_after(before:Seq<Part2MctComponent>,prepared:Part2MctWaveletPreparation,sample:usize,source:Seq<i64>,result:Result<Seq<i64>,crate::DecodeError>)->Part2MctLinePixelEffect {
    match result{Err(error)=>(Err(error),before,source),Ok(values)=>{
        let stored=part2_mct_store_output_rows(before,prepared.1,values,sample,prepared.6 as nat);(stored.0,stored.1,source)
    }}
}
pub(crate) open spec fn part2_mct_line_pixel_run(before:Seq<Part2MctComponent>,prepared:Part2MctWaveletPreparation,sample:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLinePixelEffect> {
    let snapshot=part2_mct_wavelet_snapshot(before,prepared.0,prepared.8,sample,part2_mct_wavelet_reversible(prepared.7),prepared.6 as nat);
    match snapshot.0{
        Err(error)=>Some((Ok((Err(error),before,snapshot.1)),calls)),Ok(())=>part2_tier1_storage_resume(
            part2_mct_line_reconstruction_run(snapshot.1,prepared.3,prepared.2,part2_mct_wavelet_reversible(prepared.7),prepared.4,prepared.6,calls),
            |result:Result<Seq<i64>,crate::DecodeError>,rest|Some((Ok(part2_mct_line_pixel_after(before,prepared,sample,snapshot.1,result)),rest))),
    }
}
pub(crate) open spec fn part2_mct_line_pixel_result(before:Seq<Part2MctComponent>,prepared:Part2MctWaveletPreparation,sample:usize,result:Part2MctLinePixelEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_line_pixel_run(before,prepared,sample,calls),Ok(result))
}
pub(crate) proof fn part2_mct_line_pixel_normal(before:Seq<Part2MctComponent>,prepared:Part2MctWaveletPreparation,sample:usize)
    ensures part2_mct_line_pixel_result(before,prepared,sample,part2_mct_wavelet_pixel(before,prepared,sample)),
{
    let snapshot=part2_mct_wavelet_snapshot(before,prepared.0,prepared.8,sample,part2_mct_wavelet_reversible(prepared.7),prepared.6 as nat);
    let result=Ok(part2_mct_wavelet_pixel(before,prepared,sample));
    if snapshot.0.is_err(){part2_tier1_storage_pure(result);}else{
        let child=part2_mct_wavelet_reconstruction(snapshot.1,prepared.3,prepared.2,part2_mct_wavelet_reversible(prepared.7),prepared.4,prepared.6);
        part2_mct_line_reconstruction_normal(snapshot.1,prepared.3,prepared.2,part2_mct_wavelet_reversible(prepared.7),prepared.4,prepared.6);
        part2_tier1_storage_eta(|calls|part2_mct_line_reconstruction_run(snapshot.1,prepared.3,prepared.2,part2_mct_wavelet_reversible(prepared.7),prepared.4,prepared.6,calls),child);
        part2_tier1_storage_pure(result);
        part2_tier1_resume_frame(|calls|part2_mct_line_reconstruction_run(snapshot.1,prepared.3,prepared.2,part2_mct_wavelet_reversible(prepared.7),prepared.4,prepared.6,calls),
            |child:Result<Seq<i64>,crate::DecodeError>,rest|Some((Ok(part2_mct_line_pixel_after(before,prepared,sample,snapshot.1,child)),rest)),child,result);
    }
}
pub(crate) proof fn part2_mct_line_pixel_child_error(before:Seq<Part2MctComponent>,prepared:Part2MctWaveletPreparation,sample:usize,source:Seq<i64>,error:crate::DecodeError)
    requires part2_mct_wavelet_snapshot(before,prepared.0,prepared.8,sample,part2_mct_wavelet_reversible(prepared.7),prepared.6 as nat)==(Ok(()),source),
        part2_mct_line_reconstruction_result(source,prepared.3,prepared.2,part2_mct_wavelet_reversible(prepared.7),prepared.4,prepared.6,Err(error)),
    ensures part2_mct_line_pixel_result(before,prepared,sample,(Err(error),before,source)),
{
    part2_tier1_storage_eta(|calls|part2_mct_line_reconstruction_run(source,prepared.3,prepared.2,part2_mct_wavelet_reversible(prepared.7),prepared.4,prepared.6,calls),Err(error));
    let result=Ok::<Part2MctLinePixelEffect,crate::DecodeError>((Err(error),before,source));part2_tier1_storage_pure(result);
    part2_tier1_resume_frame(|calls|part2_mct_line_reconstruction_run(source,prepared.3,prepared.2,part2_mct_wavelet_reversible(prepared.7),prepared.4,prepared.6,calls),
        |child:Result<Seq<i64>,crate::DecodeError>,rest|Some((Ok(part2_mct_line_pixel_after(before,prepared,sample,source,child)),rest)),Err(error),result);
}
}
