//! Actual inverse-wavelet children inside component preparation/folding.
use super::*;
verus! {
pub enum Part2WaveletRequest {
    Horizontal {low:Part1WaveletBand,high:Part1WaveletBand,width:u32,first:bool},
    Vertical {low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool},
    Level {level:Part1WaveletLevel},
}
pub(crate) open spec fn part2_wavelet_request_run(request:Part2WaveletRequest,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1ReconstructedPlane> {
    let irreversible=match kernel{None=>!reversible,Some(kernel)=>!kernel.0};
    match request{
        Part2WaveletRequest::Horizontal {low,high,width,first}=>part2_wavelet_horizontal_run(low,high,width,first,irreversible,kernel,maximum,calls),
        Part2WaveletRequest::Vertical {low,high,height,first}=>part2_wavelet_vertical_run(low,high,height,first,irreversible,kernel,maximum,calls),
        Part2WaveletRequest::Level {level}=>part2_wavelet_level_run(level,irreversible,kernel,maximum,calls),
    }
}
pub(crate) open spec fn part2_wavelet_request_value(request:Part2WaveletRequest,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64)->Part1ReconstructionResult {
    let irreversible=match kernel{None=>!reversible,Some(kernel)=>!kernel.0};
    match request{
        Part2WaveletRequest::Horizontal {low,high,width,first}=>part2_wavelet_horizontal_value(low,high,width,first,irreversible,kernel,maximum),
        Part2WaveletRequest::Vertical {low,high,height,first}=>part2_wavelet_vertical_value(low,high,height,first,irreversible,kernel,maximum),
        Part2WaveletRequest::Level {level}=>part2_wavelet_level_value(level,irreversible,kernel,maximum),
    }
}
pub(crate) open spec fn part2_wavelet_resolution_admit(before:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,
    direction:crate::codestream::DecompositionDirection,reversible:bool)->Result<(Part2WaveletRequest,usize),crate::DecodeError> {
    use crate::codestream::DecompositionDirection::*;
    let first=before.3 as nat;
    if first>=bands.len(){Err(part1_block_placement_error(false))}
    else if bands[first as int].2!=part1_prepare_fraction(reversible) || first>=geometry.len(){Err(part1_block_placement_error(false))}
    else{
        let detail=bands[first as int];let shape=geometry[first as int];let low=(before.0,before.1,before.2);
        match direction{
            None=>Err(part1_block_placement_error(false)),
            Horizontal|Vertical=>if first+1>usize::MAX{Err(part1_block_placement_error(true))}else{
                Ok((if direction is Horizontal{Part2WaveletRequest::Horizontal {low,high:part1_prepare_band(detail),width:shape.resolution_width,first:shape.low_pass_first_x}}
                else{Part2WaveletRequest::Vertical {low,high:part1_prepare_band(detail),height:shape.resolution_height,first:shape.low_pass_first_y}},(first+1) as usize))
            },
            TwoDimensional=>if first+1>usize::MAX{Err(part1_block_placement_error(true))}
                else if first+1>=bands.len(){Err(part1_block_placement_error(false))}
                else if first+2>usize::MAX{Err(part1_block_placement_error(true))}
                else if first+2>=bands.len(){Err(part1_block_placement_error(false))}
                else if bands[(first+1) as int].2!=part1_prepare_fraction(reversible) || bands[(first+2) as int].2!=part1_prepare_fraction(reversible){Err(part1_block_placement_error(false))}
                else if first+3>usize::MAX{Err(part1_block_placement_error(true))}
                else{Ok((Part2WaveletRequest::Level {level:(low,part1_prepare_band(detail),part1_prepare_band(bands[(first+1) as int]),part1_prepare_band(bands[(first+2) as int]),
                    shape.resolution_width,shape.resolution_height,shape.low_pass_first_x,shape.low_pass_first_y)},(first+3) as usize))},
        }
    }
}
pub(crate) open spec fn part2_wavelet_resolution_finish(reversible:bool,next:usize,plane:Part1ReconstructedPlane)->Result<Part1PrepareFold,crate::DecodeError> {
    if plane.2!=part1_prepare_fraction(reversible){Err(part1_block_placement_error(false))}
    else{Ok((plane.0,plane.1,plane.3,next))}
}
pub(crate) open spec fn part2_wavelet_resolution_finish_run(reversible:bool,next:usize,plane:Part1ReconstructedPlane,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareFold> {
    if plane.2!=part1_prepare_fraction(reversible){Some((Err(part1_block_placement_error(false)),calls))}
    else{part2_prepare_plane_copy_run(plane,next,calls)}
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_resolution_run(before:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,
    direction:crate::codestream::DecompositionDirection,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareFold> {
    match part2_wavelet_resolution_admit(before,bands,geometry,direction,reversible){
        Err(error)=>Some((Err(error),calls)),Ok((request,next))=>part2_tier1_storage_bind(part2_wavelet_request_run(request,reversible,kernel,maximum,calls),
            |plane:Part1ReconstructedPlane,rest|part2_wavelet_resolution_finish_run(reversible,next,plane,rest)),
    }
}
pub(crate) open spec fn part2_wavelet_resolution_result(before:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,
    direction:crate::codestream::DecompositionDirection,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,result:Result<Part1PrepareFold,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_resolution_run(before,bands,geometry,direction,reversible,kernel,maximum,calls),result)
}
pub(crate) open spec fn part2_wavelet_fold_next(before:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,style:Part1PrepareStyle,
    reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareFold> {
    match part1_direction_for_resolution(style.1,style.2,count as u8){
        Err(error)=>Some((Err(error),calls)),Ok(direction)=>{
            let transformed=if matches!(direction,crate::codestream::DecompositionDirection::None){Some((Ok(before),calls))}
                else{part2_wavelet_resolution_run(before,bands,geometry,direction,reversible,kernel,maximum,calls)};
            part2_tier1_storage_bind(transformed,|after:Part1PrepareFold,rest|Some((if count>=255{Err(part1_block_placement_error(true))}else{Ok(after)},rest)))
        },
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_fold_run(initial:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,style:Part1PrepareStyle,
    reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareFold>
    decreases count,
{
    if count==0{Some((Ok(initial),calls))}else{
        part2_tier1_storage_bind(part2_wavelet_fold_run(initial,bands,geometry,style,reversible,kernel,maximum,(count-1) as nat,calls),
            |before:Part1PrepareFold,rest|part2_wavelet_fold_next(before,bands,geometry,style,reversible,kernel,maximum,count,rest))
    }
}
pub(crate) open spec fn part2_wavelet_reconstruct_run(bands:Seq<Part1WorkingSubbandModel>,plan:Part1PreparePlan,style:Part1PrepareStyle,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareFold> {
    if bands.len()==0{Some((Err(part1_block_placement_error(false)),calls))}
    else{part2_tier1_storage_bind(part2_prepare_initial_run(bands[0],calls),
        |initial:Part1PrepareFold,rest|part2_wavelet_fold_run(initial,bands,plan.subbands,style,reversible,kernel,maximum,plan.resolution as nat,rest))}
}
pub(crate) open spec fn part2_wavelet_reconstruct_result(bands:Seq<Part1WorkingSubbandModel>,plan:Part1PreparePlan,style:Part1PrepareStyle,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,
    result:Result<Part1PrepareFold,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_reconstruct_run(bands,plan,style,reversible,kernel,maximum,calls),result)
}
pub(crate) proof fn part2_wavelet_request_normal(request:Part2WaveletRequest,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64)
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_request_run(request,reversible,kernel,maximum,calls),part2_wavelet_request_value(request,reversible,kernel,maximum)),
{
    let irreversible=match kernel{None=>!reversible,Some(kernel)=>!kernel.0};
    match request{
        Part2WaveletRequest::Horizontal {low,high,width,first}=>{part2_wavelet_horizontal_normal(low,high,width,first,irreversible,kernel,maximum);
            part2_wavelet_horizontal_frames(low,high,width,first,irreversible,kernel,maximum,part2_wavelet_horizontal_value(low,high,width,first,irreversible,kernel,maximum));},
        Part2WaveletRequest::Vertical {low,high,height,first}=>{part2_wavelet_vertical_normal(low,high,height,first,irreversible,kernel,maximum);
            part2_wavelet_vertical_frames(low,high,height,first,irreversible,kernel,maximum,part2_wavelet_vertical_value(low,high,height,first,irreversible,kernel,maximum));},
        Part2WaveletRequest::Level {level}=>{part2_wavelet_level_normal(level,irreversible,kernel,maximum);part2_wavelet_level_frames(level,irreversible,kernel,maximum,part2_wavelet_level_value(level,irreversible,kernel,maximum));},
    }
}
pub(crate) proof fn part2_wavelet_request_observed(request:Part2WaveletRequest,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,result:Part1ReconstructionResult)
    requires match request{
        Part2WaveletRequest::Horizontal {low,high,width,first}=>part2_wavelet_horizontal_result(low,high,width,first,match kernel{None=>!reversible,Some(kernel)=>!kernel.0},kernel,maximum,result),
        Part2WaveletRequest::Vertical {low,high,height,first}=>part2_wavelet_vertical_result(low,high,height,first,match kernel{None=>!reversible,Some(kernel)=>!kernel.0},kernel,maximum,result),
        Part2WaveletRequest::Level {level}=>part2_wavelet_level_result(level,match kernel{None=>!reversible,Some(kernel)=>!kernel.0},kernel,maximum,result),
    },
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_request_run(request,reversible,kernel,maximum,calls),result),
{
    let irreversible=match kernel{None=>!reversible,Some(kernel)=>!kernel.0};
    match request{
        Part2WaveletRequest::Horizontal {low,high,width,first}=>{part2_wavelet_horizontal_frames(low,high,width,first,irreversible,kernel,maximum,result);},
        Part2WaveletRequest::Vertical {low,high,height,first}=>{part2_wavelet_vertical_frames(low,high,height,first,irreversible,kernel,maximum,result);},
        Part2WaveletRequest::Level {level}=>{part2_wavelet_level_frames(level,irreversible,kernel,maximum,result);},
    }
}
pub(crate) proof fn part2_wavelet_resolution_normal(before:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,
    direction:crate::codestream::DecompositionDirection,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64)
    ensures part2_wavelet_resolution_result(before,bands,geometry,direction,reversible,kernel,maximum,part2_prepare_resolution(before,bands,geometry,direction,reversible,kernel,maximum)),
{
    reveal(part2_wavelet_resolution_run);
    part2_wavelet_resolution_equation(before,bands,geometry,direction,reversible,kernel,maximum);
    let result=part2_prepare_resolution(before,bands,geometry,direction,reversible,kernel,maximum);
    match part2_wavelet_resolution_admit(before,bands,geometry,direction,reversible){
        Err(_)=>{part2_tier1_storage_pure(result);},Ok((request,next))=>{
            let plane=part2_wavelet_request_value(request,reversible,kernel,maximum);
            part2_wavelet_request_normal(request,reversible,kernel,maximum);
            part2_tier1_storage_eta(|calls|part2_wavelet_request_run(request,reversible,kernel,maximum,calls),plane);
            if let Ok(value)=plane{
                if value.2!=part1_prepare_fraction(reversible){part2_tier1_storage_pure(result);}
                else{part2_prepare_plane_copy_normal(value,next);
                    part2_tier1_storage_eta(|calls|part2_prepare_plane_copy_run(value,next,calls),result);}
            }
            part2_tier1_storage_bind_frame(|calls|part2_wavelet_request_run(request,reversible,kernel,maximum,calls),
                |plane:Part1ReconstructedPlane,rest|part2_wavelet_resolution_finish_run(reversible,next,plane,rest),plane,result);
        },
    }
}
pub(crate) proof fn part2_wavelet_resolution_equation(before:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,
        direction:crate::codestream::DecompositionDirection,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64)
        ensures part2_prepare_resolution(before,bands,geometry,direction,reversible,kernel,maximum)==match part2_wavelet_resolution_admit(before,bands,geometry,direction,reversible){
            Err(error)=>Err(error),Ok((request,next))=>match part2_wavelet_request_value(request,reversible,kernel,maximum){
                Err(error)=>Err(error),Ok(plane)=>part2_wavelet_resolution_finish(reversible,next,plane),
            },
        },
    {
        reveal(part2_prepare_resolution);
        reveal(part2_kernel_inverse_horizontal);reveal(part2_kernel_inverse_vertical);reveal(part2_kernel_inverse_level);
        match direction{
            crate::codestream::DecompositionDirection::None=>{},
            crate::codestream::DecompositionDirection::Horizontal=>{},
            crate::codestream::DecompositionDirection::Vertical=>{},
            crate::codestream::DecompositionDirection::TwoDimensional=>{},
        }
    }
pub(crate) proof fn part2_wavelet_resolution_child_error(before:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,direction:crate::codestream::DecompositionDirection,
    reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,request:Part2WaveletRequest,next:usize,error:crate::DecodeError)
    requires part2_wavelet_resolution_admit(before,bands,geometry,direction,reversible)==Ok((request,next)),
        part2_tier1_storage_framed(|calls|part2_wavelet_request_run(request,reversible,kernel,maximum,calls),Err(error)),
    ensures part2_wavelet_resolution_result(before,bands,geometry,direction,reversible,kernel,maximum,Err(error)),
{
    reveal(part2_wavelet_resolution_run);
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_request_run(request,reversible,kernel,maximum,calls),
        |plane:Part1ReconstructedPlane,rest|part2_wavelet_resolution_finish_run(reversible,next,plane,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_wavelet_resolution_copy_observed(before:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,
    direction:crate::codestream::DecompositionDirection,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,request:Part2WaveletRequest,next:usize,plane:Part1ReconstructedPlane,result:Result<Part1PrepareFold,crate::DecodeError>)
    requires part2_wavelet_resolution_admit(before,bands,geometry,direction,reversible)==Ok((request,next)),
        part2_tier1_storage_framed(|calls|part2_wavelet_request_run(request,reversible,kernel,maximum,calls),Ok(plane)),
        plane.2==part1_prepare_fraction(reversible),part2_prepare_plane_copy_result(plane,next,result),
    ensures part2_wavelet_resolution_result(before,bands,geometry,direction,reversible,kernel,maximum,result),
{
    reveal(part2_wavelet_resolution_run);
    part2_tier1_storage_eta(|calls|part2_prepare_plane_copy_run(plane,next,calls),result);
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_request_run(request,reversible,kernel,maximum,calls),
        |plane:Part1ReconstructedPlane,rest|part2_wavelet_resolution_finish_run(reversible,next,plane,rest),Ok(plane),result);
}
pub(crate) proof fn part2_wavelet_fold_normal(initial:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,style:Part1PrepareStyle,
    reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_fold_run(initial,bands,geometry,style,reversible,kernel,maximum,count,calls),part2_prepare_fold(initial,bands,geometry,style,reversible,kernel,maximum,count)),
    decreases count,
{
    reveal(part2_wavelet_fold_run);reveal(part2_prepare_fold);
    let result=part2_prepare_fold(initial,bands,geometry,style,reversible,kernel,maximum,count);
    if count==0{part2_tier1_storage_pure(result);}else{
        let previous=part2_prepare_fold(initial,bands,geometry,style,reversible,kernel,maximum,(count-1) as nat);
        part2_wavelet_fold_normal(initial,bands,geometry,style,reversible,kernel,maximum,(count-1) as nat);
        if let Ok(before)=previous{
            match part1_direction_for_resolution(style.1,style.2,count as u8){
                Err(_)=>{part2_tier1_storage_pure(result);},Ok(direction)=>{
                    let transformed=if matches!(direction,crate::codestream::DecompositionDirection::None){Ok(before)}else{part2_prepare_resolution(before,bands,geometry,direction,reversible,kernel,maximum)};
                    if matches!(direction,crate::codestream::DecompositionDirection::None){part2_tier1_storage_pure(transformed);}
                    else{part2_wavelet_resolution_normal(before,bands,geometry,direction,reversible,kernel,maximum);
                        part2_tier1_storage_eta(|calls|part2_wavelet_resolution_run(before,bands,geometry,direction,reversible,kernel,maximum,calls),transformed);}
                    if transformed.is_ok(){part2_tier1_storage_pure(result);}
                    part2_tier1_storage_bind_frame(|calls|if matches!(direction,crate::codestream::DecompositionDirection::None){Some((Ok(before),calls))}else{part2_wavelet_resolution_run(before,bands,geometry,direction,reversible,kernel,maximum,calls)},
                        |after:Part1PrepareFold,rest|Some((if count>=255{Err(part1_block_placement_error(true))}else{Ok(after)},rest)),transformed,result);
                },
            }
        }
        part2_tier1_storage_bind_frame(|calls|part2_wavelet_fold_run(initial,bands,geometry,style,reversible,kernel,maximum,(count-1) as nat,calls),
            |before:Part1PrepareFold,rest|part2_wavelet_fold_next(before,bands,geometry,style,reversible,kernel,maximum,count,rest),previous,result);
    }
}
pub(crate) proof fn part2_wavelet_reconstruct_normal(bands:Seq<Part1WorkingSubbandModel>,plan:Part1PreparePlan,style:Part1PrepareStyle,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64)
    ensures part2_wavelet_reconstruct_result(bands,plan,style,reversible,kernel,maximum,part2_prepare_reconstruct(bands,plan,style,reversible,kernel,maximum)),
{
    if bands.len()==0{part2_tier1_storage_pure(part2_prepare_reconstruct(bands,plan,style,reversible,kernel,maximum));}
    else{let ll=bands[0];
        part2_prepare_initial_normal(ll);
        part2_wavelet_fold_normal((ll.0,ll.1,ll.3,1usize),bands,plan.subbands,style,reversible,kernel,maximum,plan.resolution as nat);
        part2_tier1_storage_eta(|calls|part2_wavelet_fold_run((ll.0,ll.1,ll.3,1usize),bands,plan.subbands,style,reversible,kernel,maximum,plan.resolution as nat,calls),
            part2_prepare_reconstruct(bands,plan,style,reversible,kernel,maximum));
        part2_wavelet_reconstruct_after_initial_observed(bands,plan,style,reversible,kernel,maximum,part2_prepare_reconstruct(bands,plan,style,reversible,kernel,maximum));}
}
pub(crate) proof fn part2_wavelet_reconstruct_after_initial_observed(bands:Seq<Part1WorkingSubbandModel>,plan:Part1PreparePlan,style:Part1PrepareStyle,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,result:Result<Part1PrepareFold,crate::DecodeError>)
    requires bands.len()>0,part2_prepare_initial_result(bands[0],Ok((bands[0].0,bands[0].1,bands[0].3,1usize))),
        part2_tier1_storage_framed(|calls|part2_wavelet_fold_run((bands[0].0,bands[0].1,bands[0].3,1usize),bands,plan.subbands,style,reversible,kernel,maximum,plan.resolution as nat,calls),result),
    ensures part2_wavelet_reconstruct_result(bands,plan,style,reversible,kernel,maximum,result),
{
    part2_tier1_storage_eta(|calls|part2_wavelet_fold_run((bands[0].0,bands[0].1,bands[0].3,1usize),bands,plan.subbands,style,reversible,kernel,maximum,plan.resolution as nat,calls),result);
    part2_tier1_storage_bind_frame(|calls|part2_prepare_initial_run(bands[0],calls),
        |initial:Part1PrepareFold,rest|part2_wavelet_fold_run(initial,bands,plan.subbands,style,reversible,kernel,maximum,plan.resolution as nat,rest),
        Ok((bands[0].0,bands[0].1,bands[0].3,1usize)),result);
}
pub(crate) proof fn part2_wavelet_reconstruct_initial_error(bands:Seq<Part1WorkingSubbandModel>,plan:Part1PreparePlan,style:Part1PrepareStyle,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,error:crate::DecodeError)
    requires bands.len()>0,part2_prepare_initial_result(bands[0],Err(error)),
    ensures part2_wavelet_reconstruct_result(bands,plan,style,reversible,kernel,maximum,Err(error)),
{
    part2_tier1_storage_bind_frame(|calls|part2_prepare_initial_run(bands[0],calls),
        |initial:Part1PrepareFold,rest|part2_wavelet_fold_run(initial,bands,plan.subbands,style,reversible,kernel,maximum,plan.resolution as nat,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_wavelet_fold_prefix_error(initial:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,style:Part1PrepareStyle,
    reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,prefix:nat,count:nat,error:crate::DecodeError)
    requires prefix<=count,part2_tier1_storage_framed(|calls|part2_wavelet_fold_run(initial,bands,geometry,style,reversible,kernel,maximum,prefix,calls),Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_fold_run(initial,bands,geometry,style,reversible,kernel,maximum,count,calls),Err(error)),
    decreases count-prefix,
{
    if prefix<count{
        reveal(part2_wavelet_fold_run);
        part2_wavelet_fold_prefix_error(initial,bands,geometry,style,reversible,kernel,maximum,prefix,(count-1) as nat,error);
        part2_tier1_storage_bind_frame(|calls|part2_wavelet_fold_run(initial,bands,geometry,style,reversible,kernel,maximum,(count-1) as nat,calls),
            |before:Part1PrepareFold,rest|part2_wavelet_fold_next(before,bands,geometry,style,reversible,kernel,maximum,count,rest),Err(error),Err(error));
    }
}
pub(crate) proof fn part2_wavelet_fold_resolution_error(initial:Part1PrepareFold,bands:Seq<Part1WorkingSubbandModel>,geometry:Seq<crate::decode::SubbandGeometry>,style:Part1PrepareStyle,
    reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,index:nat,before:Part1PrepareFold,direction:crate::codestream::DecompositionDirection,error:crate::DecodeError)
    requires index>0,index<=255,part2_prepare_fold(initial,bands,geometry,style,reversible,kernel,maximum,(index-1) as nat)==Ok(before),
        part1_direction_for_resolution(style.1,style.2,index as u8)==Ok(direction),!matches!(direction,crate::codestream::DecompositionDirection::None),
        part2_wavelet_resolution_result(before,bands,geometry,direction,reversible,kernel,maximum,Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_fold_run(initial,bands,geometry,style,reversible,kernel,maximum,index,calls),Err(error)),
{
    reveal(part2_wavelet_fold_run);
    part2_wavelet_fold_normal(initial,bands,geometry,style,reversible,kernel,maximum,(index-1) as nat);
    part2_tier1_storage_eta(|calls|part2_wavelet_resolution_run(before,bands,geometry,direction,reversible,kernel,maximum,calls),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_resolution_run(before,bands,geometry,direction,reversible,kernel,maximum,calls),
        |after:Part1PrepareFold,rest|Some((if index>=255{Err(part1_block_placement_error(true))}else{Ok(after)},rest)),Err(error),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_fold_run(initial,bands,geometry,style,reversible,kernel,maximum,(index-1) as nat,calls),
        |before:Part1PrepareFold,rest|part2_wavelet_fold_next(before,bands,geometry,style,reversible,kernel,maximum,index,rest),Ok(before),Err(error));
}
pub(crate) proof fn part2_wavelet_reconstruct_error(bands:Seq<Part1WorkingSubbandModel>,plan:Part1PreparePlan,style:Part1PrepareStyle,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,
    index:nat,before:Part1PrepareFold,direction:crate::codestream::DecompositionDirection,error:crate::DecodeError)
    requires bands.len()>0,index>0,index<=plan.resolution as nat,
        part2_prepare_initial_result(bands[0],Ok((bands[0].0,bands[0].1,bands[0].3,1usize))),
        part2_prepare_fold((bands[0].0,bands[0].1,bands[0].3,1usize),bands,plan.subbands,style,reversible,kernel,maximum,(index-1) as nat)==Ok(before),
        part1_direction_for_resolution(style.1,style.2,index as u8)==Ok(direction),!matches!(direction,crate::codestream::DecompositionDirection::None),
        part2_wavelet_resolution_result(before,bands,plan.subbands,direction,reversible,kernel,maximum,Err(error)),
    ensures part2_wavelet_reconstruct_result(bands,plan,style,reversible,kernel,maximum,Err(error)),
{
    let initial=(bands[0].0,bands[0].1,bands[0].3,1usize);
    part2_wavelet_fold_resolution_error(initial,bands,plan.subbands,style,reversible,kernel,maximum,index,before,direction,error);
    part2_wavelet_fold_prefix_error(initial,bands,plan.subbands,style,reversible,kernel,maximum,index,plan.resolution as nat,error);
    part2_tier1_storage_eta(|calls|part2_wavelet_fold_run(initial,bands,plan.subbands,style,reversible,kernel,maximum,plan.resolution as nat,calls),Err(error));
    part2_wavelet_reconstruct_after_initial_observed(bands,plan,style,reversible,kernel,maximum,Err(error));
}
pub(crate) proof fn part2_wavelet_reconstruct_frames(bands:Seq<Part1WorkingSubbandModel>,plan:Part1PreparePlan,style:Part1PrepareStyle,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,result:Result<Part1PrepareFold,crate::DecodeError>)
    requires part2_wavelet_reconstruct_result(bands,plan,style,reversible,kernel,maximum,result),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_reconstruct_run(bands,plan,style,reversible,kernel,maximum,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareFold>|
            (forall|calls| #[trigger] other(calls)==part2_wavelet_reconstruct_run(bands,plan,style,reversible,kernel,maximum,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{part2_tier1_storage_eta(|calls|part2_wavelet_reconstruct_run(bands,plan,style,reversible,kernel,maximum,calls),result);}
pub(crate) proof fn part2_wavelet_reconstruct_empty_error(bands:Seq<Part1WorkingSubbandModel>,plan:Part1PreparePlan,style:Part1PrepareStyle,reversible:bool,kernel:Option<Part2RawKernel>,maximum:u64,error:crate::DecodeError)
    requires bands.len()==0,part2_wavelet_reconstruct_result(bands,plan,style,reversible,kernel,maximum,Err(error)),
    ensures error==part1_block_placement_error(false),
{
    let run=|calls|part2_wavelet_reconstruct_run(bands,plan,style,reversible,kernel,maximum,calls);
    let prefix=choose|prefix| #[trigger] part2_tier1_storage_prefix(run,prefix,Err(error));
    part2_tier1_storage_at(run,prefix,Err(error),Seq::empty());
}
}
