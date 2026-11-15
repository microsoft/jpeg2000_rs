//! Ordered spectral pixels with exact partial components and admitted work.
use super::*;
verus! {
pub type Part2MctLinePixelsEffect=(Result<(),crate::DecodeError>,Seq<Part2MctComponent>);
pub type Part2MctLineEffect=(Result<(),crate::DecodeError>,Seq<Part2MctComponent>,u64);
pub(crate) open spec fn part2_mct_line_pixels_next(before:Part2MctLinePixelsEffect,prepared:Part2MctWaveletPreparation,index:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLinePixelsEffect> {
    if before.0.is_err(){Some((Ok(before),calls))}else if index>usize::MAX{Some((Ok((Err(part1_transform_error(true)),before.1)),calls))}
    else{part2_tier1_storage_bind(part2_mct_line_pixel_run(before.1,prepared,index as usize,calls),
        |pixel:Part2MctLinePixelEffect,rest|Some((Ok((pixel.0,pixel.1)),rest)))}
}
#[verifier::opaque]
pub(crate) open spec fn part2_mct_line_pixels_run(initial:Seq<Part2MctComponent>,prepared:Part2MctWaveletPreparation,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLinePixelsEffect>
    decreases count,
{
    if count==0{Some((Ok((Ok(()),initial)),calls))}else{
        part2_tier1_storage_bind(part2_mct_line_pixels_run(initial,prepared,(count-1) as nat,calls),
            |before:Part2MctLinePixelsEffect,rest|part2_mct_line_pixels_next(before,prepared,(count-1) as nat,rest))
    }
}
pub(crate) open spec fn part2_mct_line_wavelet_finish(prepared:Part2MctWaveletPreparation,work:u64,pixels:Part2MctLinePixelsEffect)->Part2MctLineEffect {
    match pixels.0{Err(error)=>(Err(error),pixels.1,work),Ok(())=>{
        let tagged=part2_mct_destination_precisions(pixels.1,prepared.1,if part2_mct_wavelet_reversible(prepared.7){0}else{32},prepared.1.len());
        (tagged.0,tagged.1,work)
    }}
}
pub(crate) open spec fn part2_mct_line_wavelet_run(before:Seq<Part2MctComponent>,collection:Part2MctCollection,work:u64,maximum_work:u64,maximum_bytes:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLineEffect> {
    let prepared=part2_mct_prepare_wavelet(before,collection,work,maximum_work,maximum_bytes);
    match prepared.0{
        Err(error)=>Some((Ok((Err(error),before,prepared.1)),calls)),
        Ok(plan)=>part2_tier1_storage_bind(part2_mct_line_pixels_run(before,plan,plan.5 as nat,calls),
            |pixels:Part2MctLinePixelsEffect,rest|Some((Ok(part2_mct_line_wavelet_finish(plan,prepared.1,pixels)),rest))),
    }
}
pub(crate) open spec fn part2_mct_line_wavelet_result(before:Seq<Part2MctComponent>,collection:Part2MctCollection,work:u64,maximum_work:u64,maximum_bytes:u64,result:Part2MctLineEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_line_wavelet_run(before,collection,work,maximum_work,maximum_bytes,calls),Ok(result))
}
pub(crate) proof fn part2_mct_line_pixels_normal(initial:Seq<Part2MctComponent>,prepared:Part2MctWaveletPreparation,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_mct_line_pixels_run(initial,prepared,count,calls),Ok(part2_mct_wavelet_pixels(initial,prepared,count))),
    decreases count,
{
    reveal(part2_mct_line_pixels_run);reveal(part2_mct_wavelet_pixels);
    let result=Ok(part2_mct_wavelet_pixels(initial,prepared,count));
    if count==0{part2_tier1_storage_pure(result);}else{
        let before=part2_mct_wavelet_pixels(initial,prepared,(count-1) as nat);
        part2_mct_line_pixels_normal(initial,prepared,(count-1) as nat);
        if before.0.is_err() || count-1>usize::MAX{part2_tier1_storage_pure(result);}else{
            let pixel=part2_mct_wavelet_pixel(before.1,prepared,(count-1) as usize);
            part2_mct_line_pixel_normal(before.1,prepared,(count-1) as usize);
            part2_tier1_storage_eta(|calls|part2_mct_line_pixel_run(before.1,prepared,(count-1) as usize,calls),Ok(pixel));
            part2_tier1_storage_pure(result);
            part2_tier1_storage_bind_frame(|calls|part2_mct_line_pixel_run(before.1,prepared,(count-1) as usize,calls),
                |pixel:Part2MctLinePixelEffect,rest|Some((Ok((pixel.0,pixel.1)),rest)),Ok(pixel),result);
        }
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_pixels_run(initial,prepared,(count-1) as nat,calls),
            |before:Part2MctLinePixelsEffect,rest|part2_mct_line_pixels_next(before,prepared,(count-1) as nat,rest),Ok(before),result);
    }
}
pub(crate) proof fn part2_mct_line_wavelet_normal(before:Seq<Part2MctComponent>,collection:Part2MctCollection,work:u64,maximum_work:u64,maximum_bytes:u64)
    ensures part2_mct_line_wavelet_result(before,collection,work,maximum_work,maximum_bytes,part2_mct_wavelet(before,collection,work,maximum_work,maximum_bytes)),
{
    let preparation=part2_mct_prepare_wavelet(before,collection,work,maximum_work,maximum_bytes);
    let result=Ok(part2_mct_wavelet(before,collection,work,maximum_work,maximum_bytes));
    match preparation.0{
        Err(_)=>{part2_tier1_storage_pure(result);},Ok(plan)=>{
            let pixels=part2_mct_wavelet_pixels(before,plan,plan.5 as nat);
            part2_mct_line_pixels_normal(before,plan,plan.5 as nat);part2_tier1_storage_pure(result);
            part2_tier1_storage_bind_frame(|calls|part2_mct_line_pixels_run(before,plan,plan.5 as nat,calls),
                |pixels:Part2MctLinePixelsEffect,rest|Some((Ok(part2_mct_line_wavelet_finish(plan,preparation.1,pixels)),rest)),Ok(pixels),result);
        },
    }
}
pub(crate) proof fn part2_mct_line_pixels_error(initial:Seq<Part2MctComponent>,prepared:Part2MctWaveletPreparation,prefix:nat,count:nat,effect:Part2MctLinePixelsEffect)
    requires prefix<=count,effect.0.is_err(),part2_tier1_storage_framed(|calls|part2_mct_line_pixels_run(initial,prepared,prefix,calls),Ok(effect)),
    ensures part2_tier1_storage_framed(|calls|part2_mct_line_pixels_run(initial,prepared,count,calls),Ok(effect)),
    decreases count-prefix,
{
    if prefix<count{reveal(part2_mct_line_pixels_run);
        part2_mct_line_pixels_error(initial,prepared,prefix,(count-1) as nat,effect);part2_tier1_storage_pure(Ok(effect));
        part2_tier1_storage_bind_frame(|calls|part2_mct_line_pixels_run(initial,prepared,(count-1) as nat,calls),
            |before:Part2MctLinePixelsEffect,rest|part2_mct_line_pixels_next(before,prepared,(count-1) as nat,rest),Ok(effect),Ok(effect));
    }
}
pub(crate) proof fn part2_mct_line_wavelet_pixel_error(initial:Seq<Part2MctComponent>,collection:Part2MctCollection,work:u64,maximum_work:u64,maximum_bytes:u64,prepared:Part2MctWaveletPreparation,admitted_work:u64,
    index:nat,before:Seq<Part2MctComponent>,pixel:Part2MctLinePixelEffect)
    requires part2_mct_prepare_wavelet(initial,collection,work,maximum_work,maximum_bytes)==(Ok(prepared),admitted_work),
        index<prepared.5,part2_mct_wavelet_pixels(initial,prepared,index)==(Ok(()),before),
        pixel.0.is_err(),part2_mct_line_pixel_result(before,prepared,index as usize,pixel),
    ensures part2_mct_line_wavelet_result(initial,collection,work,maximum_work,maximum_bytes,(pixel.0,pixel.1,admitted_work)),
{
    reveal(part2_mct_line_pixels_run);
    let effect=(pixel.0,pixel.1);
    part2_tier1_storage_eta(|calls|part2_mct_line_pixel_run(before,prepared,index as usize,calls),Ok(pixel));part2_tier1_storage_pure(Ok(effect));
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_pixel_run(before,prepared,index as usize,calls),
        |pixel:Part2MctLinePixelEffect,rest|Some((Ok((pixel.0,pixel.1)),rest)),Ok(pixel),Ok(effect));
    part2_mct_line_pixels_normal(initial,prepared,index);
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_pixels_run(initial,prepared,index,calls),
        |before:Part2MctLinePixelsEffect,rest|part2_mct_line_pixels_next(before,prepared,index,rest),Ok((Ok(()),before)),Ok(effect));
    part2_mct_line_pixels_error(initial,prepared,index+1,prepared.5 as nat,effect);
    let result=Ok::<Part2MctLineEffect,crate::DecodeError>((pixel.0,pixel.1,admitted_work));part2_tier1_storage_pure(result);
    part2_tier1_storage_bind_frame(|calls|part2_mct_line_pixels_run(initial,prepared,prepared.5 as nat,calls),
        |pixels:Part2MctLinePixelsEffect,rest|Some((Ok(part2_mct_line_wavelet_finish(prepared,admitted_work,pixels)),rest)),Ok(effect),result);
}
}
