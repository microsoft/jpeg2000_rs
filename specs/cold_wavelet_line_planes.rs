//! Ordered real line children within the already qualified matrix owners.
use super::*;
verus! {
pub(crate) open spec fn part2_wavelet_row_run(low:Part1WaveletBand,high:Part1WaveletBand,y:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    if kernel.is_none() && y != 0 {
        Some((part1_horizontal_row(low,high,y,first,irreversible),calls))
    } else { match part1_band_row(low,y){Err(error)=>Some((Err(error),calls)),Ok(a)=>match part1_band_row(high,y){
        Err(error)=>Some((Err(error),calls)),Ok(b)=>part2_wavelet_sequence_run(a,b,first,irreversible,kernel,calls),
    }} }
}
pub(crate) open spec fn part2_wavelet_row_value(low:Part1WaveletBand,high:Part1WaveletBand,y:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>)->Result<Seq<i64>,crate::DecodeError> {
    match kernel{None=>part1_horizontal_row(low,high,y,first,irreversible),Some(kernel)=>part2_atk_horizontal_row(low,high,y,first,kernel)}
}
pub(crate) open spec fn part2_wavelet_row_result(low:Part1WaveletBand,high:Part1WaveletBand,y:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_row_run(low,high,y,first,irreversible,kernel,calls),result)
}
pub(crate) open spec fn part2_wavelet_column_after_low(low:Seq<i64>,high:Part1WaveletBand,x:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_wavelet_gather_run(high,x,calls),
        |b:Seq<i64>,rest|part2_wavelet_sequence_run(low,b,first,irreversible,kernel,rest))
}
pub(crate) open spec fn part2_wavelet_column_run(low:Part1WaveletBand,high:Part1WaveletBand,x:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_wavelet_gather_run(low,x,calls),
        |a:Seq<i64>,rest|part2_wavelet_column_after_low(a,high,x,first,irreversible,kernel,rest))
}
pub(crate) open spec fn part2_wavelet_column_value(low:Part1WaveletBand,high:Part1WaveletBand,x:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>)->Result<Seq<i64>,crate::DecodeError> {
    match kernel{None=>part1_vertical_column(low,high,x,first,irreversible),Some(kernel)=>part2_atk_vertical_column(low,high,x,first,kernel)}
}
pub(crate) open spec fn part2_wavelet_column_result(low:Part1WaveletBand,high:Part1WaveletBand,x:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_wavelet_column_run(low,high,x,first,irreversible,kernel,calls),result)
}
pub(crate) open spec fn part2_wavelet_horizontal_lines_next(previous:Seq<i64>,low:Part1WaveletBand,high:Part1WaveletBand,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,y:nat,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_wavelet_row_run(low,high,y as u32,first,irreversible,kernel,calls),
        |row:Seq<i64>,rest|Some((Ok(previous+row),rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_horizontal_lines_run(low:Part1WaveletBand,high:Part1WaveletBand,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,count:nat,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>>
    decreases count,
{
    if count==0{Some((Ok(Seq::empty()),calls))}else{
        part2_tier1_storage_bind(part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,(count-1) as nat,calls),
            |previous:Seq<i64>,rest|part2_wavelet_horizontal_lines_next(previous,low,high,first,irreversible,kernel,(count-1) as nat,rest))
    }
}
pub(crate) open spec fn part2_wavelet_vertical_lines_next(previous:Seq<i64>,low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,x:nat,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_wavelet_column_run(low,high,x as u32,first,irreversible,kernel,calls),
        |column:Seq<i64>,rest|{let stored=part1_store_column_prefix(previous,low.0,x as u32,column,height as nat);
            Some((match stored.0{Err(error)=>Err(error),Ok(())=>Ok(stored.1)},rest))})
}
#[verifier::opaque]
pub(crate) open spec fn part2_wavelet_vertical_lines_run(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,count:nat,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>>
    decreases count,
{
    if count==0{Some((Ok(Seq::new(length as nat,|_:int|0i64)),calls))}else{
        part2_tier1_storage_bind(part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,(count-1) as nat,calls),
            |previous:Seq<i64>,rest|part2_wavelet_vertical_lines_next(previous,low,high,height,first,irreversible,kernel,(count-1) as nat,rest))
    }
}
pub(crate) proof fn part2_wavelet_row_normal(low:Part1WaveletBand,high:Part1WaveletBand,y:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>)
    ensures part2_wavelet_row_result(low,high,y,first,irreversible,kernel,part2_wavelet_row_value(low,high,y,first,irreversible,kernel)),
{
    let result=part2_wavelet_row_value(low,high,y,first,irreversible,kernel);
    if kernel.is_none() && y != 0 { part2_tier1_storage_pure(result); }
    else { match part1_band_row(low,y){Err(_)=>{part2_tier1_storage_pure(result);},Ok(a)=>match part1_band_row(high,y){
        Err(_)=>{part2_tier1_storage_pure(result);},Ok(b)=>{
            part2_wavelet_sequence_normal(a,b,first,irreversible,kernel);
            part2_wavelet_sequence_frames(a,b,first,irreversible,kernel,result);
        },
    }} }
}
pub(crate) proof fn part2_wavelet_column_normal(low:Part1WaveletBand,high:Part1WaveletBand,x:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>)
    ensures part2_wavelet_column_result(low,high,x,first,irreversible,kernel,part2_wavelet_column_value(low,high,x,first,irreversible,kernel)),
{
    let result=part2_wavelet_column_value(low,high,x,first,irreversible,kernel);
    let a=part1_collect_column(low,x);let b=part1_collect_column(high,x);
    part2_wavelet_gather_normal(low,x);part2_wavelet_gather_frames(low,x,a);
    if let Ok(a)=a{
        part2_wavelet_gather_normal(high,x);part2_wavelet_gather_frames(high,x,b);
        if let Ok(b)=b{part2_wavelet_sequence_normal(a,b,first,irreversible,kernel);part2_wavelet_sequence_frames(a,b,first,irreversible,kernel,result);}
        part2_tier1_storage_bind_frame(|calls|part2_wavelet_gather_run(high,x,calls),
            |b:Seq<i64>,rest|part2_wavelet_sequence_run(a,b,first,irreversible,kernel,rest),b,result);
        part2_tier1_storage_eta(|calls|part2_wavelet_column_after_low(a,high,x,first,irreversible,kernel,calls),result);
    }
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_gather_run(low,x,calls),
        |a:Seq<i64>,rest|part2_wavelet_column_after_low(a,high,x,first,irreversible,kernel,rest),a,result);
}
pub(crate) proof fn part2_wavelet_row_child_observed(low:Part1WaveletBand,high:Part1WaveletBand,y:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,a:Seq<i64>,b:Seq<i64>,result:Result<Seq<i64>,crate::DecodeError>)
    requires kernel.is_some() || y == 0,
        part1_band_row(low,y)==Ok(a),part1_band_row(high,y)==Ok(b),part2_wavelet_sequence_result(a,b,first,irreversible,kernel,result),
    ensures part2_wavelet_row_result(low,high,y,first,irreversible,kernel,result),
{part2_wavelet_sequence_frames(a,b,first,irreversible,kernel,result);}
pub(crate) proof fn part2_wavelet_column_low_error(low:Part1WaveletBand,high:Part1WaveletBand,x:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,error:crate::DecodeError)
    requires part2_wavelet_gather_result(low,x,Err(error)),
    ensures part2_wavelet_column_result(low,high,x,first,irreversible,kernel,Err(error)),
{
    part2_wavelet_gather_frames(low,x,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_gather_run(low,x,calls),|a:Seq<i64>,rest|part2_wavelet_column_after_low(a,high,x,first,irreversible,kernel,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_wavelet_column_low_join(low:Part1WaveletBand,high:Part1WaveletBand,x:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,a:Seq<i64>,result:Result<Seq<i64>,crate::DecodeError>)
    requires part1_collect_column(low,x)==Ok(a),part2_tier1_storage_framed(|calls|part2_wavelet_column_after_low(a,high,x,first,irreversible,kernel,calls),result),
    ensures part2_wavelet_column_result(low,high,x,first,irreversible,kernel,result),
{
    part2_wavelet_gather_normal(low,x);part2_wavelet_gather_frames(low,x,Ok(a));
    part2_tier1_storage_eta(|calls|part2_wavelet_column_after_low(a,high,x,first,irreversible,kernel,calls),result);
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_gather_run(low,x,calls),|a:Seq<i64>,rest|part2_wavelet_column_after_low(a,high,x,first,irreversible,kernel,rest),Ok(a),result);
}
pub(crate) proof fn part2_wavelet_column_high_error(low:Part1WaveletBand,high:Part1WaveletBand,x:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,a:Seq<i64>,error:crate::DecodeError)
    requires part1_collect_column(low,x)==Ok(a),part2_wavelet_gather_result(high,x,Err(error)),
    ensures part2_wavelet_column_result(low,high,x,first,irreversible,kernel,Err(error)),
{
    part2_wavelet_gather_frames(high,x,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_gather_run(high,x,calls),|b:Seq<i64>,rest|part2_wavelet_sequence_run(a,b,first,irreversible,kernel,rest),Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_wavelet_column_after_low(a,high,x,first,irreversible,kernel,calls),Err(error));
    part2_wavelet_column_low_join(low,high,x,first,irreversible,kernel,a,Err(error));
}
pub(crate) proof fn part2_wavelet_column_sequence_observed(low:Part1WaveletBand,high:Part1WaveletBand,x:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,a:Seq<i64>,b:Seq<i64>,result:Result<Seq<i64>,crate::DecodeError>)
    requires part1_collect_column(low,x)==Ok(a),part1_collect_column(high,x)==Ok(b),part2_wavelet_sequence_result(a,b,first,irreversible,kernel,result),
    ensures part2_wavelet_column_result(low,high,x,first,irreversible,kernel,result),
{
    part2_wavelet_sequence_frames(a,b,first,irreversible,kernel,result);
    part2_wavelet_gather_normal(high,x);part2_wavelet_gather_frames(high,x,Ok(b));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_gather_run(high,x,calls),|b:Seq<i64>,rest|part2_wavelet_sequence_run(a,b,first,irreversible,kernel,rest),Ok(b),result);
    part2_tier1_storage_eta(|calls|part2_wavelet_column_after_low(a,high,x,first,irreversible,kernel,calls),result);
    part2_wavelet_column_low_join(low,high,x,first,irreversible,kernel,a,result);
}
pub(crate) proof fn part2_wavelet_horizontal_lines_normal(low:Part1WaveletBand,high:Part1WaveletBand,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,count,calls),
        match kernel{None=>part1_horizontal_prefix(low,high,first,irreversible,count),Some(kernel)=>part2_atk_horizontal_prefix(low,high,first,kernel,count)}),
    decreases count,
{
    reveal(part2_wavelet_horizontal_lines_run);
    let result=match kernel{None=>part1_horizontal_prefix(low,high,first,irreversible,count),Some(kernel)=>part2_atk_horizontal_prefix(low,high,first,kernel,count)};
    if count==0{part2_tier1_storage_pure(result);}else{
        let previous=match kernel{None=>part1_horizontal_prefix(low,high,first,irreversible,(count-1) as nat),Some(kernel)=>part2_atk_horizontal_prefix(low,high,first,kernel,(count-1) as nat)};
        part2_wavelet_horizontal_lines_normal(low,high,first,irreversible,kernel,(count-1) as nat);
        if let Ok(prefix)=previous{
            let row=part2_wavelet_row_value(low,high,(count-1) as u32,first,irreversible,kernel);
            part2_wavelet_row_normal(low,high,(count-1) as u32,first,irreversible,kernel);
            part2_tier1_storage_eta(|calls|part2_wavelet_row_run(low,high,(count-1) as u32,first,irreversible,kernel,calls),row);
            if row.is_ok(){part2_tier1_storage_pure(result);}
            part2_tier1_storage_bind_frame(|calls|part2_wavelet_row_run(low,high,(count-1) as u32,first,irreversible,kernel,calls),
                |row:Seq<i64>,rest|Some((Ok(prefix+row),rest)),row,result);
        }
        part2_tier1_storage_bind_frame(|calls|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,(count-1) as nat,calls),
            |previous:Seq<i64>,rest|part2_wavelet_horizontal_lines_next(previous,low,high,first,irreversible,kernel,(count-1) as nat,rest),previous,result);
    }
}
pub(crate) proof fn part2_wavelet_vertical_lines_normal(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,count,calls),
        match kernel{None=>part1_vertical_prefix(low,high,height,first,irreversible,length,count),Some(kernel)=>part2_atk_vertical_prefix(low,high,height,first,kernel,length,count)}),
    decreases count,
{
    reveal(part2_wavelet_vertical_lines_run);
    let result=match kernel{None=>part1_vertical_prefix(low,high,height,first,irreversible,length,count),Some(kernel)=>part2_atk_vertical_prefix(low,high,height,first,kernel,length,count)};
    if count==0{part2_tier1_storage_pure(result);}else{
        let previous=match kernel{None=>part1_vertical_prefix(low,high,height,first,irreversible,length,(count-1) as nat),Some(kernel)=>part2_atk_vertical_prefix(low,high,height,first,kernel,length,(count-1) as nat)};
        part2_wavelet_vertical_lines_normal(low,high,height,first,irreversible,kernel,length,(count-1) as nat);
        if let Ok(prefix)=previous{
            let column=part2_wavelet_column_value(low,high,(count-1) as u32,first,irreversible,kernel);
            part2_wavelet_column_normal(low,high,(count-1) as u32,first,irreversible,kernel);
            part2_tier1_storage_eta(|calls|part2_wavelet_column_run(low,high,(count-1) as u32,first,irreversible,kernel,calls),column);
            if column.is_ok(){part2_tier1_storage_pure(result);}
            part2_tier1_storage_bind_frame(|calls|part2_wavelet_column_run(low,high,(count-1) as u32,first,irreversible,kernel,calls),
                |column:Seq<i64>,rest|{let stored=part1_store_column_prefix(prefix,low.0,(count-1) as u32,column,height as nat);Some((match stored.0{Err(error)=>Err(error),Ok(())=>Ok(stored.1)},rest))},column,result);
        }
        part2_tier1_storage_bind_frame(|calls|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,(count-1) as nat,calls),
            |previous:Seq<i64>,rest|part2_wavelet_vertical_lines_next(previous,low,high,height,first,irreversible,kernel,(count-1) as nat,rest),previous,result);
    }
}
pub(crate) proof fn part2_wavelet_horizontal_prefix_error(low:Part1WaveletBand,high:Part1WaveletBand,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,prefix:nat,count:nat,error:crate::DecodeError)
    requires prefix<=count,part2_tier1_storage_framed(|calls|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,prefix,calls),Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,count,calls),Err(error)),
    decreases count-prefix,
{
    if prefix<count{reveal(part2_wavelet_horizontal_lines_run);
        part2_wavelet_horizontal_prefix_error(low,high,first,irreversible,kernel,prefix,(count-1) as nat,error);
        part2_tier1_storage_bind_frame(|calls|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,(count-1) as nat,calls),
            |previous:Seq<i64>,rest|part2_wavelet_horizontal_lines_next(previous,low,high,first,irreversible,kernel,(count-1) as nat,rest),Err(error),Err(error));
    }
}
pub(crate) proof fn part2_wavelet_vertical_prefix_error(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,prefix:nat,count:nat,error:crate::DecodeError)
    requires prefix<=count,part2_tier1_storage_framed(|calls|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,prefix,calls),Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,count,calls),Err(error)),
    decreases count-prefix,
{
    if prefix<count{reveal(part2_wavelet_vertical_lines_run);
        part2_wavelet_vertical_prefix_error(low,high,height,first,irreversible,kernel,length,prefix,(count-1) as nat,error);
        part2_tier1_storage_bind_frame(|calls|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,(count-1) as nat,calls),
            |previous:Seq<i64>,rest|part2_wavelet_vertical_lines_next(previous,low,high,height,first,irreversible,kernel,(count-1) as nat,rest),Err(error),Err(error));
    }
}
pub(crate) proof fn part2_wavelet_rows_child_error(low:Part1WaveletBand,high:Part1WaveletBand,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,capacity:usize,y:nat,previous:Seq<i64>,error:crate::DecodeError)
    requires y<low.1,part2_wavelet_row_result(low,high,y as u32,first,irreversible,kernel,Err(error)),
        (match kernel{None=>part1_horizontal_prefix(low,high,first,irreversible,y),Some(kernel)=>part2_atk_horizontal_prefix(low,high,first,kernel,y)})==Ok(previous),
    ensures part2_wavelet_rows_result(low,high,first,irreversible,kernel,capacity,Err(error)),
{
    reveal(part2_wavelet_rows_run);reveal(part2_wavelet_horizontal_lines_run);
    part2_tier1_storage_eta(|calls|part2_wavelet_row_run(low,high,y as u32,first,irreversible,kernel,calls),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_row_run(low,high,y as u32,first,irreversible,kernel,calls),
        |row:Seq<i64>,rest|Some((Ok(previous+row),rest)),Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_wavelet_horizontal_lines_next(previous,low,high,first,irreversible,kernel,y,calls),Err(error));
    part2_wavelet_horizontal_lines_normal(low,high,first,irreversible,kernel,y);
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,y,calls),
        |previous:Seq<i64>,rest|part2_wavelet_horizontal_lines_next(previous,low,high,first,irreversible,kernel,y,rest),Ok(previous),Err(error));
    part2_wavelet_horizontal_prefix_error(low,high,first,irreversible,kernel,y+1,low.1 as nat,error);
    part2_tier1_storage_eta(|calls|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,low.1 as nat,calls),Err(error));
    part2_wavelet_capacity_observed(Part2WaveletPlaneOwner::Rows,capacity as nat,Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Rows,capacity as nat,calls),
        |_:(),rest|part2_wavelet_horizontal_lines_run(low,high,first,irreversible,kernel,low.1 as nat,rest),Ok(()),Err(error));
}
pub(crate) proof fn part2_wavelet_columns_child_error(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,irreversible:bool,kernel:Option<Part2RawKernel>,length:usize,x:nat,previous:Seq<i64>,error:crate::DecodeError)
    requires x<low.0,part2_wavelet_column_result(low,high,x as u32,first,irreversible,kernel,Err(error)),
        (match kernel{None=>part1_vertical_prefix(low,high,height,first,irreversible,length,x),Some(kernel)=>part2_atk_vertical_prefix(low,high,height,first,kernel,length,x)})==Ok(previous),
    ensures part2_wavelet_scalar_columns_result(low,high,height,first,irreversible,kernel,length,Err(error)),
{
    reveal(part2_wavelet_scalar_columns_run);reveal(part2_wavelet_vertical_lines_run);
    part2_tier1_storage_eta(|calls|part2_wavelet_column_run(low,high,x as u32,first,irreversible,kernel,calls),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_column_run(low,high,x as u32,first,irreversible,kernel,calls),
        |column:Seq<i64>,rest|{let stored=part1_store_column_prefix(previous,low.0,x as u32,column,height as nat);Some((match stored.0{Err(error)=>Err(error),Ok(())=>Ok(stored.1)},rest))},Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_wavelet_vertical_lines_next(previous,low,high,height,first,irreversible,kernel,x,calls),Err(error));
    part2_wavelet_vertical_lines_normal(low,high,height,first,irreversible,kernel,length,x);
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,x,calls),
        |previous:Seq<i64>,rest|part2_wavelet_vertical_lines_next(previous,low,high,height,first,irreversible,kernel,x,rest),Ok(previous),Err(error));
    part2_wavelet_vertical_prefix_error(low,high,height,first,irreversible,kernel,length,x+1,low.0 as nat,error);
    part2_tier1_storage_eta(|calls|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,low.0 as nat,calls),Err(error));
    part2_wavelet_capacity_observed(Part2WaveletPlaneOwner::Columns,length as nat,Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Columns,length as nat,calls),
        |_:(),rest|part2_wavelet_vertical_lines_run(low,high,height,first,irreversible,kernel,length,low.0 as nat,rest),Ok(()),Err(error));
}
}
