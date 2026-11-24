//! Independently bounded Q16 vertical 9/7 traversal.
use super::*;
verus! {
pub(crate) proof fn rowwise_q16_shift_bound(adjusted:i64,bound:i64)
    requires 0<=bound<=8796093022208,
        -(bound as int)*65536<=adjusted<((bound as int)+1)*65536,
    ensures -bound<=adjusted>>16<=bound,
{
    let lower=(-(bound as int)*65536) as i64;
    let upper=(((bound as int)+1)*65536-1) as i64;
    assert((lower>>16)<=(adjusted>>16)<=(upper>>16)) by(bit_vector)
        requires lower<=adjusted<=upper;
    assert((lower>>16)==-bound && (upper>>16)==bound) by(bit_vector)
        requires 0<=bound<=8796093022208,
            lower==(-(bound as int)*65536) as i64,
            upper==(((bound as int)+1)*65536-1) as i64;
}
pub(crate) proof fn rowwise_fixed_product_bound(value:i64,factor:i64,bound:i64)
    requires 0<bound<=4398046511104,-bound<=value<=bound,-131071<=factor<=131071,
    ensures part1_fixed_product(value,factor).is_ok(),
        -2*(bound as int)<=part1_fixed_product(value,factor).get_Ok_0()<=2*(bound as int),
{
    let product=(value as int)*(factor as int);
    assert(-(bound as int)*131071<=product<=(bound as int)*131071) by(nonlinear_arith)
        requires product==(value as int)*(factor as int),0<bound,-bound<=value<=bound,-131071<=factor<=131071;
    assert(i64::MIN<=product<=i64::MAX && i64::MIN<=product+32768<=i64::MAX) by(nonlinear_arith)
        requires 0<bound<=4398046511104,-(bound as int)*131071<=product<=(bound as int)*131071;
    assert(-2*(bound as int)*65536<=product+32768<(2*(bound as int)+1)*65536) by(nonlinear_arith)
        requires 0<bound,-(bound as int)*131071<=product<=(bound as int)*131071;
    rowwise_q16_shift_bound((product+32768) as i64,(2*(bound as int)) as i64);
}
pub(crate) open spec fn rowwise_fixed_bound(stage:nat)->int {
    if stage==0{4294967296}else if stage==1{34359738368}
    else if stage==2{274877906944}else if stage==3{2199023255552}else{17592186044416}
}
pub(crate) open spec fn fixed_stage_bounded(samples:Seq<i64>, stage:nat)->bool {
    forall|i:int| 0<=i<samples.len() ==>
        -rowwise_fixed_bound(stage)<=#[trigger] samples[i]<=rowwise_fixed_bound(stage)
}
pub(crate) open spec fn fixed_scaled_parity_bounded(samples:Seq<i64>, even:bool, end:nat)->bool {
    forall|i:int| 0<=i<end && (i%2==0)==even ==> -1073741824<=#[trigger] samples[i]<=1073741824
}
pub(crate) open spec fn fixed_scale_result(
    samples:Seq<i64>, even:bool, factor:i64, track:bool,
) -> (Result<bool, crate::DecodeError>, Seq<i64>) {
    let (status, after) = part1_scaling_prefix(samples,even,factor,samples.len());
    (match status {
        Ok(()) => Ok(!track || fixed_scaled_parity_bounded(after,even,after.len())),
        Err(error) => Err(error),
    }, after)
}

pub(crate) proof fn fixed_scaled_parity_step(
    before:Seq<i64>, after:Seq<i64>, even:bool, index:nat,
)
    requires index<before.len(), after.len()==before.len(),
        forall|i:int| 0<=i<before.len() && i!=index ==> #[trigger] after[i]==before[i],
    ensures fixed_scaled_parity_bounded(after,even,index+1) ==
        (fixed_scaled_parity_bounded(before,even,index) &&
            ((index%2==0)!=even || -1073741824<=after[index as int]<=1073741824)),
{
    if fixed_scaled_parity_bounded(after,even,index+1) {
        assert forall|i:int| 0<=i<index && (i%2==0)==even implies
            -1073741824<=#[trigger] before[i]<=1073741824 by { assert(after[i]==before[i]); }
        if (index%2==0)==even { assert(-1073741824<=after[index as int]<=1073741824); }
    }
    if fixed_scaled_parity_bounded(before,even,index) &&
        ((index%2==0)!=even || -1073741824<=after[index as int]<=1073741824) {
        assert forall|i:int| 0<=i<index+1 && (i%2==0)==even implies
            -1073741824<=#[trigger] after[i]<=1073741824 by {
            if i<index { assert(after[i]==before[i]); }
        }
    }
}

pub(crate) proof fn fixed_scaled_row_admission(low:Seq<i64>, both:Seq<i64>, first:bool)
    requires low.len()==both.len(),
        forall|i:int| 0<=i<both.len() && (i%2==0)==first ==> #[trigger] both[i]==low[i],
    ensures rowwise_bounded(both) ==
        (fixed_scaled_parity_bounded(low,first,low.len()) && fixed_scaled_parity_bounded(both,!first,both.len())),
{
    if rowwise_bounded(both) {
        assert forall|i:int| 0<=i<low.len() && (i%2==0)==first implies
            -1073741824<=#[trigger] low[i]<=1073741824 by { assert(both[i]==low[i]); }
    }
    if fixed_scaled_parity_bounded(low,first,low.len()) && fixed_scaled_parity_bounded(both,!first,both.len()) {
        assert forall|i:int| 0<=i<both.len() implies -1073741824<=#[trigger] both[i]<=1073741824 by {
            if (i%2==0)==first { assert(both[i]==low[i]); }
        }
    }
}
pub(crate) proof fn fixed_stage_bound_grows(stage:nat)
    requires stage<4,
    ensures rowwise_fixed_bound(stage)<=rowwise_fixed_bound(stage+1),
{
    if stage==0 {} else if stage==1 {} else if stage==2 {} else { assert(stage==3); }
}
pub(crate) open spec fn rowwise_scale_bound(low:bool)->int {
    if low{1073741824}else{2147483648}
}
pub(crate) open spec fn rowwise_scaled(samples:Seq<i64>,width:nat,target:bool,factor:i64)->Seq<i64> {
    Seq::new(samples.len(),|i:int|if ((i/(width as int))%2==0)==target{
        part1_fixed_product(samples[i],factor).get_Ok_0()
    }else{samples[i]})
}
pub(crate) open spec fn rowwise_fixed_neighbors(current:i64,left:i64,right:i64,stage:u8)->Result<i64,crate::DecodeError> {
    part1_lifting_sample(seq![left,current,right],1,false,2,part1_nine_seven_lift(stage))
}
pub(crate) open spec fn rowwise_fixed_value(samples:Seq<i64>,width:nat,height:nat,y:nat,x:nat,stage:u8)->i64 {
    let left=if y==0{width as int}else{(y-1)*width};
    let right=if y+1<height{((y+1)*width) as int}else{(y-1)*width};
    rowwise_fixed_neighbors(samples[(y*width+x) as int],samples[(left+x) as int],samples[(right+x) as int],stage).get_Ok_0()
}
pub(crate) open spec fn rowwise_fixed_stage(samples:Seq<i64>,width:nat,height:nat,target:bool,stage:u8)->Seq<i64> {
    Seq::new(samples.len(),|i:int|if ((i/(width as int))%2==0)==target {
        rowwise_fixed_value(samples,width,height,(i/(width as int)) as nat,(i%(width as int)) as nat,stage)
    }else{samples[i]})
}
pub(crate) open spec fn rowwise_fixed_lifts(samples:Seq<i64>,width:nat,height:nat,first:bool,count:nat)->Seq<i64>
    decreases count,
{
    if count==0{samples}else{
        rowwise_fixed_stage(rowwise_fixed_lifts(samples,width,height,first,(count-1) as nat),
            width,height,if count%2==1{first}else{!first},(count-1) as u8)
    }
}
pub(crate) open spec fn rowwise_fixed_output(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool)->Seq<i64> {
    let samples=rowwise_interleaved(low,high,height,first);
    let a=rowwise_scaled(samples,low.0 as nat,first,part1_nine_seven_scale(true));
    let b=rowwise_scaled(a,low.0 as nat,!first,part1_nine_seven_scale(false));
    rowwise_fixed_lifts(b,low.0 as nat,height as nat,first,4)
}
pub(crate) proof fn rowwise_fixed_neighbors_bound(current:i64,left:i64,right:i64,stage:u8)
    requires stage<4,
        -rowwise_fixed_bound(stage as nat)<=current<=rowwise_fixed_bound(stage as nat),
        -rowwise_fixed_bound(stage as nat)<=left<=rowwise_fixed_bound(stage as nat),
        -rowwise_fixed_bound(stage as nat)<=right<=rowwise_fixed_bound(stage as nat),
    ensures rowwise_fixed_neighbors(current,left,right,stage).is_ok(),
        -rowwise_fixed_bound(stage as nat+1)<=rowwise_fixed_neighbors(current,left,right,stage).get_Ok_0()<=rowwise_fixed_bound(stage as nat+1),
{
    let bound=rowwise_fixed_bound(stage as nat);
    if stage==0{}else if stage==1{}else if stage==2{}else{assert(stage==3);}
    assert(rowwise_fixed_bound(stage as nat+1)==8*bound);
    let sum=((left as int)+(right as int)) as i64;
    rowwise_fixed_product_bound(sum,part1_nine_seven_lift(stage),(2*bound) as i64);
}
pub(crate) proof fn rowwise_fixed_frame(original:Seq<i64>,current:Seq<i64>,width:nat,height:nat,y:nat,x:nat,target:bool,stage:u8)
    requires width>0,height>1,y<height,x<width,(y%2==0)==target,
        original.len()==current.len(),width*height==original.len(),
        forall|i:int|0<=i<current.len()==>#[trigger] current[i]==if i<y*width+x{
            rowwise_fixed_stage(original,width,height,target,stage)[i]
        }else{original[i]},
    ensures
        current[(y*width+x) as int]==original[(y*width+x) as int],
        current[((if y==0{1nat}else{(y-1) as nat})*width+x) as int]
            ==original[((if y==0{1nat}else{(y-1) as nat})*width+x) as int],
        current[((if y+1<height{y+1}else{(y-1) as nat})*width+x) as int]
            ==original[((if y+1<height{y+1}else{(y-1) as nat})*width+x) as int],
        rowwise_fixed_stage(original,width,height,target,stage)[(y*width+x) as int]
            ==rowwise_fixed_value(original,width,height,y,x,stage),
{
    let left=if y==0{1nat}else{(y-1) as nat};
    let right=if y+1<height{y+1}else{(y-1) as nat};
    rowwise_cell(y as int,x as int,width as int,height as int);
    rowwise_cell(left as int,x as int,width as int,height as int);
    rowwise_cell(right as int,x as int,width as int,height as int);
    rowwise_index(y as int,x as int,width as int);
    rowwise_index(left as int,x as int,width as int);
    rowwise_index(right as int,x as int,width as int);
    assert((left%2==0)!=target && (right%2==0)!=target);
}
pub(crate) proof fn rowwise_fixed_stage_bound(samples:Seq<i64>,width:nat,height:nat,target:bool,stage:u8)
    requires width>0,height>1,width*height==samples.len(),stage<4,
        forall|i:int|0<=i<samples.len()==>-rowwise_fixed_bound(stage as nat)<=#[trigger] samples[i]<=rowwise_fixed_bound(stage as nat),
    ensures forall|i:int|0<=i<samples.len()==>-rowwise_fixed_bound(stage as nat+1)
        <=#[trigger] rowwise_fixed_stage(samples,width,height,target,stage)[i]<=rowwise_fixed_bound(stage as nat+1),
{
    assert forall|i:int|0<=i<samples.len() implies -rowwise_fixed_bound(stage as nat+1)
        <=#[trigger] rowwise_fixed_stage(samples,width,height,target,stage)[i]<=rowwise_fixed_bound(stage as nat+1) by{
        rowwise_coordinates(i,width as int,height as int);
        let y=(i/(width as int)) as nat;let x=(i%(width as int)) as nat;
        if (y%2==0)==target{
            let left=if y==0{1nat}else{(y-1) as nat};
            let right=if y+1<height{y+1}else{(y-1) as nat};
            rowwise_cell(left as int,x as int,width as int,height as int);
            rowwise_cell(right as int,x as int,width as int,height as int);
            rowwise_fixed_neighbors_bound(samples[i],samples[(left*width+x) as int],samples[(right*width+x) as int],stage);
            assert(i==y*width+x);
            assert(rowwise_fixed_stage(samples,width,height,target,stage)[i]
                ==rowwise_fixed_neighbors(samples[i],samples[(left*width+x) as int],samples[(right*width+x) as int],stage).get_Ok_0());
        }else{if stage==0{}else if stage==1{}else if stage==2{}else{}}
    }
}
    pub(crate) proof fn rowwise_fixed_lifts_length(samples:Seq<i64>,width:nat,height:nat,first:bool,count:nat)
        ensures rowwise_fixed_lifts(samples,width,height,first,count).len()==samples.len(),
        decreases count,
    {
        if count>0{rowwise_fixed_lifts_length(samples,width,height,first,(count-1) as nat);}
    }
    pub(crate) proof fn rowwise_fixed_output_length(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize)
        requires rowwise_eligible(low,high,height,first,length),
        ensures rowwise_fixed_output(low,high,height,first).len()==length,
    {
        let a=rowwise_scaled(rowwise_interleaved(low,high,height,first),low.0 as nat,first,part1_nine_seven_scale(true));
        let b=rowwise_scaled(a,low.0 as nat,!first,part1_nine_seven_scale(false));
        rowwise_fixed_lifts_length(b,low.0 as nat,height as nat,first,4);
    }
pub(crate) proof fn rowwise_scaled_bound(samples:Seq<i64>,width:nat,height:nat,target:bool,low:bool)
    requires width>0,width*height==samples.len(),
        forall|i:int|0<=i<samples.len()==>-rowwise_scale_bound(low)<=#[trigger] samples[i]<=rowwise_scale_bound(low),
    ensures forall|i:int|0<=i<samples.len()==>-2*rowwise_scale_bound(low)
        <=#[trigger] rowwise_scaled(samples,width,target,part1_nine_seven_scale(low))[i]<=2*rowwise_scale_bound(low),
{
    assert forall|i:int|0<=i<samples.len() implies -2*rowwise_scale_bound(low)
        <=#[trigger] rowwise_scaled(samples,width,target,part1_nine_seven_scale(low))[i]<=2*rowwise_scale_bound(low) by{
        if ((i/(width as int))%2==0)==target{
            rowwise_fixed_product_bound(samples[i],part1_nine_seven_scale(low),rowwise_scale_bound(low) as i64);
        }
    }
}
    pub(crate) proof fn rowwise_scaling_prefix(samples:Seq<i64>,target:bool,factor:i64,count:nat)
        requires count<=samples.len(),
            forall|i:nat|i<samples.len() && (i%2==0)==target ==> #[trigger] part1_fixed_product(samples[i as int],factor).is_ok(),
        ensures part1_scaling_prefix(samples,target,factor,count)==(Ok(()),
            Seq::new(samples.len(),|i:int|if i<count && (i%2==0)==target{part1_fixed_product(samples[i],factor).get_Ok_0()}else{samples[i]})),
        decreases count,
    {
        reveal_with_fuel(part1_scaling_prefix,2);
        if count>0{
            rowwise_scaling_prefix(samples,target,factor,(count-1) as nat);
            let previous=Seq::new(samples.len(),|i:int|if i<count-1 && (i%2==0)==target{part1_fixed_product(samples[i],factor).get_Ok_0()}else{samples[i]});
            let next=Seq::new(samples.len(),|i:int|if i<count && (i%2==0)==target{part1_fixed_product(samples[i],factor).get_Ok_0()}else{samples[i]});
            if ((count-1)%2==0)==target{
                assert(part1_fixed_product(samples[count-1],factor).is_ok());
                assert(previous.update(count-1,part1_fixed_product(samples[count-1],factor).get_Ok_0()) =~=next);
            }else{assert(previous =~=next);}
        }else{
            assert(samples =~=Seq::new(samples.len(),|i:int|if i<count && (i%2==0)==target{part1_fixed_product(samples[i],factor).get_Ok_0()}else{samples[i]}));
        }
    }
    pub(crate) proof fn rowwise_scaled_column(samples:Seq<i64>,width:u32,height:u32,x:u32,target:bool,low:bool)
        requires width>0,x<width,(width as int)*(height as int)==samples.len(),
            forall|i:int|0<=i<samples.len()==>-rowwise_scale_bound(low)<=#[trigger] samples[i]<=rowwise_scale_bound(low),
        ensures part1_scaling_prefix(rowwise_column(samples,width as nat,height as nat,x as nat),target,part1_nine_seven_scale(low),height as nat)
            ==(Ok(()),rowwise_column(rowwise_scaled(samples,width as nat,target,part1_nine_seven_scale(low)),width as nat,height as nat,x as nat)),
    {
        let column=rowwise_column(samples,width as nat,height as nat,x as nat);
        let factor=part1_nine_seven_scale(low);
        assert forall|y:nat|y<height && (y%2==0)==target implies #[trigger] part1_fixed_product(column[y as int],factor).is_ok() by{
            rowwise_cell(y as int,x as int,width as int,height as int);
            rowwise_fixed_product_bound(column[y as int],factor,rowwise_scale_bound(low) as i64);
        }
        rowwise_scaling_prefix(column,target,factor,height as nat);
        assert(Seq::new(column.len(),|y:int|if (y%2==0)==target{part1_fixed_product(column[y],factor).get_Ok_0()}else{column[y]})
            =~=rowwise_column(rowwise_scaled(samples,width as nat,target,factor),width as nat,height as nat,x as nat)) by{
            assert forall|y:int|0<=y<height implies
                #[trigger] rowwise_scaled(samples,width as nat,target,factor)[y*(width as int)+x]
                    ==if (y%2==0)==target{part1_fixed_product(column[y],factor).get_Ok_0()}else{column[y]} by{
                rowwise_cell(y,x as int,width as int,height as int);
                rowwise_index(y,x as int,width as int);
            }
        }
    }
    pub(crate) proof fn rowwise_fixed_stage_column(samples:Seq<i64>,width:u32,height:u32,x:u32,target:bool,stage:u8)
        requires width>0,height>1,x<width,(width as int)*(height as int)==samples.len(),stage<4,
            forall|i:int|0<=i<samples.len()==>-rowwise_fixed_bound(stage as nat)<=#[trigger] samples[i]<=rowwise_fixed_bound(stage as nat),
        ensures part1_lifting_prefix(rowwise_column(samples,width as nat,height as nat,x as nat),target,2,part1_nine_seven_lift(stage),height as nat)
            ==(Ok(()),rowwise_column(rowwise_fixed_stage(samples,width as nat,height as nat,target,stage),width as nat,height as nat,x as nat)),
    {
        let column=rowwise_column(samples,width as nat,height as nat,x as nat);
        let factor=part1_nine_seven_lift(stage);
        assert forall|y:nat|y<height implies #[trigger] part1_lifting_sample(column,y,target,2,factor).is_ok() by{
            if (y%2==0)==target{
                let left=if y==0{1nat}else{(y-1) as nat};
                let right=if y+1<height{y+1}else{(y-1) as nat};
                rowwise_cell(y as int,x as int,width as int,height as int);
                rowwise_cell(left as int,x as int,width as int,height as int);
                rowwise_cell(right as int,x as int,width as int,height as int);
                rowwise_fixed_neighbors_bound(column[y as int],column[left as int],column[right as int],stage);
            }
        }
        rowwise_lift_prefix_with_factor(column,target,2,factor,height as nat);
        assert(Seq::new(column.len(),|y:int|part1_lifting_sample(column,y as nat,target,2,factor).get_Ok_0())
            =~=rowwise_column(rowwise_fixed_stage(samples,width as nat,height as nat,target,stage),width as nat,height as nat,x as nat)) by{
            assert forall|y:int|0<=y<height implies #[trigger] part1_lifting_sample(column,y as nat,target,2,factor).get_Ok_0()
                ==rowwise_fixed_stage(samples,width as nat,height as nat,target,stage)[y*(width as int)+x] by{
                rowwise_cell(y,x as int,width as int,height as int);
                rowwise_index(y,x as int,width as int);
            }
        }
    }
    pub(crate) proof fn rowwise_fixed_lifts_bound(samples:Seq<i64>,width:nat,height:nat,first:bool,count:nat)
        requires count<=4,width>0,height>1,width*height==samples.len(),
            forall|i:int|0<=i<samples.len()==>-rowwise_fixed_bound(0)<=#[trigger] samples[i]<=rowwise_fixed_bound(0),
        ensures rowwise_fixed_lifts(samples,width,height,first,count).len()==samples.len(),
            forall|i:int|0<=i<samples.len()==>-rowwise_fixed_bound(count)
                <=#[trigger] rowwise_fixed_lifts(samples,width,height,first,count)[i]<=rowwise_fixed_bound(count),
        decreases count,
    {
        if count>0{
            rowwise_fixed_lifts_bound(samples,width,height,first,(count-1) as nat);
            rowwise_fixed_stage_bound(rowwise_fixed_lifts(samples,width,height,first,(count-1) as nat),width,height,
                if count%2==1{first}else{!first},(count-1) as u8);
        }
    }
    pub(crate) proof fn rowwise_fixed_lifts_column(samples:Seq<i64>,width:u32,height:u32,x:u32,first:bool,count:nat)
        requires count<=4,width>0,height>1,x<width,(width as int)*(height as int)==samples.len(),
            forall|i:int|0<=i<samples.len()==>-rowwise_fixed_bound(0)<=#[trigger] samples[i]<=rowwise_fixed_bound(0),
        ensures part1_nine_seven_lifting_prefix(rowwise_column(samples,width as nat,height as nat,x as nat),first,count)
            ==(Ok(()),rowwise_column(rowwise_fixed_lifts(samples,width as nat,height as nat,first,count),width as nat,height as nat,x as nat)),
        decreases count,
    {
        if count>0{
            rowwise_fixed_lifts_column(samples,width,height,x,first,(count-1) as nat);
            rowwise_fixed_lifts_bound(samples,width as nat,height as nat,first,(count-1) as nat);
            rowwise_fixed_stage_column(rowwise_fixed_lifts(samples,width as nat,height as nat,first,(count-1) as nat),
                width,height,x,if count%2==1{first}else{!first},(count-1) as u8);
        }
    }
    pub(crate) proof fn rowwise_fixed_inverse_column(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,x:u32)
        requires rowwise_eligible(low,high,height,first,length),height>1,x<low.0,
        ensures part1_vertical_column(low,high,x,first,true)==
            Ok(rowwise_column(rowwise_fixed_output(low,high,height,first),low.0 as nat,height as nat,x as nat)),
    {
        rowwise_geometry(low,high,height,first,length);
        rowwise_collect(low.2,low.0,low.1,x,low.1 as nat);
        rowwise_collect(high.2,high.0,high.1,x,high.1 as nat);
        let a=rowwise_column(low.2,low.0 as nat,low.1 as nat,x as nat);
        let b=rowwise_column(high.2,high.0 as nat,high.1 as nat,x as nat);
        let samples=rowwise_interleaved(low,high,height,first);
        let column=rowwise_column(samples,low.0 as nat,height as nat,x as nat);
        assert(part1_interleaved(a,b,first)==Ok(column)) by{
            assert(Seq::new(height as nat,|y:int|if (y%2==0)==first{a[y/2]}else{b[y/2]}) =~=column) by{
                assert forall|y:int|0<=y<height implies #[trigger] samples[y*(low.0 as int)+x]==if (y%2==0)==first{a[y/2]}else{b[y/2]} by{
                    rowwise_cell(y,x as int,low.0 as int,height as int);rowwise_index(y,x as int,low.0 as int);
                }
            }
        }
        rowwise_interleaved_properties(low,high,height,first,length);
        rowwise_scaled_column(samples,low.0,height,x,first,true);
        rowwise_scaled_bound(samples,low.0 as nat,height as nat,first,true);
        let scaled_low=rowwise_scaled(samples,low.0 as nat,first,part1_nine_seven_scale(true));
        rowwise_scaled_column(scaled_low,low.0,height,x,!first,false);
        rowwise_scaled_bound(scaled_low,low.0 as nat,height as nat,!first,false);
        let scaled=rowwise_scaled(scaled_low,low.0 as nat,!first,part1_nine_seven_scale(false));
        rowwise_fixed_lifts_column(scaled,low.0,height,x,first,4);
        assert(part1_inverse_nine_seven(a,b,first)==Ok(
            rowwise_column(rowwise_fixed_output(low,high,height,first),low.0 as nat,height as nat,x as nat)));
    }
    pub(crate) proof fn rowwise_fixed_vertical_prefix(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,count:nat)
        requires rowwise_eligible(low,high,height,first,length),height>1,count<=low.0,
        ensures part1_vertical_prefix(low,high,height,first,true,length,count)==Ok(
            Seq::new(length as nat,|i:int|if i%(low.0 as int)<count{rowwise_fixed_output(low,high,height,first)[i]}else{0i64})),
        decreases count,
    {
        rowwise_fixed_output_length(low,high,height,first,length);
        let target=rowwise_fixed_output(low,high,height,first);
        if count>0{
            rowwise_fixed_vertical_prefix(low,high,height,first,length,(count-1) as nat);
            rowwise_fixed_inverse_column(low,high,height,first,length,(count-1) as u32);
            let previous=Seq::new(length as nat,|i:int|if i%(low.0 as int)<count-1{target[i]}else{0i64});
            rowwise_store(previous,target,low.0,height,(count-1) as u32,height as nat);
            let expected=Seq::new(length as nat,|i:int|if i%(low.0 as int)<count{target[i]}else{0i64});
            assert(Seq::new(length as nat,|i:int|if i%(low.0 as int)==count-1 && i/(low.0 as int)<height{target[i]}else{previous[i]}) =~=expected) by{
                assert forall|i:int|0<=i<length implies #[trigger] expected[i]==if i%(low.0 as int)==count-1 && i/(low.0 as int)<height{target[i]}else{previous[i]} by{
                    rowwise_coordinates(i,low.0 as int,height as int);
                }
            }
        }else{
            let expected=Seq::new(length as nat,|i:int|if i%(low.0 as int)<count{target[i]}else{0i64});
            assert(expected =~=Seq::new(length as nat,|_:int|0i64)) by{
                assert forall|i:int|0<=i<length implies #[trigger] expected[i]==0i64 by{rowwise_coordinates(i,low.0 as int,height as int);}
            }
        }
    }
    pub(crate) proof fn rowwise_fixed_equivalent(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize)
        requires rowwise_eligible(low,high,height,first,length),height>1,
        ensures part1_vertical_prefix(low,high,height,first,true,length,low.0 as nat)==Ok(rowwise_fixed_output(low,high,height,first)),
    {
        rowwise_fixed_output_length(low,high,height,first,length);
        rowwise_fixed_vertical_prefix(low,high,height,first,length,low.0 as nat);
        assert(Seq::new(length as nat,|i:int|if i%(low.0 as int)<low.0{rowwise_fixed_output(low,high,height,first)[i]}else{0i64}) =~=rowwise_fixed_output(low,high,height,first));
    }
    #[verifier::opaque]
    pub(crate) open spec fn rowwise_fixed_run(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,
        calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
        part2_tier1_storage_bind(part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Columns,length as nat,calls),
            |_:(),rest|Some((Ok(rowwise_fixed_output(low,high,height,first)),rest)))
    }
    pub(crate) open spec fn rowwise_fixed_result(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,
        result:Result<Seq<i64>,crate::DecodeError>)->bool {
        part2_tier1_storage_framed(|calls|rowwise_fixed_run(low,high,height,first,length,calls),result)
    }
    pub(crate) proof fn rowwise_fixed_observed(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,allocation:Result<(),crate::DecodeError>)
        requires part2_wavelet_capacity_result(Part2WaveletPlaneOwner::Columns,length as nat,allocation),
        ensures rowwise_fixed_result(low,high,height,first,length,match allocation{Err(error)=>Err(error),Ok(())=>Ok(rowwise_fixed_output(low,high,height,first))}),
    {
        reveal(rowwise_fixed_run);
        let result=match allocation{Err(error)=>Err(error),Ok(())=>Ok(rowwise_fixed_output(low,high,height,first))};
        if allocation.is_ok(){part2_tier1_storage_pure(result);}
        part2_tier1_storage_bind_frame(|calls|part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Columns,length as nat,calls),
            |_:(),rest|Some((Ok(rowwise_fixed_output(low,high,height,first)),rest)),allocation,result);
    }
pub(crate) proof fn rowwise_fixed_single_owner(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,
    succeeded:bool,tail:Seq<Part2Tier1StorageEvent>)
    requires rowwise_eligible(low,high,height,first,length),height>1,
    ensures rowwise_fixed_run(low,high,height,first,length,
        seq![Part2Tier1StorageEvent::WaveletPlaneCapacity {
            owner:Part2WaveletPlaneOwner::Columns,elements:length as nat,succeeded,
        }]+tail)==Some((if succeeded{Ok(rowwise_fixed_output(low,high,height,first))}else{Err(crate::DecodeError::AllocationFailed)},tail)),
{
    reveal(rowwise_fixed_run);reveal(part2_wavelet_capacity_run);
    let prefix=seq![Part2Tier1StorageEvent::WaveletPlaneCapacity {
        owner:Part2WaveletPlaneOwner::Columns,elements:length as nat,succeeded,
    }];
    assert(length>0) by(nonlinear_arith)
        requires low.0>=2,height>0,length==(low.0 as int)*(height as int);
    assert((prefix+tail).drop_first() =~=tail);
}
}
