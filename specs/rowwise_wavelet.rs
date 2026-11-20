//! Borrowed-band reversible vertical traversal. One output owner; no line scratch.
use super::*;
verus! {
pub(crate) open spec fn rowwise_bounded(samples:Seq<i64>)->bool {
    forall|i:int| 0<=i<samples.len() ==> -1073741824<=samples[i]<=1073741824
}
pub(crate) open spec fn rowwise_eligible(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize)->bool {
    low.0>=2 && height>0 && low.0==high.0 && low.1==part1_low_count(height,first)
    && high.1==height-low.1 && low.2.len()+high.2.len()==length
    && low.0 as int*height as int==length && low.0 as int*low.1 as int==low.2.len()
    && rowwise_bounded(low.2) && rowwise_bounded(high.2)
}
pub(crate) open spec fn rowwise_interleaved(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool)->Seq<i64> {
    Seq::new((low.0 as nat)*(height as nat),|i:int|{
        let y=i/(low.0 as int);let x=i%(low.0 as int);
        let band=if (y%2==0)==first{low}else{high};
        band.2[(y/2)*(low.0 as int)+x]
    })
}
pub(crate) open spec fn rowwise_column(samples:Seq<i64>,width:nat,height:nat,x:nat)->Seq<i64> {
    Seq::new(height,|y:int|samples[y*(width as int)+x])
}
pub(crate) open spec fn rowwise_neighbors(current:i64,left:i64,right:i64,predict:bool)->Result<i64,crate::DecodeError> {
    part1_lifting_sample(seq![left,current,right],1,false,if predict{1u8}else{0u8},0)
}
pub(crate) open spec fn rowwise_value(samples:Seq<i64>,width:nat,height:nat,y:nat,x:nat,predict:bool)->i64 {
    let row=y*width;
    let left=if y==0{width}else{(y-1)*width};
    let right=if y+1<height{(y+1)*width}else{(y-1)*width};
    rowwise_neighbors(samples[(row+x) as int],samples[(left+x) as int],samples[(right+x) as int],predict).unwrap()
}
pub(crate) open spec fn rowwise_stage(samples:Seq<i64>,width:nat,height:nat,target:bool,predict:bool)->Seq<i64> {
    Seq::new(samples.len(),|i:int|if ((i/(width as int))%2==0)==target {
        rowwise_value(samples,width,height,(i/(width as int)) as nat,(i%(width as int)) as nat,predict)
    }else{samples[i]})
}
pub(crate) open spec fn rowwise_output(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool)->Seq<i64> {
    let samples=rowwise_interleaved(low,high,height,first);
    if height==1 {
        if first{samples}else{Seq::new(samples.len(),|i:int|samples[i]>>1)}
    }else{
        let update=rowwise_stage(samples,low.0 as nat,height as nat,first,false);
        rowwise_stage(update,low.0 as nat,height as nat,!first,true)
    }
}
#[verifier::opaque]
pub(crate) open spec fn rowwise_run(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Columns,length as nat,calls),
        |_:(),rest|Some((Ok(rowwise_output(low,high,height,first)),rest)))
}
pub(crate) open spec fn rowwise_result(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,
    result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|rowwise_run(low,high,height,first,length,calls),result)
}
pub(crate) proof fn rowwise_observed(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,
    allocation:Result<(),crate::DecodeError>)
    requires part2_wavelet_capacity_result(Part2WaveletPlaneOwner::Columns,length as nat,allocation),
    ensures rowwise_result(low,high,height,first,length,match allocation{Err(error)=>Err(error),Ok(())=>Ok(rowwise_output(low,high,height,first))}),
{
    reveal(rowwise_run);
    let result=match allocation{Err(error)=>Err(error),Ok(())=>Ok(rowwise_output(low,high,height,first))};
    if allocation.is_ok(){part2_tier1_storage_pure(result);}
    part2_tier1_storage_bind_frame(|calls|part2_wavelet_capacity_run(Part2WaveletPlaneOwner::Columns,length as nat,calls),
        |_:(),rest|Some((Ok(rowwise_output(low,high,height,first)),rest)),allocation,result);
}
pub(crate) proof fn rowwise_single_owner(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,
    succeeded:bool,tail:Seq<Part2Tier1StorageEvent>)
    requires rowwise_eligible(low,high,height,first,length),
    ensures rowwise_run(low,high,height,first,length,
        seq![Part2Tier1StorageEvent::WaveletPlaneCapacity {
            owner:Part2WaveletPlaneOwner::Columns,elements:length as nat,succeeded,
        }]+tail)==Some((if succeeded{Ok(rowwise_output(low,high,height,first))}else{Err(crate::DecodeError::AllocationFailed)},tail)),
{
    reveal(rowwise_run);reveal(part2_wavelet_capacity_run);
    let prefix=seq![Part2Tier1StorageEvent::WaveletPlaneCapacity {
        owner:Part2WaveletPlaneOwner::Columns,elements:length as nat,succeeded,
    }];
    assert(length>0) by(nonlinear_arith)
        requires low.0>=2,height>0,length==(low.0 as int)*(height as int);
    assert((prefix+tail).drop_first() =~=tail);
}
pub(crate) proof fn rowwise_neighbors_bounded(current:i64,left:i64,right:i64,predict:bool)
    requires
        -(if predict{2147483648int}else{1073741824int})<=current<=if predict{2147483648int}else{1073741824int},
        -(if predict{2147483648int}else{1073741824int})<=left<=if predict{2147483648int}else{1073741824int},
        -(if predict{2147483648int}else{1073741824int})<=right<=if predict{2147483648int}else{1073741824int},
    ensures rowwise_neighbors(current,left,right,predict).is_ok(),
        -(if predict{4294967296int}else{2147483648int})<=rowwise_neighbors(current,left,right,predict).unwrap()
            <=if predict{4294967296int}else{2147483648int},
{
    let sum=(left as int)+(right as int);
    assert(i64::MIN<=sum<=i64::MAX);
    if predict {
        let sum=sum as i64;
        assert(-2147483648int<=sum>>1<=2147483648int) by(bit_vector)
            requires -4294967296int<=sum<=4294967296int;
    }else{
        let biased=(sum+2) as i64;
        assert(-1073741824int<=biased>>2<=1073741824int) by(bit_vector)
            requires -2147483646int<=biased<=2147483650int;
    }
}
pub(crate) proof fn rowwise_collect(samples:Seq<i64>,width:u32,height:u32,x:u32,count:nat)
    requires width>0,x<width,count<=height,width as int*height as int==samples.len(),samples.len()<=usize::MAX,
    ensures part1_column_prefix(samples,width,x,count)==Ok(rowwise_column(samples,width as nat,count,x as nat)),
    decreases count,
{
    if count>0 {
        rowwise_collect(samples,width,height,x,(count-1) as nat);
        assert(rowwise_column(samples,width as nat,(count-1) as nat,x as nat).push(samples[(count-1)*(width as int)+x])
            =~= rowwise_column(samples,width as nat,count,x as nat));
    }
}
pub(crate) proof fn rowwise_lift_prefix(samples:Seq<i64>,target:bool,kind:u8,count:nat)
    requires count<=samples.len(),
        forall|i:nat| i<samples.len() ==> part1_lifting_sample(samples,i,target,kind,0).is_ok(),
    ensures part1_lifting_prefix(samples,target,kind,0,count)==(Ok(()),
        Seq::new(samples.len(),|i:int|if i<count{part1_lifting_sample(samples,i as nat,target,kind,0).unwrap()}else{samples[i]})),
    decreases count,
{
    if count>0{
        rowwise_lift_prefix(samples,target,kind,(count-1) as nat);
        assert(Seq::new(samples.len(),|i:int|if i<count-1{part1_lifting_sample(samples,i as nat,target,kind,0).unwrap()}else{samples[i]})
            .update(count-1,part1_lifting_sample(samples,(count-1) as nat,target,kind,0).unwrap())
            =~= Seq::new(samples.len(),|i:int|if i<count{part1_lifting_sample(samples,i as nat,target,kind,0).unwrap()}else{samples[i]}));
    }else{assert(samples =~= Seq::new(samples.len(),|i:int|samples[i]));}
}
pub(crate) proof fn rowwise_stage_column(samples:Seq<i64>,width:u32,height:u32,x:u32,target:bool,predict:bool)
    requires width>0,height>1,x<width,width as int*height as int==samples.len(),
        forall|i:int|0<=i<samples.len()==>
            -(if predict{2147483648int}else{1073741824int})<=samples[i]<=if predict{2147483648int}else{1073741824int},
    ensures part1_lifting_prefix(rowwise_column(samples,width as nat,height as nat,x as nat),target,if predict{1u8}else{0u8},0,height as nat)
        ==(Ok(()),rowwise_column(rowwise_stage(samples,width as nat,height as nat,target,predict),width as nat,height as nat,x as nat)),
{
    let column=rowwise_column(samples,width as nat,height as nat,x as nat);
    assert forall|y:nat|y<height implies
        part1_lifting_sample(column,y,target,if predict{1u8}else{0u8},0).is_ok() by{
        if (y%2==0)==target {
            let left=if y==0{1nat}else{(y-1) as nat};
            let right=if y+1<height{y+1}else{(y-1) as nat};
            rowwise_neighbors_bounded(column[y as int],column[left as int],column[right as int],predict);
        }
    }
    rowwise_lift_prefix(column,target,if predict{1u8}else{0u8},height as nat);
    assert(Seq::new(column.len(),|i:int|part1_lifting_sample(column,i as nat,target,if predict{1u8}else{0u8},0).unwrap())
        =~=rowwise_column(rowwise_stage(samples,width as nat,height as nat,target,predict),width as nat,height as nat,x as nat)) by{
        assert forall|y:int|0<=y<height implies
            part1_lifting_sample(column,y as nat,target,if predict{1u8}else{0u8},0).unwrap()
            ==rowwise_stage(samples,width as nat,height as nat,target,predict)[y*(width as int)+x] by{
            assert((y*(width as int)+x)/(width as int)==y) by(nonlinear_arith)
                requires width>0,0<=x<width;
            assert((y*(width as int)+x)%(width as int)==x) by(nonlinear_arith)
                requires width>0,0<=x<width;
        }
    }
    pub(crate) proof fn rowwise_stage_bounded(samples:Seq<i64>,width:nat,height:nat,target:bool,predict:bool)
        requires width>0,height>1,width*height==samples.len(),
            forall|i:int|0<=i<samples.len()==>
                -(if predict{2147483648int}else{1073741824int})<=samples[i]<=if predict{2147483648int}else{1073741824int},
        ensures forall|i:int|0<=i<samples.len()==>
            -(if predict{4294967296int}else{2147483648int})<=rowwise_stage(samples,width,height,target,predict)[i]
                <=if predict{4294967296int}else{2147483648int},
    {
        assert forall|i:int|0<=i<samples.len() implies
            -(if predict{4294967296int}else{2147483648int})<=rowwise_stage(samples,width,height,target,predict)[i]
                <=if predict{4294967296int}else{2147483648int} by{
            let y=(i/(width as int)) as nat;let x=(i%(width as int)) as nat;
            if (y%2==0)==target {
                let left=if y==0{width}else{(y-1)*width};
                let right=if y+1<height{(y+1)*width}else{(y-1)*width};
                assert(0<=y<height && 0<=x<width) by(nonlinear_arith)
                    requires 0<=i<width*height,width>0;
                rowwise_neighbors_bounded(samples[i],samples[(left+x) as int],samples[(right+x) as int],predict);
            }
        }
    }
    pub(crate) proof fn rowwise_interleaved_properties(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize)
        requires rowwise_eligible(low,high,height,first,length),
        ensures rowwise_bounded(rowwise_interleaved(low,high,height,first)),
            rowwise_interleaved(low,high,height,first).len()==length,
    {
        let samples=rowwise_interleaved(low,high,height,first);
        assert forall|i:int|0<=i<samples.len() implies -1073741824<=samples[i]<=1073741824 by{
            let y=i/(low.0 as int);let x=i%(low.0 as int);
            assert(0<=y<height && 0<=x<low.0) by(nonlinear_arith)
                requires low.0>=2,0<=i<(low.0 as int)*(height as int);
            if (y%2==0)==first {
                assert(0<=y/2<low.1);
                assert(0<=(y/2)*(low.0 as int)+x<low.2.len()) by(nonlinear_arith)
                    requires 0<=y/2<low.1,0<=x<low.0,low.0>=2,low.2.len()==(low.0 as int)*(low.1 as int);
            }else{
                assert(0<=y/2<high.1);
                assert(0<=(y/2)*(low.0 as int)+x<high.2.len()) by(nonlinear_arith)
                    requires 0<=y/2<high.1,0<=x<low.0,low.0>=2,high.2.len()==(low.0 as int)*(high.1 as int);
            }
        }
    }
    pub(crate) proof fn rowwise_inverse_column(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,x:u32)
        requires rowwise_eligible(low,high,height,first,length),x<low.0,
        ensures part1_vertical_column(low,high,x,first,false)==
            Ok(rowwise_column(rowwise_output(low,high,height,first),low.0 as nat,height as nat,x as nat)),
    {
        rowwise_collect(low.2,low.0,low.1,x,low.1 as nat);
        rowwise_collect(high.2,high.0,high.1,x,high.1 as nat);
        let a=rowwise_column(low.2,low.0 as nat,low.1 as nat,x as nat);
        let b=rowwise_column(high.2,high.0 as nat,high.1 as nat,x as nat);
        let samples=rowwise_interleaved(low,high,height,first);
        let column=rowwise_column(samples,low.0 as nat,height as nat,x as nat);
        assert(part1_interleaved(a,b,first)==Ok(column)) by{
            assert(Seq::new(height as nat,|y:int|if (y%2==0)==first{a[y/2]}else{b[y/2]}) =~=column) by{
                assert forall|y:int|0<=y<height implies
                    samples[y*(low.0 as int)+x]==if (y%2==0)==first{a[y/2]}else{b[y/2]} by{
                    assert((y*(low.0 as int)+x)/(low.0 as int)==y) by(nonlinear_arith)
                        requires low.0>=2,0<=x<low.0;
                    assert((y*(low.0 as int)+x)%(low.0 as int)==x) by(nonlinear_arith)
                        requires low.0>=2,0<=x<low.0;
                }
            }
        }
        if height==1 {
            if !first {
                assert(column.update(0,column[0]>>1) =~=
                    rowwise_column(rowwise_output(low,high,height,first),low.0 as nat,height as nat,x as nat));
            }
        }else{
            rowwise_interleaved_properties(low,high,height,first,length);
            rowwise_stage_column(samples,low.0,height,x,first,false);
            rowwise_stage_bounded(samples,low.0 as nat,height as nat,first,false);
            let update=rowwise_stage(samples,low.0 as nat,height as nat,first,false);
            rowwise_stage_column(update,low.0,height,x,!first,true);
        }
    }
    pub(crate) proof fn rowwise_store(output:Seq<i64>,target:Seq<i64>,width:u32,height:u32,x:u32,count:nat)
        requires width>0,x<width,count<=height,output.len()==target.len(),target.len()==(width as nat)*(height as nat),
            target.len()<=usize::MAX,
        ensures part1_store_column_prefix(output,width,x,rowwise_column(target,width as nat,height as nat,x as nat),count)
            ==(Ok(()),Seq::new(output.len(),|i:int|if i%(width as int)==x && i/(width as int)<count{target[i]}else{output[i]})),
        decreases count,
    {
        if count>0{
            rowwise_store(output,target,width,height,x,(count-1) as nat);
            let previous=Seq::new(output.len(),|i:int|if i%(width as int)==x && i/(width as int)<count-1{target[i]}else{output[i]});
            let index=(count-1)*(width as int)+x;
            assert(index/(width as int)==count-1 && index%(width as int)==x) by(nonlinear_arith)
                requires width>0,0<=x<width;
            assert(previous.update(index,target[index]) =~=
                Seq::new(output.len(),|i:int|if i%(width as int)==x && i/(width as int)<count{target[i]}else{output[i]})) by{
                assert forall|i:int|0<=i<output.len() && i!=index implies
                    !(i%(width as int)==x && i/(width as int)==count-1) by(nonlinear_arith)
                    requires width>0,index==(count-1)*(width as int)+x;
            }
        }else{assert(output =~=Seq::new(output.len(),|i:int|output[i]));}
    }
    pub(crate) proof fn rowwise_vertical_prefix(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize,count:nat)
        requires rowwise_eligible(low,high,height,first,length),count<=low.0,
        ensures part1_vertical_prefix(low,high,height,first,false,length,count)==Ok(
            Seq::new(length as nat,|i:int|if i%(low.0 as int)<count{rowwise_output(low,high,height,first)[i]}else{0i64})),
        decreases count,
    {
        if count>0{
            rowwise_vertical_prefix(low,high,height,first,length,(count-1) as nat);
            rowwise_inverse_column(low,high,height,first,length,(count-1) as u32);
            let target=rowwise_output(low,high,height,first);
            let previous=Seq::new(length as nat,|i:int|if i%(low.0 as int)<count-1{target[i]}else{0i64});
            rowwise_store(previous,target,low.0,height,(count-1) as u32,height as nat);
            assert(Seq::new(length as nat,|i:int|if i%(low.0 as int)==count-1 && i/(low.0 as int)<height{target[i]}else{previous[i]})
                =~=Seq::new(length as nat,|i:int|if i%(low.0 as int)<count{target[i]}else{0i64})) by{
                assert forall|i:int|0<=i<length implies i/(low.0 as int)<height by(nonlinear_arith)
                    requires low.0>0,length==(low.0 as int)*(height as int);
            }
        }
    }
    pub(crate) proof fn rowwise_equivalent(low:Part1WaveletBand,high:Part1WaveletBand,height:u32,first:bool,length:usize)
        requires rowwise_eligible(low,high,height,first,length),
        ensures part1_vertical_prefix(low,high,height,first,false,length,low.0 as nat)==Ok(rowwise_output(low,high,height,first)),
    {
        rowwise_vertical_prefix(low,high,height,first,length,low.0 as nat);
        assert(Seq::new(length as nat,|i:int|if i%(low.0 as int)<low.0{rowwise_output(low,high,height,first)[i]}else{0i64})
            =~=rowwise_output(low,high,height,first));
    }
}
}
