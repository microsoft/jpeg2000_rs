//! Source-index and row-splice composition for direct bounded placement.
use super::*;
verus! {
pub(crate) proof fn part2_fused_span(dw:int,dh:int,bw:int,bh:int,x:int,y:int,row:int)
    requires dw>0,0<bw,0<bh,0<=x,x+bw<=dw,0<=y,y+bh<=dh,0<=row<bh,
    ensures 0<=(y+row)*dw+x,(y+row)*dw+x+bw<=dw*dh,
        0<=row*bw,row*bw+bw<=bw*bh,
        (row+1)*bw==row*bw+bw,
{
    assert(0<=(y+row)*dw+x && (y+row)*dw+x+bw<=dw*dh
        && 0<=row*bw && row*bw+bw<=bw*bh && (row+1)*bw==row*bw+bw) by(nonlinear_arith)
        requires dw>0,0<bw,0<bh,0<=x,x+bw<=dw,0<=y,y+bh<=dh,0<=row<bh;
}
pub(crate) proof fn part2_fused_coordinates(index:int,width:int,height:int)
    requires width>0,0<=index<width*height,
    ensures 0<=index/width<height,0<=index%width<width,index==(index/width)*width+index%width,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(index,width);
    vstd::arithmetic::div_mod::lemma_mod_bound(index,width);
    assert((index/width)*width==width*(index/width)) by(nonlinear_arith);
    assert(0<=index/width<height) by(nonlinear_arith)
        requires index==(index/width)*width+index%width,0<=index%width<width,width>0,0<=index<width*height;
}
pub(crate) open spec fn part2_fused_values(plane:Tier1RawPlane,shift:u8,step:i64,reversible:bool)->Seq<i64> {
    Seq::new(plane.coefficients.len(),|i:int|part2_fused_sample(plane.coefficients[i],shift,step,reversible))
}
pub(crate) open spec fn part2_fused_write_admit(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,
    x:u32,y:u32,shift:u8,step:i64,reversible:bool)->bool {
    let count=(plane.width as int)*(plane.height as int);
    let area=(destination.0 as int)*(destination.1 as int);
    count>0 && count<=usize::MAX && count==plane.coefficients.len() && area<=usize::MAX
    && (forall|i:int|0<=i<plane.coefficients.len() ==> #[trigger] plane.coefficients[i].limbs.len()==6)
    && destination.3.len()==area && destination.4.len()==area && step>=0
    && x as int+plane.width as int<=destination.0 && y as int+plane.height as int<=destination.1
    && forall|row:int,column:int|0<=row<plane.height && 0<=column<plane.width ==>
        #[trigger] part2_fused_cell_valid(destination,plane,x,y,shift,step,reversible,row,column)
}
pub(crate) proof fn part2_fused_geometry(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,x:u32,y:u32,shift:u8,step:i64,reversible:bool)
    requires part2_fused_write_admit(destination,plane,x,y,shift,step,reversible),
    ensures plane.width>0,plane.height>0,destination.0>0,destination.1>0,
        destination.0<=usize::MAX,destination.1<=usize::MAX,
        plane.width<=usize::MAX,plane.height<=usize::MAX,
{
    assert(plane.width>0 && plane.height>0 && destination.0>0 && destination.1>0) by(nonlinear_arith)
        requires (plane.width as int)*(plane.height as int)>0,x as int+plane.width as int<=destination.0,
            y as int+plane.height as int<=destination.1;
    assert(destination.0<=usize::MAX && destination.1<=usize::MAX) by(nonlinear_arith)
        requires destination.0>0,destination.1>0,(destination.0 as int)*(destination.1 as int)<=usize::MAX;
}
pub(crate) open spec fn part2_fused_row(band:Part1WorkingSubbandModel,source:Seq<i64>,width:u32,x:u32,y:u32,row:nat,count:nat)->Part1WorkingSubbandModel {
    let start=((y as int)+row)*(band.0 as int)+x as int;
    (band.0,band.1,band.2,
        Seq::new(band.3.len(),|i:int|if start<=i<start+count{source[row*(width as int)+i-start]}else{band.3[i]}),
        Seq::new(band.4.len(),|i:int|if start<=i<start+count{true}else{band.4[i]}))
}
pub(crate) open spec fn part2_fused_rows(band:Part1WorkingSubbandModel,source:Seq<i64>,width:u32,x:u32,y:u32,count:nat)->Part1WorkingSubbandModel
    decreases count,
{
    if count==0{band}else{part2_fused_row(part2_fused_rows(band,source,width,x,y,(count-1) as nat),source,width,x,y,(count-1) as nat,width as nat)}
}
pub(crate) proof fn part2_fused_row_scalar(band:Part1WorkingSubbandModel,source:Seq<i64>,width:u32,x:u32,y:u32,row:u32,count:nat)
    requires width>0,count<=width,x as int+width as int<=band.0,(y as int+row as int)<band.1,
        band.3.len()==(band.0 as int)*(band.1 as int),band.4.len()==band.3.len(),band.3.len()<=usize::MAX,
        ((row as int)+1)*(width as int)<=source.len(),source.len()<=usize::MAX,
        forall|c:int|0<=c<width ==> !#[trigger] band.4[(y as int+row as int)*(band.0 as int)+x as int+c],
    ensures part1_quantized_block_row(band,source,width,x,y,row,count)==(Ok(()),part2_fused_row(band,source,width,x,y,row as nat,count)),
    decreases count,
{
    reveal_with_fuel(part1_quantized_block_row,2);
    if count>0{
        part2_fused_row_scalar(band,source,width,x,y,row,(count-1) as nat);
        let start=(y as int+row as int)*(band.0 as int)+x as int;
        let index=start+count-1;
        assert(band.0>0);
        assert(0<=start && start+(width as int)<=band.3.len()) by(nonlinear_arith)
            requires start==(y as int+row as int)*(band.0 as int)+x as int,x as int+width as int<=band.0,
                (y as int+row as int)<band.1,band.3.len()==(band.0 as int)*(band.1 as int),band.0>0;
        assert(band.0<=usize::MAX && y as int+row as int<=usize::MAX) by(nonlinear_arith)
            requires band.0>0,(y as int+row as int)<band.1,band.3.len()==(band.0 as int)*(band.1 as int),band.3.len()<=usize::MAX;
        let previous=part2_fused_row(band,source,width,x,y,row as nat,(count-1) as nat);
        let next=part2_fused_row(band,source,width,x,y,row as nat,count);
        assert(width<=usize::MAX && row<=usize::MAX) by(nonlinear_arith)
            requires width>0,((row as int)+1)*(width as int)<=source.len(),source.len()<=usize::MAX;
        assert(0<=(row as int)*(width as int)+count-1<source.len()) by(nonlinear_arith)
            requires width>0,row>=0,0<count<=width,((row as int)+1)*(width as int)<=source.len();
        assert(part1_transform_offset((y as int+row as int) as u32,band.0,(x as int+count-1) as u32)==Ok(index as usize));
        assert(part1_transform_offset(row,width,(count-1) as u32)==Ok(((row as int)*(width as int)+count-1) as usize));
        assert(!previous.4[index]);
        assert(previous.3.update(index,source[(row as int)*(width as int)+count-1]) =~=next.3);
        assert(previous.4.update(index,true) =~=next.4);
        assert(part1_quantized_block_pixel(previous,source,width,x,y,(count-1) as u32,row)==(Ok(()),next));
    }else{
        assert(part2_fused_row(band,source,width,x,y,row as nat,0).3 =~=band.3);
        assert(part2_fused_row(band,source,width,x,y,row as nat,0).4 =~=band.4);
    }
}
    pub(crate) proof fn part2_fused_rows_frame(band:Part1WorkingSubbandModel,source:Seq<i64>,width:u32,x:u32,y:u32,count:nat)
        requires width>0,x as int+width as int<=band.0,y as int+count<=band.1,count*(width as int)<=source.len(),
        ensures
            part2_fused_rows(band,source,width,x,y,count).0==band.0,
            part2_fused_rows(band,source,width,x,y,count).1==band.1,
            part2_fused_rows(band,source,width,x,y,count).2==band.2,
            part2_fused_rows(band,source,width,x,y,count).3.len()==band.3.len(),
            part2_fused_rows(band,source,width,x,y,count).4.len()==band.4.len(),
            forall|i:int|(y as int+count)*(band.0 as int)+x as int<=i<band.3.len() ==>
                #[trigger] part2_fused_rows(band,source,width,x,y,count).3[i]==band.3[i],
            forall|i:int|(y as int+count)*(band.0 as int)+x as int<=i<band.4.len() ==>
                #[trigger] part2_fused_rows(band,source,width,x,y,count).4[i]==band.4[i],
        decreases count,
    {
        if count>0{
            assert((count-1)*(width as int)<=source.len()) by(nonlinear_arith)
                requires count>0,width>0,count*(width as int)<=source.len();
            part2_fused_rows_frame(band,source,width,x,y,(count-1) as nat);
            let previous=part2_fused_rows(band,source,width,x,y,(count-1) as nat);
            let next=part2_fused_rows(band,source,width,x,y,count);
            let start=(y as int+count-1)*(band.0 as int)+x as int;
            assert(start+(width as int)<=(y as int+count)*(band.0 as int)+x as int) by(nonlinear_arith)
                requires start==(y as int+count-1)*(band.0 as int)+x as int,width<=band.0;
            assert forall|i:int|(y as int+count)*(band.0 as int)+x as int<=i<band.3.len() implies #[trigger] next.3[i]==band.3[i] by{
                assert(next.3[i]==previous.3[i]);
            }
            assert forall|i:int|(y as int+count)*(band.0 as int)+x as int<=i<band.4.len() implies #[trigger] next.4[i]==band.4[i] by{
                assert(next.4[i]==previous.4[i]);
            }
        }
    }
pub(crate) proof fn part2_fused_rows_scalar(destination:Part1WorkingSubbandModel,plane:Tier1RawPlane,x:u32,y:u32,shift:u8,step:i64,reversible:bool,count:nat)
    requires part2_fused_write_admit(destination,plane,x,y,shift,step,reversible),count<=plane.height,
    ensures
        part1_quantized_block_rows(destination,part2_fused_values(plane,shift,step,reversible),plane.width as u32,x,y,count)
            ==(Ok(()),part2_fused_rows(destination,part2_fused_values(plane,shift,step,reversible),plane.width as u32,x,y,count)),
        part2_fused_rows(destination,part2_fused_values(plane,shift,step,reversible),plane.width as u32,x,y,count).0==destination.0,
        part2_fused_rows(destination,part2_fused_values(plane,shift,step,reversible),plane.width as u32,x,y,count).1==destination.1,
        part2_fused_rows(destination,part2_fused_values(plane,shift,step,reversible),plane.width as u32,x,y,count).2==destination.2,
        part2_fused_rows(destination,part2_fused_values(plane,shift,step,reversible),plane.width as u32,x,y,count).3.len()==destination.3.len(),
        part2_fused_rows(destination,part2_fused_values(plane,shift,step,reversible),plane.width as u32,x,y,count).4.len()==destination.4.len(),
        forall|i:int|(y as int+count)*(destination.0 as int)+x as int<=i<destination.3.len() ==>
            #[trigger] part2_fused_rows(destination,part2_fused_values(plane,shift,step,reversible),plane.width as u32,x,y,count).3[i]==destination.3[i]
            && #[trigger] part2_fused_rows(destination,part2_fused_values(plane,shift,step,reversible),plane.width as u32,x,y,count).4[i]==destination.4[i],
    decreases count,
{
    reveal_with_fuel(part1_quantized_block_rows,2);
    part2_fused_geometry(destination,plane,x,y,shift,step,reversible);
    let source=part2_fused_values(plane,shift,step,reversible);
    assert(count*(plane.width as int)<=source.len()) by(nonlinear_arith)
        requires count<=plane.height,source.len()==(plane.width as int)*(plane.height as int);
    part2_fused_rows_frame(destination,source,plane.width as u32,x,y,count);
    if count>0{
        part2_fused_rows_scalar(destination,plane,x,y,shift,step,reversible,(count-1) as nat);
        part2_fused_span(destination.0 as int,destination.1 as int,plane.width as int,plane.height as int,x as int,y as int,count-1);
        let previous=part2_fused_rows(destination,source,plane.width as u32,x,y,(count-1) as nat);
        let start=(y as int+count-1)*(destination.0 as int)+x as int;
        part2_fused_rows_frame(destination,source,plane.width as u32,x,y,(count-1) as nat);
        assert forall|c:int|0<=c<plane.width implies !#[trigger] previous.4[start+c] by{
            assert(part2_fused_cell_valid(destination,plane,x,y,shift,step,reversible,count-1,c));
            assert(0<=start+c<destination.4.len());
            assert(previous.4[start+c]==destination.4[start+c]);
        }
        part2_fused_row_scalar(previous,source,plane.width as u32,x,y,(count-1) as u32,plane.width as nat);
        let next=part2_fused_rows(destination,source,plane.width as u32,x,y,count);
        assert forall|i:int|(y as int+count)*(destination.0 as int)+x as int<=i<destination.3.len() implies
            #[trigger] next.3[i]==destination.3[i] && #[trigger] next.4[i]==destination.4[i] by{
            assert(start+(plane.width as int)<=(y as int+count)*(destination.0 as int)+x as int) by(nonlinear_arith)
                requires start==(y as int+count-1)*(destination.0 as int)+x as int,plane.width<=destination.0;
            assert(next.3[i]==previous.3[i] && next.4[i]==previous.4[i]);
            assert(previous.3[i]==destination.3[i] && previous.4[i]==destination.4[i]);
        }
    }
}
}
