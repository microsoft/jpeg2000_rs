use super::super::InverseLiftingStep;
use super::super::wavelets::{fixed_mul, inverse_lifting_neighbors};
use super::{WaveletBand, assemble};
#[cfg(verus_keep_ghost)]
use super::{sequence_outcome, wavelet_band_view};
use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::rowwise_eligible(wavelet_band_view(low),wavelet_band_view(high),height,first,length),height>1,
    ensures crate::specs::rowwise_fixed_result(wavelet_band_view(low),wavelet_band_view(high),height,first,length,sequence_outcome(result)),
        sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result)
            ==crate::specs::part1_vertical_prefix(wavelet_band_view(low),wavelet_band_view(high),height,first,true,length,low.width as nat),
))]
pub(in crate::transform) fn inverse(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    height: u32,
    first: bool,
    length: usize,
) -> Result<Vec<i64>, DecodeError> {
    let rows = assemble(low, high, height, first, length);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=rows{
            crate::specs::rowwise_fixed_observed(wavelet_band_view(low),wavelet_band_view(high),height,first,length,Err(error));
        }
    }
    let mut output = rows?;
    let width = low.width as usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::rowwise_geometry(wavelet_band_view(low),wavelet_band_view(high),height,first,length);
        crate::specs::rowwise_interleaved_properties(wavelet_band_view(low),wavelet_band_view(high),height,first,length);
    }
    scale_rows(&mut output, width, height as usize, first, true)?;
    scale_rows(&mut output, width, height as usize, !first, false)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost scaled=output@;}
    let mut stage = 0_u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant stage<=4,height>1,width==low.width,output.len()==length,
            crate::specs::rowwise_eligible(wavelet_band_view(low),wavelet_band_view(high),height,first,length),
            scaled==crate::specs::rowwise_scaled(crate::specs::rowwise_scaled(
                crate::specs::rowwise_interleaved(wavelet_band_view(low),wavelet_band_view(high),height,first),
                width as nat,first,crate::specs::part1_nine_seven_scale(true)),width as nat,!first,crate::specs::part1_nine_seven_scale(false)),
            output@==crate::specs::rowwise_fixed_lifts(scaled,width as nat,height as nat,first,stage as nat),
            forall|i:int|0<=i<output.len()==>-crate::specs::rowwise_fixed_bound(stage as nat)<=#[trigger] output[i]<=crate::specs::rowwise_fixed_bound(stage as nat),
        decreases 4-stage,
    ))]
    while stage < 4 {
        let target = if stage == 0 || stage == 2 {
            first
        } else {
            !first
        };
        lift_rows(&mut output, width, height as usize, target, stage)?;
        stage += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(output@==crate::specs::rowwise_fixed_output(wavelet_band_view(low),wavelet_band_view(high),height,first));
        crate::specs::rowwise_fixed_equivalent(wavelet_band_view(low),wavelet_band_view(high),height,first,length);
        crate::specs::part2_wavelet_capacity_observed(crate::specs::Part2WaveletPlaneOwner::Columns,length as nat,Ok(()));
        crate::specs::rowwise_fixed_observed(wavelet_band_view(low),wavelet_band_view(high),height,first,length,Ok(()));
    }
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires width>=2,height>1,(width as int)*(height as int)==old(samples).len(),
        forall|i:int|0<=i<old(samples).len()==>-crate::specs::rowwise_scale_bound(low)<=#[trigger] old(samples)[i]<=crate::specs::rowwise_scale_bound(low),
    ensures result==Ok(()),final(samples)@==crate::specs::rowwise_scaled(old(samples)@,width as nat,target,crate::specs::part1_nine_seven_scale(low)),
        forall|i:int|0<=i<final(samples).len()==>-2*crate::specs::rowwise_scale_bound(low)<=#[trigger] final(samples)[i]<=2*crate::specs::rowwise_scale_bound(low),
))]
fn scale_rows(
    samples: &mut [i64],
    width: usize,
    height: usize,
    target: bool,
    low: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost original=samples@;}
    #[cfg(verus_keep_ghost)]
    proof! {assert((height as int)*(width as int)==(width as int)*(height as int)) by(nonlinear_arith);}
    let factor = crate::refinement::nine_seven_scale(low);
    let mut y = 0;
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant width>=2,height>1,(width as int)*(height as int)==samples.len(),height as int*width as int==samples.len(),y<=height,index==y*width,
            original==old(samples)@,original.len()==samples.len(),factor==crate::specs::part1_nine_seven_scale(low),
            forall|i:int|0<=i<original.len()==>-crate::specs::rowwise_scale_bound(low)<=#[trigger] original[i]<=crate::specs::rowwise_scale_bound(low),
            forall|i:int|0<=i<samples.len()==>#[trigger] samples[i]==if i<index{
                crate::specs::rowwise_scaled(original,width as nat,target,factor)[i]}else{original[i]},
        decreases height-y,
    ))]
    while y < height {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::rowwise_cell(y as int,0,width as int,height as int);crate::proofs::production_impl::production_index_parity(y);}
        let end = index + width;
        if (y & 1 == 0) == target {
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant width>=2,height>1,(width as int)*(height as int)==samples.len(),height as int*width as int==samples.len(),y<height,(y%2==0)==target,
                    y*width<=index<=end,end==(y+1)*width,end==y*width+width,end<=samples.len(),
                    original==old(samples)@,original.len()==samples.len(),factor==crate::specs::part1_nine_seven_scale(low),
                    forall|i:int|0<=i<original.len()==>-crate::specs::rowwise_scale_bound(low)<=#[trigger] original[i]<=crate::specs::rowwise_scale_bound(low),
                    forall|i:int|0<=i<samples.len()==>#[trigger] samples[i]==if i<index{
                        crate::specs::rowwise_scaled(original,width as nat,target,factor)[i]}else{original[i]},
                decreases end-index,
            ))]
            while index < end {
                #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
                crate::deadline::checkpoint_periodic(index)?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::rowwise_index(y as int,index-y*width,width as int);
                    assert(samples[index as int]==original[index as int]);
                    crate::specs::rowwise_fixed_product_bound(samples[index as int],factor,crate::specs::rowwise_scale_bound(low) as i64);
                }
                samples[index] = fixed_mul(samples[index], factor)?;
                index += 1;
            }
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|i:int|y*width<=i<(y+1)*width implies
                    #[trigger] crate::specs::rowwise_scaled(original,width as nat,target,factor)[i]==original[i] by{
                    crate::specs::rowwise_index(y as int,i-y*width,width as int);
                }
            }
            index = end;
        }
        y += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(samples@ =~=crate::specs::rowwise_scaled(original,width as nat,target,factor));
        crate::specs::rowwise_scaled_bound(original,width as nat,height as nat,target,low);
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires width>=2,height>1,(width as int)*(height as int)==old(samples).len(),stage<4,
        forall|i:int|0<=i<old(samples).len()==>-crate::specs::rowwise_fixed_bound(stage as nat)<=#[trigger] old(samples)[i]<=crate::specs::rowwise_fixed_bound(stage as nat),
    ensures result==Ok(()),final(samples)@==crate::specs::rowwise_fixed_stage(old(samples)@,width as nat,height as nat,target,stage),
        forall|i:int|0<=i<final(samples).len()==>-crate::specs::rowwise_fixed_bound(stage as nat+1)<=#[trigger] final(samples)[i]<=crate::specs::rowwise_fixed_bound(stage as nat+1),
))]
fn lift_rows(
    samples: &mut [i64],
    width: usize,
    height: usize,
    target: bool,
    stage: u8,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost original=samples@;}
    #[cfg(verus_keep_ghost)]
    proof! {assert((height as int)*(width as int)==(width as int)*(height as int)) by(nonlinear_arith);}
    let factor = crate::refinement::nine_seven_lift(stage);
    let mut y = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant width>=2,height>1,(width as int)*(height as int)==samples.len(),height as int*width as int==samples.len(),y<=height,stage<4,
            factor==crate::specs::part1_nine_seven_lift(stage),original==old(samples)@,original.len()==samples.len(),
            forall|i:int|0<=i<original.len()==>-crate::specs::rowwise_fixed_bound(stage as nat)<=#[trigger] original[i]<=crate::specs::rowwise_fixed_bound(stage as nat),
            forall|i:int|0<=i<samples.len()==>#[trigger] samples[i]==if i<y*width{
                crate::specs::rowwise_fixed_stage(original,width as nat,height as nat,target,stage)[i]}else{original[i]},
        decreases height-y,
    ))]
    while y < height {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::rowwise_cell(y as int,0,width as int,height as int);crate::proofs::production_impl::production_index_parity(y);}
        if (y & 1 == 0) == target {
            #[cfg(verus_keep_ghost)]
            proof! {if y>0{assert(width<=y*width) by(nonlinear_arith) requires y>0,width>=2;}}
            let row = y * width;
            let left = if y == 0 { width } else { row - width };
            let right = if y + 1 < height {
                row + width
            } else {
                row - width
            };
            let mut x = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant width>=2,height>1,(width as int)*(height as int)==samples.len(),height as int*width as int==samples.len(),y<height,(y%2==0)==target,
                    x<=width,row==y*width,row+width<=samples.len(),stage<4,
                    left==if y==0{width as int}else{row-width},right==if y+1<height{row+width}else{row-width},
                    factor==crate::specs::part1_nine_seven_lift(stage),original==old(samples)@,original.len()==samples.len(),
                    forall|i:int|0<=i<original.len()==>-crate::specs::rowwise_fixed_bound(stage as nat)<=#[trigger] original[i]<=crate::specs::rowwise_fixed_bound(stage as nat),
                    forall|i:int|0<=i<samples.len()==>#[trigger] samples[i]==if i<row+x{
                        crate::specs::rowwise_fixed_stage(original,width as nat,height as nat,target,stage)[i]}else{original[i]},
                decreases width-x,
            ))]
            while x < width {
                #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
                crate::deadline::checkpoint_periodic(x)?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::rowwise_fixed_frame(original,samples@,width as nat,height as nat,y as nat,x as nat,target,stage);
                    assert(left==(if y==0{1int}else{y-1})*width) by(nonlinear_arith)
                        requires left==if y==0{width as int}else{row-width},row==y*width;
                    assert(right==(if y+1<height{(y+1) as int}else{y-1})*width) by(nonlinear_arith)
                        requires right==if y+1<height{row+width}else{row-width},row==y*width;
                    crate::specs::rowwise_cell(if y==0{1int}else{y-1},x as int,width as int,height as int);
                    crate::specs::rowwise_cell(if y+1<height{(y+1) as int}else{y-1},x as int,width as int,height as int);
                    crate::specs::rowwise_fixed_neighbors_bound(samples[(row+x) as int],samples[(left+x) as int],samples[(right+x) as int],stage);
                }
                let value = inverse_lifting_neighbors(
                    samples[row + x],
                    samples[left + x],
                    samples[right + x],
                    InverseLiftingStep::Fixed(factor),
                )?;
                #[cfg(verus_keep_ghost)]
                proof! {assert(value==crate::specs::rowwise_fixed_stage(original,width as nat,height as nat,target,stage)[(row+x) as int]);}
                samples[row + x] = value;
                x += 1;
            }
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|i:int|y*width<=i<(y+1)*width implies
                    #[trigger] crate::specs::rowwise_fixed_stage(original,width as nat,height as nat,target,stage)[i]==original[i] by{
                    crate::specs::rowwise_index(y as int,i-y*width,width as int);
                }
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::rowwise_cell(y as int,0,width as int,height as int);
            assert forall|i:int|0<=i<samples.len() implies #[trigger] samples[i]==if i<(y+1)*width{
                crate::specs::rowwise_fixed_stage(original,width as nat,height as nat,target,stage)[i]}else{original[i]} by{}
        }
        y += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(samples@ =~=crate::specs::rowwise_fixed_stage(original,width as nat,height as nat,target,stage));
        crate::specs::rowwise_fixed_stage_bound(original,width as nat,height as nat,target,stage);
    }
    Ok(())
}

#[cfg(all(test, feature = "cooperative-deadlines"))]
mod tests {
    use super::*;
    use std::time::{Duration, Instant};
    #[test]
    fn fixed_row_work_checks_expiry_before_scaling_and_each_lift() {
        let error = DecodeError::DeadlineExceeded;
        assert_eq!(
            crate::deadline::with_decode_deadline(
                Instant::now() + Duration::from_millis(5),
                || {
                    std::thread::sleep(Duration::from_millis(15));
                    assert_eq!(scale_rows(&mut [0; 4096], 2048, 2, true, true), Err(error));
                    for stage in 0..4 {
                        assert_eq!(lift_rows(&mut [0; 4096], 2048, 2, true, stage), Err(error));
                    }
                    Ok(())
                }
            ),
            Err(error)
        );
        assert_eq!(scale_rows(&mut [0; 4], 2, 2, true, true), Ok(()));
    }
}
