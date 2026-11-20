use super::geometry::low_count;
use super::wavelets::inverse_lifting_neighbors;
use super::{InverseLiftingStep, WaveletBand};
#[cfg(verus_keep_ghost)]
use super::{sequence_outcome, wavelet_band_view};
use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// Two reversible stages grow this bound to at most 2^32, including rounding.
const INPUT_BOUND: i64 = 1 << 30;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == Ok(crate::specs::rowwise_bounded(samples@)),
))]
fn bounded(samples: &[i64]) -> Result<bool, DecodeError> {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= samples.len(),
            forall |i:int| 0 <= i < index ==> -1073741824 <= samples[i] <= 1073741824,
        decreases samples.len() - index,
    ))]
    while index < samples.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
        if samples[index] < -INPUT_BOUND || samples[index] > INPUT_BOUND {
            return Ok(false);
        }
        index += 1;
    }
    Ok(true)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == Ok(crate::specs::rowwise_eligible(
        wavelet_band_view(low), wavelet_band_view(high), height, first, length)),
))]
pub(super) fn eligible(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    height: u32,
    first: bool,
    length: usize,
) -> Result<bool, DecodeError> {
    Ok(low.width >= 2
        && height > 0
        && low.width == high.width
        && low.height == low_count(height, first)
        && high.height == height - low.height
        && low.samples.len().checked_add(high.samples.len()) == Some(length)
        && (low.width as u64) * (height as u64) == length as u64
        && (low.width as u64) * (low.height as u64) == low.samples.len() as u64
        && bounded(low.samples)?
        && bounded(high.samples)?)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::rowwise_eligible(
        wavelet_band_view(low), wavelet_band_view(high), height, first, length),
    ensures crate::specs::rowwise_result(wavelet_band_view(low), wavelet_band_view(high),
        height, first, length, sequence_outcome(result)),
        sequence_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            sequence_outcome(result) == crate::specs::part1_vertical_prefix(
                wavelet_band_view(low), wavelet_band_view(high), height, first, false, length, low.width as nat),
))]
pub(super) fn inverse(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    height: u32,
    first: bool,
    length: usize,
) -> Result<Vec<i64>, DecodeError> {
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::rowwise_interleaved_properties(wavelet_band_view(low),wavelet_band_view(high),height,first,length);
        crate::specs::rowwise_equivalent(wavelet_band_view(low),wavelet_band_view(high),height,first,length);
    }
    let allocated = crate::allocation::empty_with_capacity(length);
    #[cfg(verus_keep_ghost)]
    proof! {
        let unit=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_wavelet_capacity_observed(crate::specs::Part2WaveletPlaneOwner::Columns,length as nat,unit);
        if let Err(error)=allocated{
            crate::specs::rowwise_observed(wavelet_band_view(low),wavelet_band_view(high),height,first,length,Err(error));
        }
    }
    let mut output = allocated?;
    let width = low.width as usize;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost assembled=crate::specs::rowwise_interleaved(wavelet_band_view(low),wavelet_band_view(high),height,first);}
    let mut y = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant y <= height, width == low.width,
            crate::specs::rowwise_eligible(wavelet_band_view(low),wavelet_band_view(high),height,first,length),
            assembled==crate::specs::rowwise_interleaved(wavelet_band_view(low),wavelet_band_view(high),height,first),
            output.len()==y*width,output@==assembled.subrange(0,(y*width) as int),
        decreases height-y,
    ))]
    while y < height as usize {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        let band = if (y % 2 == 0) == first { low } else { high };
        let start = (y / 2) * width;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((y/2)<band.height);
            assert(start+width<=band.samples.len()) by(nonlinear_arith)
                requires (y/2)<band.height, start==(y/2)*width,
                    band.samples.len()==width*(band.height as int),width>=2;
        }
        append_row(&mut output, &band.samples[start..start + width])?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(output@ =~= assembled.subrange(0,((y+1)*width) as int)) by{
                assert forall|i:int|y*width<=i<(y+1)*width implies
                    assembled[i]==band.samples[(start as int)+i-(y*width)] by{
                    assert(i/(width as int)==y) by(nonlinear_arith)
                        requires width>=2,y*width<=i<(y+1)*width;
                    assert(i%(width as int)==i-y*width) by(nonlinear_arith)
                        requires width>=2,y*width<=i<(y+1)*width;
                }
            }
        }
        y += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {assert(output@ =~= assembled);}
    if height == 1 {
        if !first {
            let mut x = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant x<=width,height==1,!first,width==low.width,
                    output.len()==width,assembled.len()==width,
                    forall|i:int|0<=i<width ==> output[i]==if i<x{assembled[i]>>1}else{assembled[i]},
                decreases width-x,
            ))]
            while x < width {
                #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
                crate::deadline::checkpoint_periodic(x)?;
                output[x] >>= 1;
                x += 1;
            }
        }
    } else {
        lift_rows(&mut output, width, height as usize, first, false)?;
        lift_rows(&mut output, width, height as usize, !first, true)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(output@ =~=crate::specs::rowwise_output(wavelet_band_view(low),wavelet_band_view(high),height,first));
        crate::specs::rowwise_equivalent(wavelet_band_view(low),wavelet_band_view(high),height,first,length);
        crate::specs::part2_wavelet_capacity_observed(crate::specs::Part2WaveletPlaneOwner::Columns,length as nat,Ok(()));
        crate::specs::rowwise_observed(wavelet_band_view(low),wavelet_band_view(high),height,first,length,Ok(()));
    }
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(output).len() as int+row.len() as int<=usize::MAX,
    ensures result==Ok(()),final(output)@==old(output)@+row@,
))]
fn append_row(output: &mut Vec<i64>, row: &[i64]) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost original=output@;}
    let mut offset = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant offset<=row.len(),original==old(output)@,
            original.len()+row.len()<=usize::MAX,
            output@==original+row@.subrange(0,offset as int),
        decreases row.len()-offset,
    ))]
    while offset < row.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        let remaining = row.len() - offset;
        let count = if remaining > 1024 { 1024 } else { remaining };
        output.extend_from_slice(&row[offset..offset + count]);
        #[cfg(verus_keep_ghost)]
        proof! {assert(output@ =~=original+row@.subrange(0,(offset+count) as int));}
        offset += count;
    }
    #[cfg(verus_keep_ghost)]
    proof! {assert(row@.subrange(0,row.len() as int) =~=row@);}
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires width>=2,height>1,width as int*height as int==old(samples).len(),
        forall|i:int|0<=i<old(samples).len()==>
            -(if predict{2147483648int}else{1073741824int})<=old(samples)[i]<=if predict{2147483648int}else{1073741824int},
    ensures result==Ok(()),
        final(samples)@==crate::specs::rowwise_stage(old(samples)@,width as nat,height as nat,target_even,predict),
        forall|i:int|0<=i<final(samples).len()==>
            -(if predict{4294967296int}else{2147483648int})<=final(samples)[i]<=if predict{4294967296int}else{2147483648int},
))]
fn lift_rows(
    samples: &mut [i64],
    width: usize,
    height: usize,
    target_even: bool,
    predict: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost original=samples@;}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::rowwise_stage_bounded(original,width as nat,height as nat,target_even,predict);}
    let mut y = if target_even { 0 } else { 1 };
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant width>=2,height>1,width as int*height as int==samples.len(),
            y<=height+1,(y%2==0)==target_even,
            original==old(samples)@,samples.len()==original.len(),
            forall|i:int|0<=i<original.len()==>
                -(if predict{2147483648int}else{1073741824int})<=original[i]<=if predict{2147483648int}else{1073741824int},
            forall|i:int|0<=i<samples.len()==>samples[i]==if i/(width as int)<y{
                crate::specs::rowwise_stage(original,width as nat,height as nat,target_even,predict)[i]
            }else{original[i]},
        decreases height+1-y,
    ))]
    while y < height {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        let row = y * width;
        let left = if y == 0 { width } else { row - width };
        let right = if y + 1 < height {
            row + width
        } else {
            row - width
        };
        let step = if predict {
            InverseLiftingStep::ReversiblePredict
        } else {
            InverseLiftingStep::ReversibleUpdate
        };
        let mut x = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant width>=2,height>1,width as int*height as int==samples.len(),
                y<height,(y%2==0)==target_even,x<=width,row==y*width,
                left==if y==0{width}else{row-width},
                right==if y+1<height{row+width}else{row-width},
                super::lifting_step_view(step)==(if predict{1u8}else{0u8},0i64),
                original==old(samples)@,samples.len()==original.len(),
                forall|i:int|0<=i<original.len()==>
                    -(if predict{2147483648int}else{1073741824int})<=original[i]<=if predict{2147483648int}else{1073741824int},
                forall|i:int|0<=i<samples.len()==>samples[i]==if i/(width as int)<y || (i/(width as int)==y && i%(width as int)<x){
                    crate::specs::rowwise_stage(original,width as nat,height as nat,target_even,predict)[i]
                }else{original[i]},
            decreases width-x,
        ))]
        while x < width {
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint_periodic(x)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert((row+x)/(width as int)==y && (row+x)%(width as int)==x) by(nonlinear_arith)
                    requires row==y*width,width>=2,0<=x<width;
                assert((left+x)/(width as int)==if y==0{1int}else{y-1}) by(nonlinear_arith)
                    requires left==if y==0{width}else{row-width},row==y*width,width>=2,0<=x<width;
                assert((right+x)/(width as int)==if y+1<height{y+1}else{y-1}) by(nonlinear_arith)
                    requires right==if y+1<height{row+width}else{row-width},row==y*width,width>=2,0<=x<width;
                assert(samples[(row+x) as int]==original[(row+x) as int]);
                assert(samples[(left+x) as int]==original[(left+x) as int]);
                assert(samples[(right+x) as int]==original[(right+x) as int]);
                crate::specs::rowwise_neighbors_bounded(samples[(row+x) as int],samples[(left+x) as int],samples[(right+x) as int],predict);
            }
            samples[row + x] = inverse_lifting_neighbors(
                samples[row + x],
                samples[left + x],
                samples[right + x],
                step,
            )?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(samples[(row+x) as int]==crate::specs::rowwise_stage(original,width as nat,height as nat,target_even,predict)[(row+x) as int]);
            }
            x += 1;
        }
        y += 2;
    }
    Ok(())
}

#[cfg(all(test, feature = "cooperative-deadlines"))]
mod deadline_tests {
    use super::*;
    use std::time::{Duration, Instant};

    #[test]
    fn rowwise_work_checks_expiry_before_preflight_copy_and_lift() {
        let error = DecodeError::DeadlineExceeded;
        assert_eq!(
            crate::deadline::with_decode_deadline(
                Instant::now() + Duration::from_millis(5),
                || {
                    std::thread::sleep(Duration::from_millis(15));
                    assert_eq!(bounded(&[0; 2048]), Err(error));
                    assert_eq!(
                        append_row(&mut Vec::with_capacity(2048), &[0; 2048]),
                        Err(error)
                    );
                    assert_eq!(lift_rows(&mut [0; 4096], 2048, 2, true, false), Err(error));
                    Ok(())
                }
            ),
            Err(error),
        );
        assert_eq!(bounded(&[0]), Ok(true));
        let mut output = Vec::with_capacity(2048);
        assert_eq!(append_row(&mut output, &[7; 2048]), Ok(()));
        assert_eq!(output, [7; 2048]);
    }
}
