use super::WaveletBand;
use super::geometry::low_count;
use super::wavelets::inverse_reversible_bounded;
#[cfg(verus_keep_ghost)]
use super::{sequence_outcome, wavelet_band_view};
use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// Two reversible stages grow this bound to at most 2^32, including rounding.
const INPUT_BOUND: i64 = 1_073_741_824;

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod fixed;
pub(super) use fixed::inverse as inverse_fixed;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == Ok(crate::specs::rowwise_bounded(samples@)),
))]
pub(super) fn bounded(samples: &[i64]) -> Result<bool, DecodeError> {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= samples.len(),
            forall |i:int| 0 <= i < index ==> -1073741824 <= #[trigger] samples[i] <= 1073741824,
        decreases samples.len() - index,
    ))]
    while index < samples.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
        if samples[index] < -INPUT_BOUND || samples[index] > INPUT_BOUND {
            #[cfg(verus_keep_ghost)]
            proof! {assert(!crate::specs::rowwise_bounded(samples@));}
            return Ok(false);
        }
        index += 1;
    }
    Ok(true)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result as int == width as int*height as int,
))]
#[inline]
fn area(width: u32, height: u32) -> u64 {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(0<=width as int*height as int<=u64::MAX) by(nonlinear_arith)
            requires 0<=width<=u32::MAX,0<=height<=u32::MAX;
    }
    (width as u64) * (height as u64)
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
        && area(low.width, height) == length as u64
        && area(low.width, low.height) == low.samples.len() as u64
        && bounded(low.samples)?
        && bounded(high.samples)?)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::rowwise_eligible(
        wavelet_band_view(low), wavelet_band_view(high), height, first, length),
    ensures match result{
        Err(error)=>error==DecodeError::AllocationFailed
            && crate::specs::part2_wavelet_capacity_result(crate::specs::Part2WaveletPlaneOwner::Columns,length as nat,Err(error)),
        Ok(values)=>values@==crate::specs::rowwise_interleaved(wavelet_band_view(low),wavelet_band_view(high),height,first)
            && crate::specs::part2_wavelet_capacity_result(crate::specs::Part2WaveletPlaneOwner::Columns,length as nat,Ok(())),
    },
))]
fn assemble(
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
        crate::specs::rowwise_geometry(wavelet_band_view(low),wavelet_band_view(high),height,first,length);
        assert(length>0) by(nonlinear_arith)
            requires low.width>=2,height>0,(low.width as int)*(height as int)==length;
        crate::specs::rowwise_interleaved_properties(wavelet_band_view(low),wavelet_band_view(high),height,first,length);
    }
    let allocated = crate::allocation::empty_with_capacity(length);
    #[cfg(verus_keep_ghost)]
    proof! {
        let unit=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_wavelet_capacity_observed(crate::specs::Part2WaveletPlaneOwner::Columns,length as nat,unit);
    }
    let mut output = allocated?;
    let width = low.width as usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((height as int)*width==length) by(nonlinear_arith)
            requires width==low.width,(low.width as int)*(height as int)==length;
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost assembled=crate::specs::rowwise_interleaved(wavelet_band_view(low),wavelet_band_view(high),height,first);}
    let mut y = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant y <= height, width == low.width,
            crate::specs::rowwise_eligible(wavelet_band_view(low),wavelet_band_view(high),height,first,length),
            assembled==crate::specs::rowwise_interleaved(wavelet_band_view(low),wavelet_band_view(high),height,first),
            assembled.len()==length,height as int*width as int==length,
            output.len()==y*width,output@==assembled.subrange(0,(y*width) as int),
        decreases height-y,
    ))]
    while y < height as usize {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! {crate::proofs::production_impl::production_index_parity(y);}
        let band = if (y & 1 == 0) == first { low } else { high };
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::rowwise_geometry(wavelet_band_view(low),wavelet_band_view(high),height,first,length);
            crate::specs::rowwise_cell(y as int,0,width as int,height as int);
            assert((y/2)<band.height);
            assert((y/2)*width+width<=band.samples.len()) by(nonlinear_arith)
                requires (y/2)<band.height,
                    band.samples.len()==width*(band.height as int),width>=2;
            assert((y+1)*width<=length) by(nonlinear_arith)
                requires y<height,width>=2,length==width*(height as int);
            assert(output.len() as int+width as int<=usize::MAX);
        }
        let start = (y / 2) * width;
        append_row(&mut output, &band.samples[start..start + width])?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(output@ =~= assembled.subrange(0,((y+1)*width) as int)) by{
                assert forall|i:int|0<=i<(y+1)*width implies
                    #[trigger] output[i]==assembled[i] by{
                    if i>=y*width{
                        crate::specs::rowwise_index(y as int,i-y*width,width as int);
                        assert(assembled[i]==band.samples[(start as int)+i-y*width]);
                    }
                }
            }
        }
        y += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(output@ =~= assembled);
        crate::specs::part2_wavelet_capacity_observed(crate::specs::Part2WaveletPlaneOwner::Columns,length as nat,Ok(()));
    }
    Ok(output)
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
    let rows = assemble(low, high, height, first, length);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=rows{
            crate::specs::rowwise_observed(wavelet_band_view(low),wavelet_band_view(high),height,first,length,Err(error));
        }
    }
    let mut output = rows?;
    let width = low.width as usize;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost assembled=crate::specs::rowwise_interleaved(wavelet_band_view(low),wavelet_band_view(high),height,first);}
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::rowwise_geometry(wavelet_band_view(low),wavelet_band_view(high),height,first,length);
        crate::specs::rowwise_interleaved_properties(wavelet_band_view(low),wavelet_band_view(high),height,first,length);
        assert(output@==assembled);
        assert(assembled.len()==length);
        assert(width as int==low.width as int);
    }
    if height == 1 {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(length==width) by(nonlinear_arith)
                requires height==1,(low.width as int)*(height as int)==length,width==low.width;
            assert(output.len()==width);
            assert(assembled.len()==width);
        }
        if !first {
            let mut x = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant x<=width,height==1,!first,width==low.width,
                    output.len()==width,assembled.len()==width,
                    crate::specs::rowwise_eligible(wavelet_band_view(low),wavelet_band_view(high),height,first,length),
                    assembled==crate::specs::rowwise_interleaved(wavelet_band_view(low),wavelet_band_view(high),height,first),
                    forall|i:int|0<=i<width ==> #[trigger] output[i]==if i<x{assembled[i]>>1}else{assembled[i]},
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
            -(if predict{2147483648int}else{1073741824int})<=#[trigger] old(samples)[i]<=if predict{2147483648int}else{1073741824int},
    ensures result==Ok(()),
        final(samples)@==crate::specs::rowwise_stage(old(samples)@,width as nat,height as nat,target_even,predict),
        forall|i:int|0<=i<final(samples).len()==>
            -(if predict{4294967296int}else{2147483648int})<=#[trigger] final(samples)[i]<=if predict{4294967296int}else{2147483648int},
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
    proof! {
        crate::specs::rowwise_stage_bounded(original,width as nat,height as nat,target_even,predict);
        assert((height as int)*(width as int)==(width as int)*(height as int)) by(nonlinear_arith);
    }
    let mut y = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant width>=2,height>1,width as int*height as int==samples.len(),
            height as int*width as int==samples.len(),
            y<=height,
            original==old(samples)@,samples.len()==original.len(),
            forall|i:int|0<=i<original.len()==>
                -(if predict{2147483648int}else{1073741824int})<=#[trigger] original[i]<=if predict{2147483648int}else{1073741824int},
            forall|i:int|0<=i<samples.len()==>#[trigger] samples[i]==if i<y*width{
                crate::specs::rowwise_stage(original,width as nat,height as nat,target_even,predict)[i]
            }else{original[i]},
        decreases height-y,
    ))]
    while y < height {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! {crate::proofs::production_impl::production_index_parity(y);}
        if (y & 1 == 0) == target_even {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::rowwise_cell(y as int,0,width as int,height as int);
                assert(0<=y*width && y*width+width<=samples.len());
                if y>0{
                    assert(width<=y*width) by(nonlinear_arith) requires y>0,width>=2;
                }
            }
            let row = y * width;
            let left = if y == 0 { width } else { row - width };
            let right = if y + 1 < height {
                row + width
            } else {
                row - width
            };
            let mut x = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant width>=2,height>1,width as int*height as int==samples.len(),
                    height as int*width as int==samples.len(),
                    y<height,(y%2==0)==target_even,x<=width,row==y*width,
                    row+width<=samples.len(),
                    left==if y==0{width as int}else{row-width},
                    right==if y+1<height{row+width}else{row-width},
                    original==old(samples)@,samples.len()==original.len(),
                    forall|i:int|0<=i<original.len()==>
                        -(if predict{2147483648int}else{1073741824int})<=#[trigger] original[i]<=if predict{2147483648int}else{1073741824int},
                    forall|i:int|0<=i<samples.len()==>#[trigger] samples[i]==if i<row+x{
                        crate::specs::rowwise_stage(original,width as nat,height as nat,target_even,predict)[i]
                    }else{original[i]},
                decreases width-x,
            ))]
            while x < width {
                #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
                crate::deadline::checkpoint_periodic(x)?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::rowwise_frame(original,samples@,width as nat,height as nat,y as nat,x as nat,target_even,predict);
                    assert(left==(if y==0{1int}else{y-1})*width) by(nonlinear_arith)
                        requires left==if y==0{width as int}else{row-width},row==y*width;
                    assert(right==(if y+1<height{(y+1) as int}else{y-1})*width) by(nonlinear_arith)
                        requires right==if y+1<height{row+width}else{row-width},row==y*width;
                    assert(samples[(row+x) as int]==original[(row+x) as int]);
                    assert(samples[(left+x) as int]==original[(left+x) as int]);
                    assert(samples[(right+x) as int]==original[(right+x) as int]);
                    crate::specs::rowwise_cell(if y==0{1int}else{y-1},x as int,width as int,height as int);
                    crate::specs::rowwise_cell(if y+1<height{(y+1) as int}else{y-1},x as int,width as int,height as int);
                    assert(left+width<=samples.len() && right+width<=samples.len()) by(nonlinear_arith)
                        requires y<height,height>1,width>=2,row==y*width,
                            left==if y==0{width as int}else{row-width},
                            right==if y+1<height{row+width}else{row-width},
                            (width as int)*(height as int)==samples.len();
                    crate::specs::rowwise_neighbors_bounded(samples[(row+x) as int],samples[(left+x) as int],samples[(right+x) as int],predict);
                }
                let value = inverse_reversible_bounded(
                    samples[row + x],
                    samples[left + x],
                    samples[right + x],
                    predict,
                );
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(value==crate::specs::rowwise_neighbors(
                        original[(row+x) as int],original[(left+x) as int],original[(right+x) as int],predict).get_Ok_0());
                    assert(crate::specs::rowwise_value(original,width as nat,height as nat,y as nat,x as nat,predict)
                        ==crate::specs::rowwise_neighbors(original[(row+x) as int],original[(left+x) as int],original[(right+x) as int],predict).get_Ok_0());
                    assert(value==crate::specs::rowwise_stage(original,width as nat,height as nat,target_even,predict)[(row+x) as int]);
                }
                samples[row + x] = value;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall|i:int|0<=i<samples.len() implies #[trigger] samples[i]==if i<row+x+1{
                        crate::specs::rowwise_stage(original,width as nat,height as nat,target_even,predict)[i]
                    }else{original[i]} by{}
                }
                x += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::rowwise_cell(y as int,0,width as int,height as int);
                assert forall|i:int|0<=i<samples.len() implies #[trigger] samples[i]==if i<(y+1)*width{
                    crate::specs::rowwise_stage(original,width as nat,height as nat,target_even,predict)[i]
                }else{original[i]} by{}
            }
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::rowwise_identity_row(original,width as nat,height as nat,y as nat,target_even,predict);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::rowwise_cell(y as int,0,width as int,height as int);
            assert forall|i:int|0<=i<samples.len() implies #[trigger] samples[i]==if i<(y+1)*width{
                crate::specs::rowwise_stage(original,width as nat,height as nat,target_even,predict)[i]
            }else{original[i]} by{}
        }
        y += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(samples@ =~=crate::specs::rowwise_stage(original,width as nat,height as nat,target_even,predict));
        crate::specs::rowwise_stage_bounded(original,width as nat,height as nat,target_even,predict);
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
