#[cfg(verus_keep_ghost)]
use super::working_subband_view;
use super::{
    CodeBlockPlane, DecodeError, ResourceLimits, SubbandGeometry, WorkingSubband,
    arithmetic_overflow, collect_prepare_coefficients, invalid_decode, inverse_quantize_magnitudes,
    write_quantized_block,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
struct Quantizer {
    step: i64,
    roi_shift: u8,
    reversible: bool,
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires x as int+crate::tier1::code_block_plane_view(plane).width as int<=geometry.width,
        y as int+crate::tier1::code_block_plane_view(plane).height as int<=geometry.height,
    ensures match result{
        Ok(Some(quantizer))=>crate::specs::part2_fused_eligible(working_subband_view(*destination),crate::tier1::code_block_plane_view(plane),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits))
            && quantizer.step==crate::specs::part2_fused_step(geometry,reversible).get_Ok_0()
            && quantizer.roi_shift==geometry.roi_shift && quantizer.reversible==reversible,
        Ok(None)=>!crate::specs::part2_fused_eligible(working_subband_view(*destination),crate::tier1::code_block_plane_view(plane),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)),
        Err(_)=>false,
    },
))]
fn preflight(
    plane: &CodeBlockPlane,
    destination: &WorkingSubband,
    geometry: SubbandGeometry,
    x: u32,
    y: u32,
    reversible: bool,
    limits: &ResourceLimits,
) -> Result<Option<Quantizer>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {reveal(working_subband_view);}
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost original=working_subband_view(*destination);}
    let width = usize::from(plane.width());
    let height = usize::from(plane.height());
    let Some(count) = width.checked_mul(height) else {
        return Ok(None);
    };
    let budget_ok = match (count as u64).checked_mul(8) {
        Some(bytes) => bytes <= limits.maximum_decoded_bytes(),
        None => false,
    };
    if count == 0
        || plane.coefficients().len() != count
        || destination.width != geometry.width
        || destination.height != geometry.height
        || geometry.dynamic_range == 0
        || geometry.dynamic_range > 38
        || geometry.quantization_step.exponent > 31
        || geometry.quantization_step.mantissa > 2047
        || !budget_ok
    {
        return Ok(None);
    }
    let Some(area) = (destination.width as usize).checked_mul(destination.height as usize) else {
        return Ok(None);
    };
    if destination.samples.len() != area || destination.visited.len() != area {
        return Ok(None);
    }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_fused_step_nonnegative(geometry,reversible);}
    let step = if reversible {
        1
    } else {
        let Ok(value) = crate::transform::quantization_step_q16(
            geometry.quantization_step,
            geometry.dynamic_range,
        ) else {
            return Ok(None);
        };
        value
    };
    let maximum = if reversible || step == 0 {
        i64::MAX as u64
    } else {
        #[cfg(verus_keep_ghost)]
        proof! {
            vstd::arithmetic::div_mod::lemma_div_by_self(step as int);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(step as int,i64::MAX as int,step as int);
        }
        ((i64::MAX / step) as u64 - 1) / 2
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_fused_shape(original,crate::tier1::code_block_plane_view(plane),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)));
        assert(width>0 && height>0) by(nonlinear_arith) requires count>0,count==(width as int)*(height as int);
    }
    let mut row = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row<=height,width==crate::tier1::code_block_plane_view(plane).width,height==crate::tier1::code_block_plane_view(plane).height,
            width>0,height>0,count==(width as int)*(height as int),area==(destination.width as int)*(destination.height as int),
            original==working_subband_view(*destination),
            crate::specs::part2_fused_shape(original,crate::tier1::code_block_plane_view(plane),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)),
            step==crate::specs::part2_fused_step(geometry,reversible).get_Ok_0(),step>=0,
            maximum==crate::specs::part2_fused_maximum(step,reversible),
            forall|r:int,c:int|0<=r<row && 0<=c<width ==> #[trigger] crate::specs::part2_fused_cell_valid(original,crate::tier1::code_block_plane_view(plane),x,y,geometry.roi_shift,step,reversible,r,c),
        decreases height-row,
    ))]
    while row < height {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_fused_span(destination.width as int,destination.height as int,width as int,height as int,x as int,y as int,row as int);
        }
        let start = (y as usize + row) * destination.width as usize + x as usize;
        let source = &plane.coefficients()[row * width..(row + 1) * width];
        let visited = &destination.visited[start..start + width];
        #[cfg(verus_keep_ghost)]
        proof! {assert(crate::tier1::coefficient_raw_views(source@) =~=crate::tier1::code_block_plane_view(plane).coefficients.subrange((row*width) as int,((row+1)*width) as int));}
        let mut column = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant column<=width,row<height,width==crate::tier1::code_block_plane_view(plane).width,height==crate::tier1::code_block_plane_view(plane).height,
                width>0,height>0,original==working_subband_view(*destination),
                crate::specs::part2_fused_shape(original,crate::tier1::code_block_plane_view(plane),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)),
                step==crate::specs::part2_fused_step(geometry,reversible).get_Ok_0(),step>=0,maximum==crate::specs::part2_fused_maximum(step,reversible),
                start==(y as int+row as int)*(destination.width as int)+x as int,
                source.len()==width,visited.len()==width,start+width<=original.4.len(),
                (row+1)*width<=crate::tier1::code_block_plane_view(plane).coefficients.len(),
                (row+1)*width==row*width+width,
                visited@==original.4.subrange(start as int,(start+width) as int),
                crate::tier1::coefficient_raw_views(source@)==crate::tier1::code_block_plane_view(plane).coefficients.subrange((row*width) as int,((row+1)*width) as int),
                forall|r:int,c:int|0<=r<row && 0<=c<width ==> #[trigger] crate::specs::part2_fused_cell_valid(original,crate::tier1::code_block_plane_view(plane),x,y,geometry.roi_shift,step,reversible,r,c),
                forall|c:int|0<=c<column ==> #[trigger] crate::specs::part2_fused_cell_valid(original,crate::tier1::code_block_plane_view(plane),x,y,geometry.roi_shift,step,reversible,row as int,c),
            decreases width-column,
        ))]
        while column < width {
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint_periodic(column)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(row*width+column<crate::tier1::code_block_plane_view(plane).coefficients.len());
                assert(crate::tier1::coefficient_raw_views(source@)[column as int]==crate::tier1::coefficient_raw_view(source@[column as int]));
                assert(crate::tier1::coefficient_raw_view(source@[column as int])==crate::tier1::code_block_plane_view(plane).coefficients[(row*width+column) as int]);
            }
            let Some(magnitude) = source[column].narrow_reconstructed_magnitude() else {
                #[cfg(verus_keep_ghost)]
                proof! {assert(!crate::specs::part2_fused_cell_valid(original,crate::tier1::code_block_plane_view(plane),x,y,geometry.roi_shift,step,reversible,row as int,column as int));}
                return Ok(None);
            };
            // Maxshift is discontinuous at its threshold: bound each restored value.
            let restored = crate::refinement::maxshift_restore(magnitude, geometry.roi_shift);
            if restored > maximum || visited[column] {
                #[cfg(verus_keep_ghost)]
                proof! {assert(!crate::specs::part2_fused_cell_valid(original,crate::tier1::code_block_plane_view(plane),x,y,geometry.roi_shift,step,reversible,row as int,column as int));}
                return Ok(None);
            }
            #[cfg(verus_keep_ghost)]
            proof! {assert(crate::specs::part2_fused_cell_valid(original,crate::tier1::code_block_plane_view(plane),x,y,geometry.roi_shift,step,reversible,row as int,column as int));}
            column += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|r:int,c:int|0<=r<row+1 && 0<=c<width implies #[trigger] crate::specs::part2_fused_cell_valid(original,crate::tier1::code_block_plane_view(plane),x,y,geometry.roi_shift,step,reversible,r,c) by{}
        }
        row += 1;
    }
    Ok(Some(Quantizer {
        step,
        roi_shift: geometry.roi_shift,
        reversible,
    }))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::part2_fused_write_admit(working_subband_view(*old(destination)),crate::tier1::code_block_plane_view(plane),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible),
    ensures result==Ok(()),working_subband_view(*final(destination))==crate::specs::part2_fused_rows(
        working_subband_view(*old(destination)),crate::specs::part2_fused_values(crate::tier1::code_block_plane_view(plane),quantizer.roi_shift,quantizer.step,quantizer.reversible),
        crate::tier1::code_block_plane_view(plane).width as u32,x,y,crate::tier1::code_block_plane_view(plane).height as nat),
))]
fn write(
    plane: &CodeBlockPlane,
    destination: &mut WorkingSubband,
    x: u32,
    y: u32,
    quantizer: Quantizer,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {reveal(working_subband_view);}
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original=working_subband_view(*destination);
        let ghost values=crate::specs::part2_fused_values(crate::tier1::code_block_plane_view(plane),quantizer.roi_shift,quantizer.step,quantizer.reversible);
    }
    let width = usize::from(plane.width());
    let height = usize::from(plane.height());
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_fused_geometry(original,crate::tier1::code_block_plane_view(plane),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible);}
    let mut row = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row<=height,width==crate::tier1::code_block_plane_view(plane).width,height==crate::tier1::code_block_plane_view(plane).height,
            original==working_subband_view(*old(destination)),
            values==crate::specs::part2_fused_values(crate::tier1::code_block_plane_view(plane),quantizer.roi_shift,quantizer.step,quantizer.reversible),
            crate::specs::part2_fused_write_admit(original,crate::tier1::code_block_plane_view(plane),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible),
            working_subband_view(*destination)==crate::specs::part2_fused_rows(original,values,width as u32,x,y,row as nat),
        decreases height-row,
    ))]
    while row < height {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_fused_geometry(original,crate::tier1::code_block_plane_view(plane),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible);
            assert((row as int)*(width as int)<=values.len()) by(nonlinear_arith)
                requires row<height,values.len()==(width as int)*(height as int);
            crate::specs::part2_fused_rows_frame(original,values,width as u32,x,y,row as nat);
            crate::specs::part2_fused_span(original.0 as int,original.1 as int,width as int,height as int,x as int,y as int,row as int);
        }
        let start = (y as usize + row) * destination.width as usize + x as usize;
        let source = &plane.coefficients()[row * width..(row + 1) * width];
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=working_subband_view(*destination);}
        #[cfg(verus_keep_ghost)]
        proof! {assert(crate::tier1::coefficient_raw_views(source@) =~=crate::tier1::code_block_plane_view(plane).coefficients.subrange((row*width) as int,((row+1)*width) as int));}
        {
            let samples = &mut destination.samples.as_mut_slice()[start..start + width];
            let visited = &mut destination.visited.as_mut_slice()[start..start + width];
            let mut column = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant column<=width,row<height,width==crate::tier1::code_block_plane_view(plane).width,height==crate::tier1::code_block_plane_view(plane).height,
                original==working_subband_view(*old(destination)),
                values==crate::specs::part2_fused_values(crate::tier1::code_block_plane_view(plane),quantizer.roi_shift,quantizer.step,quantizer.reversible),
                crate::specs::part2_fused_write_admit(original,crate::tier1::code_block_plane_view(plane),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible),
                before==crate::specs::part2_fused_rows(original,values,width as u32,x,y,row as nat),
                start==(y as int+row as int)*(before.0 as int)+x as int,
                samples.len()==width,visited.len()==width,source.len()==width,
                0<=start,start+width<=before.3.len(),before.4.len()==before.3.len(),
                (row+1)*width<=crate::tier1::code_block_plane_view(plane).coefficients.len(),
                (row+1)*width==row*width+width,
                crate::tier1::coefficient_raw_views(source@)==crate::tier1::code_block_plane_view(plane).coefficients.subrange((row*width) as int,((row+1)*width) as int),
                forall|c:int|0<=c<width ==> #[trigger] samples[c]==if c<column{values[row*width+c]}else{before.3[start+c]},
                forall|c:int|0<=c<width ==> #[trigger] visited[c]==if c<column{true}else{before.4[start+c]},
            decreases width-column,
        ))]
            while column < width {
                #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
                crate::deadline::checkpoint_periodic(column)?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(row*width+column<crate::tier1::code_block_plane_view(plane).coefficients.len());
                    assert(crate::tier1::coefficient_raw_views(source@)[column as int]==crate::tier1::coefficient_raw_view(source@[column as int]));
                    assert(crate::tier1::coefficient_raw_view(source@[column as int])==crate::tier1::code_block_plane_view(plane).coefficients[(row*width+column) as int]);
                    assert(crate::specs::part2_fused_cell_valid(original,crate::tier1::code_block_plane_view(plane),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible,row as int,column as int));
                }
                let coefficient = &source[column];
                let magnitude = crate::refinement::maxshift_restore(
                    coefficient.reconstructed_magnitude_bounded(),
                    quantizer.roi_shift,
                );
                #[cfg(verus_keep_ghost)]
                proof! {crate::specs::part2_fused_limit_bounds(magnitude,quantizer.step,quantizer.reversible);}
                samples[column] = crate::transform::quantize_bounded_magnitude(
                    magnitude,
                    coefficient.reconstructed_negative(),
                    quantizer.step,
                    quantizer.reversible,
                );
                visited[column] = true;
                #[cfg(verus_keep_ghost)]
                proof! {assert(samples[column as int]==values[(row*width+column) as int]);}
                column += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(samples@ =~=values.subrange((row*width) as int,((row+1)*width) as int));
                assert(visited@ =~=Seq::new(width as nat,|_:int|true));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(working_subband_view(*destination)==crate::specs::part2_fused_row(before,values,width as u32,x,y,row as nat,width as nat)) by{
                assert(destination.samples@ =~=crate::specs::part2_fused_row(before,values,width as u32,x,y,row as nat,width as nat).3);
                assert(destination.visited@ =~=crate::specs::part2_fused_row(before,values,width as u32,x,y,row as nat,width as nat).4);
            }
        }
        row += 1;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_fused_band_result(working_subband_view(*old(destination)),crate::tier1::code_block_plane_view(plane),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits),
            (result,working_subband_view(*final(destination)))),
        result!=Err(DecodeError::AllocationFailed) ==>
        (result,working_subband_view(*final(destination)))==crate::specs::part2_fused_band_value(
            working_subband_view(*old(destination)),crate::tier1::code_block_plane_view(plane),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)),
        result==Err(DecodeError::AllocationFailed) ==> working_subband_view(*final(destination))==working_subband_view(*old(destination)),
        result==Err(DecodeError::AllocationFailed) ==> !crate::specs::part2_fused_eligible(working_subband_view(*old(destination)),crate::tier1::code_block_plane_view(plane),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits))
            && x as int+crate::tier1::code_block_plane_view(plane).width as int<=geometry.width
            && y as int+crate::tier1::code_block_plane_view(plane).height as int<=geometry.height,
))]
pub(in crate::decode) fn place(
    plane: &CodeBlockPlane,
    destination: &mut WorkingSubband,
    geometry: SubbandGeometry,
    x: u32,
    y: u32,
    reversible: bool,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial=working_subband_view(*destination);
        let ghost working=(seq![initial],0u64);
        let ghost position=crate::specs::part2_fused_position(x,y);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_fused_band_normal(initial,crate::tier1::code_block_plane_view(plane),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits));
    }
    let width = u32::from(plane.width());
    let height = u32::from(plane.height());
    if x.checked_add(width).ok_or_else(arithmetic_overflow)? > geometry.width
        || y.checked_add(height).ok_or_else(arithmetic_overflow)? > geometry.height
    {
        return Err(invalid_decode());
    }
    if let Some(quantizer) = preflight(plane, destination, geometry, x, y, reversible, limits)? {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_fused_band_equivalent(working_subband_view(*destination),crate::tier1::code_block_plane_view(plane),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits));}
        return write(plane, destination, x, y, quantizer);
    }
    let collected = collect_prepare_coefficients(plane);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_coefficient_collect_frames(crate::tier1::code_block_plane_view(plane),crate::transform::quantized_coefficients_outcome(collected));
        if let Err(error)=collected{
            crate::specs::part2_extraction_place_error(working,seq![geometry],seq![seq![crate::tier1::code_block_plane_view(plane)]],position,reversible,
                crate::limits::resource_decoded_bytes_limit(limits),geometry,crate::tier1::code_block_plane_view(plane),error);
        }
    }
    let coefficients = collected?;
    let quantized_result = inverse_quantize_magnitudes(
        &coefficients,
        geometry.quantization_step,
        geometry.dynamic_range,
        reversible,
        geometry.roi_shift,
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=quantized_result{
            crate::specs::part2_extraction_place_quantization_error(working,seq![geometry],seq![seq![crate::tier1::code_block_plane_view(plane)]],position,reversible,
                crate::limits::resource_decoded_bytes_limit(limits),geometry,crate::tier1::code_block_plane_view(plane),crate::transform::quantized_coefficients_view(coefficients@),error);
        }
    }
    let quantized = quantized_result?;
    if quantized.fraction_bits() != if reversible { 0 } else { 16 } {
        return Err(invalid_decode());
    }
    write_quantized_block(destination, quantized.samples(), width, height, x, y)
}

#[cfg(test)]
#[path = "fused_tests.rs"]
mod tests;
