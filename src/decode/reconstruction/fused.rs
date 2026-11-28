#[cfg(verus_keep_ghost)]
use super::working_subband_view;
use super::{
    CodeBlockPlane, DecodeError, ResourceLimits, SubbandGeometry, WorkingSubband,
    arithmetic_overflow, collect_prepare_coefficients, invalid_decode, inverse_quantize_magnitudes,
    write_quantized_block,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[path = "fused_readable.rs"]
mod readable;
use readable::{ReadablePlane, ReadableRow};

#[derive(Clone, Copy)]
struct Quantizer {
    step: i64,
    roi_shift: u8,
    reversible: bool,
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires plane.plane_valid(),
        x as int+plane.raw_plane().width as int<=geometry.width,
        y as int+plane.raw_plane().height as int<=geometry.height,
    ensures match result{
        Ok(Some(quantizer))=>crate::specs::part2_fused_eligible(working_subband_view(*destination),plane.raw_plane(),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits))
            && quantizer.step==crate::specs::part2_fused_step(geometry,reversible).get_Ok_0()
            && quantizer.roi_shift==geometry.roi_shift && quantizer.reversible==reversible,
        Ok(None)=>!crate::specs::part2_fused_eligible(working_subband_view(*destination),plane.raw_plane(),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)),
        Err(_)=>false,
    },
))]
fn preflight<P: ReadablePlane>(
    plane: P,
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
    let (width, height) = plane.dimensions();
    let width = usize::from(width);
    let height = usize::from(height);
    let coefficient_count = plane.coefficient_count();
    let Some(count) = width.checked_mul(height) else {
        return Ok(None);
    };
    let budget_ok = match (count as u64).checked_mul(8) {
        Some(bytes) => bytes <= limits.maximum_decoded_bytes(),
        None => false,
    };
    if count == 0
        || coefficient_count != count
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
        assert(crate::specs::part2_fused_shape(original,plane.raw_plane(),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)));
        assert(width>0 && height>0) by(nonlinear_arith) requires count>0,count==(width as int)*(height as int);
    }
    let mut row = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant plane.plane_valid(),
            row<=height,width==plane.raw_plane().width,height==plane.raw_plane().height,
            width>0,height>0,count==(width as int)*(height as int),area==(destination.width as int)*(destination.height as int),
            original==working_subband_view(*destination),
            crate::specs::part2_fused_shape(original,plane.raw_plane(),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)),
            step==crate::specs::part2_fused_step(geometry,reversible).get_Ok_0(),step>=0,
            maximum==crate::specs::part2_fused_maximum(step,reversible),
            forall|r:int,c:int|0<=r<row && 0<=c<width ==>             #[trigger] crate::specs::part2_fused_cell_valid(original,plane.raw_plane(),x,y,geometry.roi_shift,step,reversible,r,c),
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
        let source = plane.row(row * width, (row + 1) * width);
        let visited = &destination.visited[start..start + width];
        let mut column = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant column<=width,row<height,width==plane.raw_plane().width,height==plane.raw_plane().height,
                width>0,height>0,original==working_subband_view(*destination),
                crate::specs::part2_fused_shape(original,plane.raw_plane(),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)),
                step==crate::specs::part2_fused_step(geometry,reversible).get_Ok_0(),step>=0,maximum==crate::specs::part2_fused_maximum(step,reversible),
                start==(y as int+row as int)*(destination.width as int)+x as int,
                visited.len()==width,start+width<=original.4.len(),
                (row+1)*width<=plane.raw_plane().coefficients.len(),
                (row+1)*width==row*width+width,
                source.valid(),source.raw_row().len()==width,
                source.raw_row()==plane.raw_plane().coefficients.subrange((row*width) as int,((row+1)*width) as int),
                visited@==original.4.subrange(start as int,(start+width) as int),
                forall|r:int,c:int|0<=r<row && 0<=c<width ==> #[trigger] crate::specs::part2_fused_cell_valid(original,plane.raw_plane(),x,y,geometry.roi_shift,step,reversible,r,c),
                forall|c:int|0<=c<column ==> #[trigger] crate::specs::part2_fused_cell_valid(original,plane.raw_plane(),x,y,geometry.roi_shift,step,reversible,row as int,c),
            decreases width-column,
        ))]
        while column < width {
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint_periodic(column)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(row*width+column<plane.raw_plane().coefficients.len());
            }
            let Some(magnitude) = source.narrow(column)? else {
                #[cfg(verus_keep_ghost)]
                proof! {assert(!crate::specs::part2_fused_cell_valid(original,plane.raw_plane(),x,y,geometry.roi_shift,step,reversible,row as int,column as int));}
                return Ok(None);
            };
            // Maxshift is discontinuous at its threshold: bound each restored value.
            let restored = crate::refinement::maxshift_restore(magnitude, geometry.roi_shift);
            if restored > maximum || visited[column] {
                #[cfg(verus_keep_ghost)]
                proof! {assert(!crate::specs::part2_fused_cell_valid(original,plane.raw_plane(),x,y,geometry.roi_shift,step,reversible,row as int,column as int));}
                return Ok(None);
            }
            #[cfg(verus_keep_ghost)]
            proof! {assert(crate::specs::part2_fused_cell_valid(original,plane.raw_plane(),x,y,geometry.roi_shift,step,reversible,row as int,column as int));}
            column += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|r:int,c:int|0<=r<row+1 && 0<=c<width implies #[trigger] crate::specs::part2_fused_cell_valid(original,plane.raw_plane(),x,y,geometry.roi_shift,step,reversible,r,c) by{}
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
    requires plane.plane_valid(),
        crate::specs::part2_fused_write_admit(working_subband_view(*old(destination)),plane.raw_plane(),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible),
    ensures result==Ok(()),working_subband_view(*final(destination))==crate::specs::part2_fused_rows(
        working_subband_view(*old(destination)),crate::specs::part2_fused_values(plane.raw_plane(),quantizer.roi_shift,quantizer.step,quantizer.reversible),
        plane.raw_plane().width as u32,x,y,plane.raw_plane().height as nat),
))]
fn write<P: ReadablePlane>(
    plane: P,
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
        let ghost values=crate::specs::part2_fused_values(plane.raw_plane(),quantizer.roi_shift,quantizer.step,quantizer.reversible);
    }
    let (width, height) = plane.dimensions();
    let width = usize::from(width);
    let height = usize::from(height);
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_fused_geometry(original,plane.raw_plane(),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible);}
    let mut row = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant plane.plane_valid(),
            row<=height,width==plane.raw_plane().width,height==plane.raw_plane().height,
            original==working_subband_view(*old(destination)),
            values==crate::specs::part2_fused_values(plane.raw_plane(),quantizer.roi_shift,quantizer.step,quantizer.reversible),
            crate::specs::part2_fused_write_admit(original,plane.raw_plane(),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible),
            working_subband_view(*destination)==crate::specs::part2_fused_rows(original,values,width as u32,x,y,row as nat),
        decreases height-row,
    ))]
    while row < height {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_fused_geometry(original,plane.raw_plane(),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible);
            assert((row as int)*(width as int)<=values.len()) by(nonlinear_arith)
                requires row<height,values.len()==(width as int)*(height as int);
            crate::specs::part2_fused_rows_frame(original,values,width as u32,x,y,row as nat);
            crate::specs::part2_fused_span(original.0 as int,original.1 as int,width as int,height as int,x as int,y as int,row as int);
        }
        let start = (y as usize + row) * destination.width as usize + x as usize;
        let source = plane.row(row * width, (row + 1) * width);
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=working_subband_view(*destination);}
        {
            let samples = &mut destination.samples.as_mut_slice()[start..start + width];
            let visited = &mut destination.visited.as_mut_slice()[start..start + width];
            let mut column = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant column<=width,row<height,width==plane.raw_plane().width,height==plane.raw_plane().height,
                original==working_subband_view(*old(destination)),
                values==crate::specs::part2_fused_values(plane.raw_plane(),quantizer.roi_shift,quantizer.step,quantizer.reversible),
                crate::specs::part2_fused_write_admit(original,plane.raw_plane(),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible),
                before==crate::specs::part2_fused_rows(original,values,width as u32,x,y,row as nat),
                start==(y as int+row as int)*(before.0 as int)+x as int,
                samples.len()==width,visited.len()==width,
                0<=start,start+width<=before.3.len(),before.4.len()==before.3.len(),
                (row+1)*width<=plane.raw_plane().coefficients.len(),
                (row+1)*width==row*width+width,
                source.valid(),source.raw_row().len()==width,
                source.raw_row()==plane.raw_plane().coefficients.subrange((row*width) as int,((row+1)*width) as int),
                forall|c:int|0<=c<width ==> #[trigger] samples[c]==if c<column{values[row*width+c]}else{before.3[start+c]},
                forall|c:int|0<=c<width ==> #[trigger] visited[c]==if c<column{true}else{before.4[start+c]},
            decreases width-column,
        ))]
            while column < width {
                #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
                crate::deadline::checkpoint_periodic(column)?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(row*width+column<plane.raw_plane().coefficients.len());
                    assert(crate::specs::part2_fused_cell_valid(original,plane.raw_plane(),x,y,quantizer.roi_shift,quantizer.step,quantizer.reversible,row as int,column as int));
                }
                let (value, negative) = source.bounded(column)?;
                let magnitude = crate::refinement::maxshift_restore(value, quantizer.roi_shift);
                #[cfg(verus_keep_ghost)]
                proof! {crate::specs::part2_fused_limit_bounds(magnitude,quantizer.step,quantizer.reversible);}
                samples[column] = crate::transform::quantize_bounded_magnitude(
                    magnitude,
                    negative,
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
    requires plane.plane_valid(),
    ensures crate::specs::part2_fused_band_result(working_subband_view(*old(destination)),plane.raw_plane(),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits),
            (result,working_subband_view(*final(destination)))),
        result!=Err(DecodeError::AllocationFailed) ==>
        (result,working_subband_view(*final(destination)))==crate::specs::part2_fused_band_value(
            working_subband_view(*old(destination)),plane.raw_plane(),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)),
        result==Err(DecodeError::AllocationFailed) ==> working_subband_view(*final(destination))==working_subband_view(*old(destination)),
        result==Err(DecodeError::AllocationFailed) ==> !crate::specs::part2_fused_eligible(working_subband_view(*old(destination)),plane.raw_plane(),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits))
            && x as int+plane.raw_plane().width as int<=geometry.width
            && y as int+plane.raw_plane().height as int<=geometry.height,
))]
fn place_readable<P: ReadablePlane>(
    plane: P,
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
        crate::specs::part2_fused_band_normal(initial,plane.raw_plane(),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits));
    }
    let (width, height) = plane.dimensions();
    let width = u32::from(width);
    let height = u32::from(height);
    if x.checked_add(width).ok_or_else(arithmetic_overflow)? > geometry.width
        || y.checked_add(height).ok_or_else(arithmetic_overflow)? > geometry.height
    {
        return Err(invalid_decode());
    }
    if let Some(quantizer) = preflight(plane, destination, geometry, x, y, reversible, limits)? {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_fused_band_equivalent(working_subband_view(*destination),plane.raw_plane(),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits));}
        return write(plane, destination, x, y, quantizer);
    }
    let collected = plane.collect();
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_coefficient_collect_frames(plane.raw_plane(),crate::transform::quantized_coefficients_outcome(collected));
        if let Err(error)=collected{
            crate::specs::part2_extraction_place_error(working,seq![geometry],seq![seq![plane.raw_plane()]],position,reversible,
                crate::limits::resource_decoded_bytes_limit(limits),geometry,plane.raw_plane(),error);
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
            crate::specs::part2_extraction_place_quantization_error(working,seq![geometry],seq![seq![plane.raw_plane()]],position,reversible,
                crate::limits::resource_decoded_bytes_limit(limits),geometry,plane.raw_plane(),crate::transform::quantized_coefficients_view(coefficients@),error);
        }
    }
    let quantized = quantized_result?;
    if quantized.fraction_bits() != if reversible { 0 } else { 16 } {
        return Err(invalid_decode());
    }
    write_quantized_block(destination, quantized.samples(), width, height, x, y)
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
    place_readable(
        readable::from_wide(plane),
        destination,
        geometry,
        x,
        y,
        reversible,
        limits,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_fused_band_result(working_subband_view(*old(destination)),plane.view().plane,geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits),
            (result,working_subband_view(*final(destination)))),
        result!=Err(DecodeError::AllocationFailed) ==>
        (result,working_subband_view(*final(destination)))==crate::specs::part2_fused_band_value(
            working_subband_view(*old(destination)),plane.view().plane,geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)),
        result==Err(DecodeError::AllocationFailed) ==> working_subband_view(*final(destination))==working_subband_view(*old(destination)),
        result==Err(DecodeError::AllocationFailed) ==> !crate::specs::part2_fused_eligible(working_subband_view(*old(destination)),plane.view().plane,geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits))
            && x as int+plane.view().plane.width as int<=geometry.width
            && y as int+plane.view().plane.height as int<=geometry.height,
))]
pub(in crate::decode) fn place_private(
    plane: &crate::tier1::PrivateHtDecoder,
    destination: &mut WorkingSubband,
    geometry: SubbandGeometry,
    x: u32,
    y: u32,
    reversible: bool,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    match plane.primary_slices() {
        crate::tier1::PrivatePrimarySlices::Wide(wide) => place_readable(
            readable::from_wide(wide),
            destination,
            geometry,
            x,
            y,
            reversible,
            limits,
        ),
        crate::tier1::PrivatePrimarySlices::Packed(width, height, words) => place_readable(
            readable::from_packed(width, height, words, plane),
            destination,
            geometry,
            x,
            y,
            reversible,
            limits,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result ==> (Ok(()), working_subband_view(*final(destination)))
        == crate::specs::part2_fused_band_value(
            working_subband_view(*old(destination)),
            crate::specs::private_legacy_compact_plane(width, height, words@),
            geometry,
            x,
            y,
            reversible,
            crate::limits::resource_decoded_bytes_limit(limits),
        ),
))]
pub(in crate::decode) fn place_compact_words(
    width: u16,
    height: u16,
    words: &[u64],
    destination: &mut WorkingSubband,
    geometry: SubbandGeometry,
    x: u32,
    y: u32,
    reversible: bool,
    limits: &ResourceLimits,
) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(working_subband_view); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = working_subband_view(*destination);
        let ghost raw_plane = crate::specs::private_legacy_compact_plane(width, height, words@);
    }
    let w_u32 = u32::from(width);
    let h_u32 = u32::from(height);
    let Some(x_end) = x.checked_add(w_u32) else {
        return false;
    };
    let Some(y_end) = y.checked_add(h_u32) else {
        return false;
    };
    if x_end > geometry.width || y_end > geometry.height {
        return false;
    }
    let w = usize::from(width);
    let h = usize::from(height);
    let Some(count) = w.checked_mul(h) else {
        return false;
    };
    let budget_ok = match (count as u64).checked_mul(8) {
        Some(bytes) => bytes <= limits.maximum_decoded_bytes(),
        None => false,
    };
    if count == 0
        || words.len() != count
        || destination.width != geometry.width
        || destination.height != geometry.height
        || geometry.dynamic_range == 0
        || geometry.dynamic_range > 38
        || geometry.quantization_step.exponent > 31
        || geometry.quantization_step.mantissa > 2047
        || !budget_ok
    {
        return false;
    }
    let Some(area) = (destination.width as usize).checked_mul(destination.height as usize) else {
        return false;
    };
    if destination.samples.len() != area || destination.visited.len() != area {
        return false;
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_fused_step_nonnegative(geometry, reversible); }
    let step = if reversible {
        1
    } else {
        let Ok(value) = crate::transform::quantization_step_q16(
            geometry.quantization_step,
            geometry.dynamic_range,
        ) else {
            return false;
        };
        value
    };
    let maximum = if reversible || step == 0 {
        i64::MAX as u64
    } else {
        #[cfg(verus_keep_ghost)]
        proof! {
            vstd::arithmetic::div_mod::lemma_div_by_self(step as int);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(step as int, i64::MAX as int, step as int);
        }
        ((i64::MAX / step) as u64 - 1) / 2
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i: int| 0 <= i < raw_plane.coefficients.len() implies #[trigger] raw_plane.coefficients[i].limbs.len() == 6 by {
            assert(raw_plane.coefficients[i] == crate::specs::compact_coefficient(words@[i]));
        }
        assert(crate::specs::part2_fused_shape(original, raw_plane, geometry, x, y, reversible, crate::limits::resource_decoded_bytes_limit(limits)));
        assert(w > 0 && h > 0) by(nonlinear_arith) requires count > 0, count == (w as int) * (h as int);
    }
    let mut row = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row <= h, w == raw_plane.width, h == raw_plane.height,
            w > 0, h > 0, count == (w as int) * (h as int), count == words.len(),
            raw_plane == crate::specs::private_legacy_compact_plane(width, height, words@),
            area == (destination.width as int) * (destination.height as int),
            original == working_subband_view(*destination),
            crate::specs::part2_fused_shape(original, raw_plane, geometry, x, y, reversible, crate::limits::resource_decoded_bytes_limit(limits)),
            step == crate::specs::part2_fused_step(geometry, reversible).get_Ok_0(), step >= 0,
            maximum == crate::specs::part2_fused_maximum(step, reversible),
            forall|r: int, c: int| 0 <= r < row && 0 <= c < w ==>
                #[trigger] crate::specs::part2_fused_cell_valid(original, raw_plane, x, y, geometry.roi_shift, step, reversible, r, c),
        decreases h - row,
    ))]
    while row < h {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_fused_span(original.0 as int, original.1 as int, w as int, h as int, x as int, y as int, row as int);
            assert((row + 1) * w == row * w + w && (row + 1) * w <= count) by(nonlinear_arith)
                requires row < h, count == (w as int) * (h as int);
        }
        let start = (y as usize + row) * destination.width as usize + x as usize;
        let source: readable::PackedRow<'_> = &words[row * w..(row + 1) * w];
        let visited = &destination.visited[start..start + w];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(source@.map_values(|word: u64| crate::specs::compact_coefficient(word))
                =~= raw_plane.coefficients.subrange((row * w) as int, ((row + 1) * w) as int));
        }
        let mut column = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant column <= w, row < h, w == raw_plane.width, h == raw_plane.height,
                (row + 1) * w == row * w + w,
                (row + 1) * w <= raw_plane.coefficients.len(),
                source.valid(), source.raw_row().len() == w,
                source.raw_row() == raw_plane.coefficients.subrange((row * w) as int, ((row + 1) * w) as int),
                visited@ == original.4.subrange(start as int, (start + w) as int),
                start == (y as int + row as int) * (destination.width as int) + x as int,
                start + w <= original.4.len(),
                original == working_subband_view(*destination),
                maximum == crate::specs::part2_fused_maximum(step, reversible),
                forall|c: int| 0 <= c < column ==>
                    #[trigger] crate::specs::part2_fused_cell_valid(original, raw_plane, x, y, geometry.roi_shift, step, reversible, row as int, c),
            decreases w - column,
        ))]
        while column < w {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(row * w + column < raw_plane.coefficients.len());
            }
            if visited[column] {
                return false;
            }
            let Ok(Some(value)) = source.narrow(column) else {
                return false;
            };
            let restored = crate::refinement::maxshift_restore(value, geometry.roi_shift);
            if restored > maximum {
                return false;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::part2_fused_cell_valid(original, raw_plane, x, y, geometry.roi_shift, step, reversible, row as int, column as int));
            }
            column += 1;
        }
        row += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_fused_eligible(original, raw_plane, geometry, x, y, reversible, crate::limits::resource_decoded_bytes_limit(limits)));
        crate::specs::part2_fused_band_equivalent(original, raw_plane, geometry, x, y, reversible, crate::limits::resource_decoded_bytes_limit(limits));
        crate::specs::part2_fused_geometry(original, raw_plane, x, y, geometry.roi_shift, step, reversible);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost values = crate::specs::part2_fused_values(raw_plane, geometry.roi_shift, step, reversible);
    }
    let mut row = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row <= h, w == raw_plane.width, h == raw_plane.height,
            count == (w as int) * (h as int), count == words.len(),
            raw_plane == crate::specs::private_legacy_compact_plane(width, height, words@),
            original == working_subband_view(*old(destination)),
            values == crate::specs::part2_fused_values(raw_plane, geometry.roi_shift, step, reversible),
            crate::specs::part2_fused_write_admit(original, raw_plane, x, y, geometry.roi_shift, step, reversible),
            working_subband_view(*destination) == crate::specs::part2_fused_rows(original, values, w as u32, x, y, row as nat),
        decreases h - row,
    ))]
    while row < h {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_fused_geometry(original, raw_plane, x, y, geometry.roi_shift, step, reversible);
            assert((row + 1) * w == row * w + w && (row + 1) * w <= count && (row + 1) * w <= values.len()) by(nonlinear_arith)
                requires row < h, count == (w as int) * (h as int), values.len() == (w as int) * (h as int);
            crate::specs::part2_fused_rows_frame(original, values, w as u32, x, y, row as nat);
            crate::specs::part2_fused_span(original.0 as int, original.1 as int, w as int, h as int, x as int, y as int, row as int);
        }
        let start = (y as usize + row) * destination.width as usize + x as usize;
        let source: readable::PackedRow<'_> = &words[row * w..(row + 1) * w];
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = working_subband_view(*destination); }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(source@.map_values(|word: u64| crate::specs::compact_coefficient(word))
                =~= raw_plane.coefficients.subrange((row * w) as int, ((row + 1) * w) as int));
        }
        {
            let samples = &mut destination.samples.as_mut_slice()[start..start + w];
            let visited = &mut destination.visited.as_mut_slice()[start..start + w];
            let mut column = 0_usize;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant column <= w, row < h, w == raw_plane.width, h == raw_plane.height,
                    original == working_subband_view(*old(destination)),
                    values == crate::specs::part2_fused_values(raw_plane, geometry.roi_shift, step, reversible),
                    crate::specs::part2_fused_write_admit(original, raw_plane, x, y, geometry.roi_shift, step, reversible),
                    before == crate::specs::part2_fused_rows(original, values, w as u32, x, y, row as nat),
                    start == (y as int + row as int) * (before.0 as int) + x as int,
                    samples.len() == w, visited.len() == w,
                    0 <= start, start + w <= before.3.len(), before.4.len() == before.3.len(),
                    (row + 1) * w <= raw_plane.coefficients.len(),
                    (row + 1) * w == row * w + w,
                    source.valid(), source.raw_row().len() == w,
                    source.raw_row() == raw_plane.coefficients.subrange((row * w) as int, ((row + 1) * w) as int),
                    forall|c: int| 0 <= c < w ==> #[trigger] samples[c] == if c < column { values[row * w + c] } else { before.3[start + c] },
                    forall|c: int| 0 <= c < w ==> #[trigger] visited[c] == if c < column { true } else { before.4[start + c] },
                decreases w - column,
            ))]
            while column < w {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(row * w + column < raw_plane.coefficients.len());
                    assert(crate::specs::part2_fused_cell_valid(original, raw_plane, x, y, geometry.roi_shift, step, reversible, row as int, column as int));
                }
                let Ok((value, negative)) = source.bounded(column) else {
                    return false;
                };
                let magnitude = crate::refinement::maxshift_restore(value, geometry.roi_shift);
                #[cfg(verus_keep_ghost)]
                proof! { crate::specs::part2_fused_limit_bounds(magnitude, step, reversible); }
                samples[column] = crate::transform::quantize_bounded_magnitude(
                    magnitude, negative, step, reversible,
                );
                visited[column] = true;
                #[cfg(verus_keep_ghost)]
                proof! { assert(samples[column as int] == values[(row * w + column) as int]); }
                column += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(samples@ =~= values.subrange((row * w) as int, ((row + 1) * w) as int));
                assert(visited@ =~= Seq::new(w as nat, |_: int| true));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(working_subband_view(*destination) == crate::specs::part2_fused_row(before, values, w as u32, x, y, row as nat, w as nat)) by {
                assert(destination.samples@ =~= crate::specs::part2_fused_row(before, values, w as u32, x, y, row as nat, w as nat).3);
                assert(destination.visited@ =~= crate::specs::part2_fused_row(before, values, w as u32, x, y, row as nat, w as nat).4);
            }
        }
        row += 1;
    }
    true
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires (width as nat) * (height as nat) <= usize::MAX,
    ensures result ==> (Ok(()), working_subband_view(*final(destination)))
        == crate::specs::part2_fused_band_value(
            working_subband_view(*old(destination)),
            crate::specs::private_legacy_empty_plane(width, height),
            geometry,
            x,
            y,
            reversible,
            crate::limits::resource_decoded_bytes_limit(limits),
        ),
))]
pub(in crate::decode) fn place_empty_block(
    width: u16,
    height: u16,
    destination: &mut WorkingSubband,
    geometry: SubbandGeometry,
    x: u32,
    y: u32,
    reversible: bool,
    limits: &ResourceLimits,
) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(working_subband_view); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = working_subband_view(*destination);
        let ghost raw_plane = crate::specs::private_legacy_empty_plane(width, height);
    }
    let w_u32 = u32::from(width);
    let h_u32 = u32::from(height);
    let Some(x_end) = x.checked_add(w_u32) else {
        return false;
    };
    let Some(y_end) = y.checked_add(h_u32) else {
        return false;
    };
    if x_end > geometry.width || y_end > geometry.height {
        return false;
    }
    let w = usize::from(width);
    let h = usize::from(height);
    let count = w * h;
    let budget_ok = match (count as u64).checked_mul(8) {
        Some(bytes) => bytes <= limits.maximum_decoded_bytes(),
        None => false,
    };
    if count == 0
        || destination.width != geometry.width
        || destination.height != geometry.height
        || geometry.dynamic_range == 0
        || geometry.dynamic_range > 38
        || geometry.quantization_step.exponent > 31
        || geometry.quantization_step.mantissa > 2047
        || !budget_ok
    {
        return false;
    }
    let Some(area) = (destination.width as usize).checked_mul(destination.height as usize) else {
        return false;
    };
    if destination.samples.len() != area || destination.visited.len() != area {
        return false;
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_fused_step_nonnegative(geometry, reversible); }
    let step = if reversible {
        1
    } else {
        let Ok(value) = crate::transform::quantization_step_q16(
            geometry.quantization_step,
            geometry.dynamic_range,
        ) else {
            return false;
        };
        value
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::tier1_empty_coefficient().limbs.len() == 6) by(compute);
        assert(crate::specs::part2_narrow_magnitude(crate::specs::tier1_empty_coefficient()) == Some(0u64)) by(compute);
        assert(geometry.roi_shift < 64u8 ==> (1u64 << geometry.roi_shift) > 0u64) by(bit_vector);
        assert(crate::specs::part1_maxshift_restore(0u64, geometry.roi_shift) == 0u64);
        assert(!crate::specs::tier1_empty_coefficient().significant);
        assert(crate::specs::part2_fused_shape(original, raw_plane, geometry, x, y, reversible, crate::limits::resource_decoded_bytes_limit(limits)));
        assert(w > 0 && h > 0) by(nonlinear_arith) requires count > 0, count == (w as int) * (h as int);
    }
    let mut row = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row <= h, w == raw_plane.width, h == raw_plane.height,
            w > 0, h > 0, count == (w as int) * (h as int),
            raw_plane == crate::specs::private_legacy_empty_plane(width, height),
            crate::specs::part1_maxshift_restore(0u64, geometry.roi_shift) == 0u64,
            crate::specs::part2_narrow_magnitude(crate::specs::tier1_empty_coefficient()) == Some(0u64),
            area == (destination.width as int) * (destination.height as int),
            original == working_subband_view(*destination),
            crate::specs::part2_fused_shape(original, raw_plane, geometry, x, y, reversible, crate::limits::resource_decoded_bytes_limit(limits)),
            step == crate::specs::part2_fused_step(geometry, reversible).get_Ok_0(), step >= 0,
            forall|r: int, c: int| 0 <= r < row && 0 <= c < w ==>
                #[trigger] crate::specs::part2_fused_cell_valid(original, raw_plane, x, y, geometry.roi_shift, step, reversible, r, c),
        decreases h - row,
    ))]
    while row < h {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_fused_span(original.0 as int, original.1 as int, w as int, h as int, x as int, y as int, row as int);
            assert((row + 1) * w == row * w + w && (row + 1) * w <= count) by(nonlinear_arith)
                requires row < h, count == (w as int) * (h as int);
        }
        let start = (y as usize + row) * destination.width as usize + x as usize;
        let visited = &destination.visited[start..start + w];
        let mut column = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant column <= w, row < h, w == raw_plane.width, h == raw_plane.height,
                (row + 1) * w == row * w + w,
                (row + 1) * w <= raw_plane.coefficients.len(),
                raw_plane == crate::specs::private_legacy_empty_plane(width, height),
                crate::specs::part1_maxshift_restore(0u64, geometry.roi_shift) == 0u64,
                crate::specs::part2_narrow_magnitude(crate::specs::tier1_empty_coefficient()) == Some(0u64),
                visited@ == original.4.subrange(start as int, (start + w) as int),
                start == (y as int + row as int) * (destination.width as int) + x as int,
                start + w <= original.4.len(),
                original == working_subband_view(*destination),
                forall|c: int| 0 <= c < column ==>
                    #[trigger] crate::specs::part2_fused_cell_valid(original, raw_plane, x, y, geometry.roi_shift, step, reversible, row as int, c),
            decreases w - column,
        ))]
        while column < w {
            if visited[column] {
                return false;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(row * w + column < raw_plane.coefficients.len());
                assert(raw_plane.coefficients[row * w + column] == crate::specs::tier1_empty_coefficient());
                assert(crate::specs::part2_fused_cell_valid(original, raw_plane, x, y, geometry.roi_shift, step, reversible, row as int, column as int));
            }
            column += 1;
        }
        row += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_fused_eligible(original, raw_plane, geometry, x, y, reversible, crate::limits::resource_decoded_bytes_limit(limits)));
        crate::specs::part2_fused_band_equivalent(original, raw_plane, geometry, x, y, reversible, crate::limits::resource_decoded_bytes_limit(limits));
        crate::specs::part2_fused_geometry(original, raw_plane, x, y, geometry.roi_shift, step, reversible);
        crate::specs::part2_fused_limit_bounds(0, step, reversible);
    }
    let zero_sample = crate::transform::quantize_bounded_magnitude(0, false, step, reversible);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost values = crate::specs::part2_fused_values(raw_plane, geometry.roi_shift, step, reversible);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i: int| 0 <= i < count implies values[i] == zero_sample by {
            assert(raw_plane.coefficients[i] == crate::specs::tier1_empty_coefficient());
            assert(crate::specs::part2_narrow_magnitude(raw_plane.coefficients[i]) == Some(0u64));
            assert(crate::specs::part1_maxshift_restore(0u64, geometry.roi_shift) == 0u64);
        }
        assert(values =~= Seq::new(count as nat, |_: int| zero_sample));
    }
    let mut row = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row <= h, w == raw_plane.width, h == raw_plane.height,
            original == working_subband_view(*old(destination)),
            values == crate::specs::part2_fused_values(raw_plane, geometry.roi_shift, step, reversible),
            values == Seq::new(count as nat, |_: int| zero_sample),
            crate::specs::part2_fused_write_admit(original, raw_plane, x, y, geometry.roi_shift, step, reversible),
            working_subband_view(*destination) == crate::specs::part2_fused_rows(original, values, w as u32, x, y, row as nat),
        decreases h - row,
    ))]
    while row < h {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_fused_geometry(original, raw_plane, x, y, geometry.roi_shift, step, reversible);
            assert((row + 1) * w == row * w + w && (row + 1) * w <= values.len()) by(nonlinear_arith)
                requires row < h, values.len() == (w as int) * (h as int);
            crate::specs::part2_fused_rows_frame(original, values, w as u32, x, y, row as nat);
            crate::specs::part2_fused_span(original.0 as int, original.1 as int, w as int, h as int, x as int, y as int, row as int);
        }
        let start = (y as usize + row) * destination.width as usize + x as usize;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = working_subband_view(*destination); }
        {
            let samples = &mut destination.samples.as_mut_slice()[start..start + w];
            let visited = &mut destination.visited.as_mut_slice()[start..start + w];
            let mut column = 0_usize;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant column <= w, row < h,
                    samples.len() == w, visited.len() == w,
                    0 <= start, start + w <= before.3.len(), before.4.len() == before.3.len(),
                    forall|c: int| 0 <= c < w ==> #[trigger] samples[c] == if c < column { zero_sample } else { before.3[start + c] },
                    forall|c: int| 0 <= c < w ==> #[trigger] visited[c] == if c < column { true } else { before.4[start + c] },
                decreases w - column,
            ))]
            while column < w {
                samples[column] = zero_sample;
                visited[column] = true;
                column += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(samples@ =~= values.subrange((row * w) as int, ((row + 1) * w) as int));
                assert(visited@ =~= Seq::new(w as nat, |_: int| true));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(working_subband_view(*destination) == crate::specs::part2_fused_row(before, values, w as u32, x, y, row as nat, w as nat)) by {
                assert(destination.samples@ =~= crate::specs::part2_fused_row(before, values, w as u32, x, y, row as nat, w as nat).3);
                assert(destination.visited@ =~= crate::specs::part2_fused_row(before, values, w as u32, x, y, row as nat, w as nat).4);
            }
        }
        row += 1;
    }
    true
}

#[cfg(test)]
#[path = "fused_tests.rs"]
mod tests;
