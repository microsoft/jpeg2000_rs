#[cfg(verus_keep_ghost)]
use super::Resource;
use super::{
    CodeBlockDecodeRequest, ComponentTransform, DecodeError, DecodedCodeBlock, DecodedImage,
    DecodedSubband, ImageSize, PlacedCodeBlock, ResourceLimits, Tier1CodeBlockDecoder,
    TileComponent, apply_irreversible_component_transform, apply_reversible_component_transform,
    arithmetic_overflow, assemble_image, checked_index, decode_code_block_contribution_body,
    invalid_decode, inverse_quantize_magnitudes,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl DecodedCodeBlock {
    pub const fn width(&self) -> u16 {
        self.width
    }
}

impl DecodedSubband {
    pub const fn width(&self) -> u32 {
        self.width
    }

    pub const fn height(&self) -> u32 {
        self.height
    }

    pub const fn fraction_bits(&self) -> u8 {
        self.fraction_bits
    }

    pub fn samples(&self) -> &[i64] {
        &self.samples
    }
}

pub fn decode_subband(
    width: u32,
    height: u32,
    blocks: &[PlacedCodeBlock<'_>],
    limits: &ResourceLimits,
) -> Result<DecodedSubband, DecodeError> {
    if width == 0 || height == 0 || blocks.is_empty() {
        return Err(invalid_decode());
    }
    let length = usize::try_from(width)
        .map_err(|_| arithmetic_overflow())?
        .checked_mul(usize::try_from(height).map_err(|_| arithmetic_overflow())?)
        .ok_or_else(arithmetic_overflow)?;
    let bytes = (length as u64)
        .checked_mul(8)
        .ok_or_else(arithmetic_overflow)?;
    if bytes > limits.maximum_decoded_bytes() {
        return Err(DecodeError::limit(
            crate::Resource::DecodedBytes,
            limits.maximum_decoded_bytes(),
            bytes,
        ));
    }
    let mut samples = vec![0_i64; length];
    let mut visited = vec![false; length];
    let mut fraction_bits = None;
    let mut block_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant block_index <= blocks.len(),
            decreases blocks.len() - block_index,
        )
    )]
    while block_index < blocks.len() {
        let placed = blocks[block_index];
        let block = decode_code_block(placed.request, limits)?;
        if fraction_bits.is_some() && fraction_bits != Some(block.fraction_bits()) {
            return Err(invalid_decode());
        }
        fraction_bits = Some(block.fraction_bits());
        let block_width = u32::from(block.width());
        let block_height = u32::from(block.height());
        if placed
            .x
            .checked_add(block_width)
            .ok_or_else(arithmetic_overflow)?
            > width
            || placed
                .y
                .checked_add(block_height)
                .ok_or_else(arithmetic_overflow)?
                > height
        {
            return Err(invalid_decode());
        }
        let mut y = 0_u32;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant y <= block_height,
                decreases block_height - y,
            )
        )]
        while y < block_height {
            let mut x = 0_u32;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant x <= block_width,
                    decreases block_width - x,
                )
            )]
            while x < block_width {
                let destination = checked_index(
                    width,
                    placed.x.checked_add(x).ok_or_else(arithmetic_overflow)?,
                    placed.y.checked_add(y).ok_or_else(arithmetic_overflow)?,
                )?;
                let source = checked_index(block_width, x, y)?;
                if destination >= samples.len()
                    || destination >= visited.len()
                    || source >= block.samples().len()
                    || visited[destination]
                {
                    return Err(invalid_decode());
                }
                let sample = block.samples().get(source).ok_or_else(invalid_decode)?;
                samples[destination] = *sample;
                visited[destination] = true;
                x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            y = y.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        block_index = block_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let mut sample_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant sample_index <= visited.len(),
            decreases visited.len() - sample_index,
        )
    )]
    while sample_index < visited.len() {
        if !visited[sample_index] {
            return Err(invalid_decode());
        }
        sample_index = sample_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    Ok(DecodedSubband {
        width,
        height,
        fraction_bits: fraction_bits.ok_or_else(invalid_decode)?,
        samples,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_image_outcome(result) == crate::specs::part1_decode_prepared_image(
        crate::image::assembly_size_view(size), crate::image::assembly_tiles_view(tile_components@),
        component_transform, crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub fn decode_prepared_image(
    size: &ImageSize,
    tile_components: &[TileComponent<'_>],
    component_transform: ComponentTransform,
    limits: &ResourceLimits,
) -> Result<DecodedImage, DecodeError> {
    let mut image = assemble_image(size, tile_components, limits)?;
    match component_transform {
        ComponentTransform::None => {}
        ComponentTransform::Reversible => {
            apply_reversible_component_transform(&mut image)?;
        }
        ComponentTransform::Irreversible => {
            apply_irreversible_component_transform(&mut image)?;
        }
    }
    Ok(image)
}

impl DecodedCodeBlock {
    pub const fn height(&self) -> u16 {
        self.height
    }

    pub const fn fraction_bits(&self) -> u8 {
        self.fraction_bits
    }

    pub fn samples(&self) -> &[i64] {
        &self.samples
    }
}

pub fn decode_code_block(
    request: CodeBlockDecodeRequest<'_>,
    limits: &ResourceLimits,
) -> Result<DecodedCodeBlock, DecodeError> {
    if request.layers.is_empty() {
        return Err(invalid_decode());
    }
    let mut decoder = Tier1CodeBlockDecoder::new(
        request.width,
        request.height,
        request.significant_bitplanes,
        request.orientation,
        request.style,
    )?;
    let mut layer_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant layer_index <= request.layers.len(),
            decreases request.layers.len() - layer_index,
        )
    )]
    while layer_index < request.layers.len() {
        let layer = request.layers[layer_index];
        decode_code_block_contribution_body(&mut decoder, layer.contribution, layer.body, limits)?;
        layer_index = layer_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    if !decoder.is_complete() {
        return Err(invalid_decode());
    }
    let coefficients = decoder.plane().coefficients();
    let expected = usize::from(request.width)
        .checked_mul(usize::from(request.height))
        .ok_or_else(arithmetic_overflow)?;
    if coefficients.len() != expected {
        return Err(invalid_decode());
    }
    let signed = collect_code_block_coefficients(decoder.plane())?;
    let quantized = inverse_quantize_magnitudes(
        &signed,
        request.quantization_step,
        request.dynamic_range,
        request.reversible,
        request.roi_shift,
        limits,
    )?;
    let quantized_count = quantized.samples().len();
    let mut samples = Vec::with_capacity(quantized_count);
    let mut sample_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant sample_index <= quantized_count,
            decreases quantized_count - sample_index,
        )
    )]
    while sample_index < quantized_count {
        let sample = quantized
            .samples()
            .get(sample_index)
            .ok_or_else(invalid_decode)?;
        samples.push(*sample);
        sample_index = sample_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    Ok(DecodedCodeBlock {
        width: request.width,
        height: request.height,
        fraction_bits: quantized.fraction_bits(),
        samples,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_extraction_result(crate::tier1::code_block_plane_view(plane),false,crate::transform::quantized_coefficients_outcome(result)),
        crate::transform::quantized_coefficients_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
            crate::transform::quantized_coefficients_outcome(result)==crate::specs::part2_extraction_value(crate::tier1::code_block_plane_view(plane),false),
))]
pub(super) fn collect_code_block_coefficients(
    plane: &crate::tier1::CodeBlockPlane,
) -> Result<Vec<crate::transform::SignedMagnitude>, DecodeError> {
    let coefficients = plane.coefficients();
    let count = coefficients.len();
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost source=crate::tier1::code_block_plane_view(plane);}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_extraction_normal(source,false);}
    let allocated = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let unit=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_extraction_capacity_observed(crate::specs::part2_extraction_context(source,false),unit);
        if let Err(error)=allocated{crate::specs::part2_extraction_refused(source,false,error);}
    }
    let mut signed = allocated?;
    let mut coefficient_index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part2_linear_coefficients_prefix,1);
        crate::transform::representation_proofs::quantized_coefficients_fields(signed@);
        assert(crate::transform::quantized_coefficients_view(signed@) =~= Seq::empty());
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant coefficient_index<=coefficients.len(), signed.len()==coefficient_index,
            crate::tier1::coefficient_raw_views(coefficients@)==source.coefficients,
            source==crate::tier1::code_block_plane_view(plane),
            crate::specs::part2_linear_coefficients_prefix(source.coefficients,coefficient_index as nat)==Ok(crate::transform::quantized_coefficients_view(signed@)),
            crate::specs::part2_extraction_result(source,false,crate::specs::part2_extraction_value(source,false)),
        decreases coefficients.len()-coefficient_index,
    ))]
    while coefficient_index < coefficients.len() {
        #[cfg(verus_keep_ghost)]
        proof! {reveal_with_fuel(crate::specs::part2_linear_coefficients_prefix,1);}
        let coefficient = coefficients[coefficient_index];
        #[cfg(verus_keep_ghost)]
        proof! {assert(crate::tier1::coefficient_raw_view(coefficient)==source.coefficients[coefficient_index as int]);}
        let value = match coefficient.signed_magnitude() {
            Ok(value) => value,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {crate::specs::part2_linear_coefficients_error(source.coefficients,coefficient_index as nat+1,coefficients.len() as nat,error);}
                return Err(error);
            }
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost prior_values=signed@;let ghost prior_index=coefficient_index;}
        signed.push(value);
        coefficient_index = coefficient_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::transform::representation_proofs::quantized_coefficients_push(prior_values,value);
            reveal_with_fuel(crate::specs::part2_linear_coefficients_prefix,1);
            assert(crate::specs::part2_linear_coefficients_prefix(source.coefficients,coefficient_index as nat)==Ok(crate::transform::quantized_coefficients_view(signed@)));
        }
    }
    Ok(signed)
}
