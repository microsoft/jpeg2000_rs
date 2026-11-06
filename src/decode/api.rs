use super::{
    CodestreamLayout, DecodeError, DecodeOptions, DecodeSelection, DecodedImage, MalformedKind,
    NonlinearComponentExtent, NonlinearRegion, ResourceLimits, TypedImage, TypedSamples,
    apply_jp2_output, arithmetic_overflow, codestream, color_selection, convert_associated_color,
    convert_associated_selected_color, decode_jpx_file, decode_jpx_file_selected, decode_layout,
    decode_layout_selected, finish_associated_selected_output, invalid_decode, jp2,
    registered_ceil_div_u32,
};
#[cfg(verus_keep_ghost)]
use super::{ImageSize, nonlinear_regions_outcome, nonlinear_regions_view};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_typed_image_outcome(result) == crate::specs::part2_decode_raw_codestream(
        input@, crate::options::decode_options_limits(options), None),
))]
pub fn decode_codestream(input: &[u8], options: &DecodeOptions) -> Result<TypedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_errors_known();
        crate::specs::part2_decode_raw_codestream_unfold(input@, crate::options::decode_options_limits(options), None);
        reveal(crate::specs::part2_decode_typed_layout);
    }
    let layout = codestream::parse_layout(input, options.limits())?;
    #[cfg(verus_keep_ghost)]
    proof! { codestream::decoder_layout_input_matches_raw(&layout); }
    decode_typed_layout(input.len(), &layout, options.limits(), None)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_typed_image_outcome(result) == crate::specs::part2_decode_raw_codestream(
        input@, crate::options::decode_options_limits(options), Some(selection)),
))]
pub fn decode_codestream_selected(
    input: &[u8],
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<TypedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_errors_known();
        crate::specs::part2_decode_raw_codestream_unfold(
            input@, crate::options::decode_options_limits(options), Some(selection));
        reveal(crate::specs::part2_decode_typed_layout);
    }
    let layout = codestream::parse_layout(input, options.limits())?;
    #[cfg(verus_keep_ghost)]
    proof! { codestream::decoder_layout_input_matches_raw(&layout); }
    decode_typed_layout(input.len(), &layout, options.limits(), Some(selection))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_typed_image_outcome(result) == crate::specs::part2_decode_typed_layout(
        input_bytes, layout, limits, requested,
    ),
))]
pub(super) fn decode_typed_layout(
    input_bytes: usize,
    layout: &CodestreamLayout<'_>,
    limits: &ResourceLimits,
    requested: Option<&DecodeSelection>,
) -> Result<TypedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_decode_typed_layout);
        reveal(crate::specs::part2_typed_layout);
        codestream::decoder_layout_input_fields(layout);
    }
    let decoded = match requested {
        None => decode_layout(layout, limits)?,
        Some(requested) => decode_layout_selected(layout, requested, limits)?,
    };
    let image = typed_layout(layout, decoded, limits)?;
    validate_part1_output_shape(input_bytes, layout, &image)?;
    Ok(image)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_validate_typed_output_shape(
        input_bytes, layout.tile_parts.len(), layout.info.image_size.components,
        crate::image::typed_image_value_view(*image),
    ),
))]
pub(super) fn validate_part1_output_shape(
    input_bytes: usize,
    layout: &CodestreamLayout<'_>,
    image: &TypedImage,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost components = crate::image::typed_image_component_views(image);
        let ghost goal = crate::specs::part1_validate_typed_output_shape(
            input_bytes, layout.tile_parts.len(), layout.info.image_size.components,
            crate::image::typed_image_value_view(*image),
        );
    }
    if !crate::refinement::decode_output_shape_valid(
        input_bytes,
        layout.tile_parts.len(),
        layout.info.image_size.components,
        image.components().len(),
        image.width(),
        image.height(),
    ) {
        return Err(invalid_decode());
    }
    let component_count = image.components().len();
    let mut component = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component <= component_count,
            component_count == components.len(),
            components == crate::image::typed_image_component_views(image),
            goal == crate::specs::part1_validate_typed_output_shape(
                input_bytes, layout.tile_parts.len(), layout.info.image_size.components,
                crate::image::typed_image_value_view(*image),
            ),
            goal == crate::specs::part1_validate_typed_output_components(components, component as nat),
            decreases component_count - component,
        )
    )]
    while component < component_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_validate_typed_output_components, 1);
        }
        let output = image
            .components()
            .get(component)
            .ok_or_else(invalid_decode)?;
        let samples = match output.samples() {
            TypedSamples::Signed(samples) => samples.len(),
            TypedSamples::Unsigned(samples) => samples.len(),
        };
        if !crate::refinement::component_output_shape_valid(
            output.width(),
            output.height(),
            samples,
        ) {
            return Err(invalid_decode());
        }
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part1_validate_typed_output_components, 1);
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_typed_image_outcome(result) == crate::specs::part2_typed_layout(
        layout, crate::image::decoded_image_view(decoded), limits,
    ),
))]
pub(super) fn typed_layout(
    layout: &CodestreamLayout<'_>,
    decoded: DecodedImage,
    limits: &ResourceLimits,
) -> Result<TypedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_typed_layout);
        codestream::decoder_layout_input_fields(layout);
    }
    let mut image = decoded.typed(limits)?;
    let regions = collect_nonlinear_regions(layout, &image)?;
    if !regions.is_empty() {
        image.apply_nonlinear_regions(&regions, limits)?;
    }
    Ok(image)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nonlinear_component_extent(
        size, crate::image::typed_image_value_view(*image), component,
    ),
))]
pub(super) fn nonlinear_component_extent(
    size: &codestream::ImageSize,
    image: &TypedImage,
    component: u16,
) -> Result<NonlinearComponentExtent, DecodeError> {
    let info = size.component(component)?;
    let output = image.component(component)?;
    let x0 = registered_ceil_div_u32(
        image.x_origin(),
        u32::from(info.x_subsampling),
        info.x_registration,
    )?;
    let y0 = registered_ceil_div_u32(
        image.y_origin(),
        u32::from(info.y_subsampling),
        info.y_registration,
    )?;
    let x1 = x0
        .checked_add(output.width())
        .ok_or_else(arithmetic_overflow)?;
    let y1 = y0
        .checked_add(output.height())
        .ok_or_else(arithmetic_overflow)?;
    let count = size.tile_count()?;
    Ok(((x0, y0, x1, y1), count))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures nonlinear_regions_outcome(result) == crate::specs::part2_collect_nonlinear_regions(
        layout, crate::image::typed_image_value_view(*image),
    ),
))]
pub(super) fn collect_nonlinear_regions<'a>(
    layout: &'a CodestreamLayout<'_>,
    image: &TypedImage,
) -> Result<Vec<NonlinearRegion<'a>>, DecodeError> {
    let mut regions = Vec::new();
    let mut component = 0_u16;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost image_view = crate::image::typed_image_value_view(*image);
        let ghost goal = crate::specs::part2_collect_nonlinear_regions(layout, image_view);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_input_fields(layout);
        assert(nonlinear_regions_view(regions@) =~= Seq::empty());
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component <= layout.info.image_size.components,
            image_view == crate::image::typed_image_value_view(*image),
            goal == crate::specs::part2_collect_nonlinear_regions(layout, image_view),
            goal == crate::specs::part2_nonlinear_component_regions(layout, image_view, component as nat, nonlinear_regions_view(regions@)),
            decreases layout.info.image_size.components - component,
        )
    )]
    while component < layout.info.image_size.components {
        #[cfg(verus_keep_ghost)]
        proof! {
            codestream::decoder_layout_input_fields(layout);
            reveal_with_fuel(crate::specs::part2_nonlinear_component_regions, 1);
        }
        let (extent, tile_count) =
            nonlinear_component_extent(&layout.info.image_size, image, component)?;
        let (output_x0, output_y0, output_x1, output_y1) = extent;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost tile_goal = crate::specs::part2_nonlinear_tile_regions(
                layout, component, extent, tile_count, 0, nonlinear_regions_view(regions@),
            );
        }
        let mut tile = 0_u64;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile <= tile_count,
                image_view == crate::image::typed_image_value_view(*image),
                component < layout.info.image_size.components,
                goal == crate::specs::part2_collect_nonlinear_regions(layout, image_view),
                goal == match tile_goal {
                    Err(error) => Err(error),
                    Ok(regions) => crate::specs::part2_nonlinear_component_regions(layout, image_view, component as nat + 1, regions),
                },
                tile_goal == crate::specs::part2_nonlinear_tile_regions(layout, component, extent, tile_count, tile as nat, nonlinear_regions_view(regions@)),
                extent == (output_x0, output_y0, output_x1, output_y1),
                decreases tile_count - tile,
            )
        )]
        while tile < tile_count {
            #[cfg(verus_keep_ghost)]
            proof! {
                codestream::decoder_layout_input_fields(layout);
                reveal_with_fuel(crate::specs::part2_nonlinear_tile_regions, 1);
            }
            let tile_index = match u16::try_from(tile) {
                Ok(index) => index,
                Err(_) => return Err(arithmetic_overflow()),
            };
            let mut extensions = &layout.info.part2_extensions;
            let mut part = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant part <= layout.tile_parts.len(),
                    codestream::owned_extensions_view(extensions) == crate::specs::part2_nonlinear_tile_extensions(
                        codestream::owned_extensions_view(&layout.info.part2_extensions),
                        codestream::tile_parts_owned_view(layout.tile_parts@), tile_index, part as nat,
                    ),
                    decreases layout.tile_parts.len() - part,
                )
            )]
            while part < layout.tile_parts.len() {
                let tile_part = layout.tile_parts.get(part).ok_or_else(invalid_decode)?;
                if tile_part.tile_index == tile_index {
                    extensions = &tile_part.part2_extensions;
                }
                part = part.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost before = regions@;
                let ghost region = crate::specs::part2_nonlinear_tile_region(layout, component, tile_index, extent);
            }
            if let Some(transform) = extensions.nonlinear_transform_for(component) {
                let bounds = layout
                    .info
                    .image_size
                    .tile_component_bounds(tile_index, component)?;
                let x0 = bounds.x0.max(output_x0);
                let y0 = bounds.y0.max(output_y0);
                let x1 = bounds.x1.min(output_x1);
                let y1 = bounds.y1.min(output_y1);
                if x0 < x1 && y0 < y1 {
                    regions.push(NonlinearRegion {
                        component,
                        x0: x0.checked_sub(output_x0).ok_or_else(arithmetic_overflow)?,
                        y0: y0.checked_sub(output_y0).ok_or_else(arithmetic_overflow)?,
                        x1: x1.checked_sub(output_x0).ok_or_else(arithmetic_overflow)?,
                        y1: y1.checked_sub(output_y0).ok_or_else(arithmetic_overflow)?,
                        transform,
                    });
                }
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(nonlinear_regions_view(regions@) =~= match region {
                    Err(_) => nonlinear_regions_view(before),
                    Ok(None) => nonlinear_regions_view(before),
                    Ok(Some(region)) => nonlinear_regions_view(before).push(region),
                });
            }
            tile = tile.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            codestream::decoder_layout_input_fields(layout);
            reveal_with_fuel(crate::specs::part2_nonlinear_tile_regions, 1);
        }
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_input_fields(layout);
        reveal_with_fuel(crate::specs::part2_nonlinear_component_regions, 1);
    }
    Ok(regions)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_typed_image_outcome(result) == crate::specs::part2_decode_raw_single_container(
        input@, crate::options::decode_options_limits(options), None, false),
))]
pub fn decode_jp2(input: &[u8], options: &DecodeOptions) -> Result<TypedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_raw_single_container_unfold(input@, crate::options::decode_options_limits(options), None, false);
    }
    let inspected = jp2::parse_and_inspect(input, options.limits())?;
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected)); }
    if !inspected
        .file()
        .file_type()
        .is_compatible_with(jp2::BoxType::JP2_BRAND)
    {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    if inspected.file().codestream_count() != 1 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    let decoded = decode_codestream(inspected.file().codestream(0)?.data(), options)?;
    apply_jp2_output(decoded, inspected.file().header(), options.limits())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_typed_image_outcome(result) == crate::specs::part2_decode_raw_single_container(
        input@, crate::options::decode_options_limits(options), Some(selection), false),
))]
pub fn decode_jp2_selected(
    input: &[u8],
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<TypedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_raw_single_container_unfold(input@, crate::options::decode_options_limits(options), Some(selection), false);
    }
    let inspected = jp2::parse_and_inspect(input, options.limits())?;
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected)); }
    if !inspected
        .file()
        .file_type()
        .is_compatible_with(jp2::BoxType::JP2_BRAND)
        || inspected.file().codestream_count() != 1
    {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    let decoded =
        decode_codestream_selected(inspected.file().codestream(0)?.data(), options, selection)?;
    apply_jp2_output(decoded, inspected.file().header(), options.limits())
}

pub fn decode_jp2_color(
    input: &[u8],
    options: &DecodeOptions,
) -> Result<crate::color::ConvertedImage, DecodeError> {
    let inspected = jp2::parse_and_inspect(input, options.limits())?;
    if !inspected
        .file()
        .file_type()
        .is_compatible_with(jp2::BoxType::JP2_BRAND)
    {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    if inspected.file().codestream_count() != 1 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    let decoded = decode_codestream(inspected.file().codestream(0)?.data(), options)?;
    let mapped = apply_jp2_output(decoded, inspected.file().header(), options.limits())?;
    crate::color::convert_jp2_color(&mapped, &inspected.file().header().color, options.limits())
}

pub fn decode_jp2_color_selected(
    input: &[u8],
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<crate::color::ConvertedImage, DecodeError> {
    let inspected = jp2::parse_and_inspect(input, options.limits())?;
    if !inspected
        .file()
        .file_type()
        .is_compatible_with(jp2::BoxType::JP2_BRAND)
        || inspected.file().codestream_count() != 1
    {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    let codestream = inspected.file().codestream(0)?.data();
    let (expanded, target) = color_selection(codestream, selection, options.limits())?;
    let decoded = decode_codestream_selected(codestream, options, &expanded)?;
    finish_associated_selected_output(
        decoded,
        Some(inspected.file().header()),
        target,
        options.limits(),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_typed_image_outcome(result) == crate::specs::part2_decode_raw_single_container(
        input@, crate::options::decode_options_limits(options), None, true),
))]
pub fn decode_jph(input: &[u8], options: &DecodeOptions) -> Result<TypedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_raw_single_container_unfold(input@, crate::options::decode_options_limits(options), None, true);
    }
    let inspected = jp2::inspect_jph(input, options.limits())?;
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected)); }
    if inspected.file().codestream_count() != 1 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    let decoded = decode_codestream(inspected.file().codestream(0)?.data(), options)?;
    apply_jp2_output(decoded, inspected.file().header(), options.limits())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_typed_image_outcome(result) == crate::specs::part2_decode_raw_single_container(
        input@, crate::options::decode_options_limits(options), Some(selection), true),
))]
pub fn decode_jph_selected(
    input: &[u8],
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<TypedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_raw_single_container_unfold(input@, crate::options::decode_options_limits(options), Some(selection), true);
    }
    let inspected = jp2::inspect_jph(input, options.limits())?;
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected)); }
    if inspected.file().codestream_count() != 1 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    let decoded =
        decode_codestream_selected(inspected.file().codestream(0)?.data(), options, selection)?;
    apply_jp2_output(decoded, inspected.file().header(), options.limits())
}

pub fn decode_jph_color(
    input: &[u8],
    options: &DecodeOptions,
) -> Result<crate::color::ConvertedImage, DecodeError> {
    let inspected = jp2::inspect_jph(input, options.limits())?;
    if inspected.file().codestream_count() != 1 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    let decoded = decode_codestream(inspected.file().codestream(0)?.data(), options)?;
    let mapped = apply_jp2_output(decoded, inspected.file().header(), options.limits())?;
    crate::color::convert_jp2_color(&mapped, &inspected.file().header().color, options.limits())
}

pub fn decode_jph_color_selected(
    input: &[u8],
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<crate::color::ConvertedImage, DecodeError> {
    let inspected = jp2::inspect_jph(input, options.limits())?;
    if inspected.file().codestream_count() != 1 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    let codestream = inspected.file().codestream(0)?.data();
    let (expanded, target) = color_selection(codestream, selection, options.limits())?;
    let decoded = decode_codestream_selected(codestream, options, &expanded)?;
    finish_associated_selected_output(
        decoded,
        Some(inspected.file().header()),
        target,
        options.limits(),
    )
}

pub fn decode_jpx_codestream(
    input: &[u8],
    codestream_index: usize,
    options: &DecodeOptions,
) -> Result<TypedImage, DecodeError> {
    let file = jp2::parse(input, options.limits())?;
    let (decoded, _) = decode_jpx_file(&file, codestream_index, options)?;
    Ok(decoded)
}

pub fn decode_jpx_codestream_selected(
    input: &[u8],
    codestream_index: usize,
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<TypedImage, DecodeError> {
    let file = jp2::parse(input, options.limits())?;
    let (decoded, _) = decode_jpx_file_selected(&file, codestream_index, options, selection)?;
    Ok(decoded)
}

pub fn decode_jpx_codestream_color(
    input: &[u8],
    codestream_index: usize,
    options: &DecodeOptions,
) -> Result<crate::color::ConvertedImage, DecodeError> {
    let file = jp2::parse(input, options.limits())?;
    let (decoded, header) = decode_jpx_file(&file, codestream_index, options)?;
    convert_associated_color(&decoded, header, options.limits())
}

pub fn decode_jpx_codestream_color_selected(
    input: &[u8],
    codestream_index: usize,
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<crate::color::ConvertedImage, DecodeError> {
    let file = jp2::parse(input, options.limits())?;
    if !file.file_type().is_jpx_compatible() {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    let (expanded, target) = color_selection(
        file.codestream(codestream_index)?.data(),
        selection,
        options.limits(),
    )?;
    let (decoded, header) = decode_jpx_file_selected(&file, codestream_index, options, &expanded)?;
    convert_associated_selected_color(&decoded, header, target, options.limits())
}
