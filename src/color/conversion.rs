use super::admission::{channel_layout, validate_components, validate_output_size};
use super::geometry::{
    arithmetic_overflow, checked_area, invalid_color_input, registered_ceil_div,
    registered_floor_div, unsupported,
};
use super::normalization::{
    chroma_at_index, nominal_at_index, normalize_component, normalize_unsigned, normalized_at,
    normalized_difference_at, pixel_coordinates,
};
use super::{
    ConvertedChannel, ConvertedChannelType, ConvertedColorSpace, ConvertedImage, FIXED_ONE,
};
#[cfg(verus_keep_ghost)]
use super::{
    converted_channel_result, converted_channel_views, converted_channel_views_push,
    converted_image_result,
};
use crate::image::{ChannelAssociation, TypedComponent, TypedImage};
#[cfg(verus_keep_ghost)]
use crate::image::{typed_component_view, typed_image_component_views, typed_image_geometry};
use crate::jp2::{
    ColorMethod, ColorSpecification, ENUMERATED_GRAYSCALE, ENUMERATED_SRGB, ENUMERATED_SYCC,
};
use crate::{DecodeError, ResourceLimits, UnsupportedColorConversion};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::specs::part2_color_convert_storage_result(crate::specs::Part2ColorConvertContext {
            image:crate::image::typed_image_value_view(*image),method:crate::jp2::color_specification_method(color),
            bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits),
        },converted_image_result(result)),
        result!=Err(DecodeError::AllocationFailed) ==> converted_image_result(result) == crate::specs::color_convert_jp2(
            crate::image::typed_image_component_views(image),
            crate::image::typed_image_definition_views(image),
            crate::image::typed_image_geometry(image), crate::jp2::color_specification_method(color),
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
        ),
    )
)]
pub fn convert_jp2_color(
    image: &TypedImage,
    color: &ColorSpecification,
    limits: &ResourceLimits,
) -> Result<ConvertedImage, DecodeError> {
    if matches!(color.method(), ColorMethod::Enumerated { color_space: 20 }) {
        return super::esrgb_image::convert_esrgb_color(image, limits);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost input = crate::image::typed_image_component_views(image);
        let ghost geometry = crate::image::typed_image_geometry(image);
        let ghost storage_context=crate::specs::Part2ColorConvertContext {
            image:crate::image::typed_image_value_view(*image),method:crate::jp2::color_specification_method(color),
            bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits)};
    }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_color_convert_storage_normal(storage_context);}
    if image.width() == 0 || image.height() == 0 {
        return Err(invalid_color_input());
    }
    let (color_count, output_space, sycc) = match color.method() {
        ColorMethod::Unspecified => {
            return Err(unsupported(
                UnsupportedColorConversion::UnspecifiedColorSpace,
            ));
        }
        ColorMethod::Enumerated {
            color_space: ENUMERATED_SRGB,
        } => (3_usize, ConvertedColorSpace::Srgb, false),
        ColorMethod::Enumerated {
            color_space: ENUMERATED_GRAYSCALE,
        } => (1_usize, ConvertedColorSpace::Grayscale, false),
        ColorMethod::Enumerated {
            color_space: ENUMERATED_SYCC,
        } => (3_usize, ConvertedColorSpace::Srgb, true),
        ColorMethod::Enumerated { .. } => {
            return Err(unsupported(
                UnsupportedColorConversion::EnumeratedColorSpace,
            ));
        }
        ColorMethod::RestrictedIcc { .. } | ColorMethod::AnyIcc { .. } => {
            return Err(unsupported(UnsupportedColorConversion::IccProfile));
        }
    };
    let organized = channel_layout(image, color_count);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=organized {
            crate::specs::part2_color_convert_layout_error(storage_context,(color_count,output_space,sycc),error);
        }
    }
    let layout = organized?;
    validate_components(image, &layout)?;
    validate_output_size(image, color_count, layout.alphas.len(), limits)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost colors = layout.colors@; }

    let pixel_count = checked_area(image.width(), image.height())?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::proofs::internal_specs::color_conversion_ready(
            input, crate::image::typed_image_definition_views(image), geometry,
            crate::jp2::color_specification_method(color), (layout.colors@, layout.alphas@),
            (color_count, output_space, sycc), pixel_count,
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
        ));
    }
    let channel_count = color_count
        .checked_add(layout.alphas.len())
        .ok_or_else(arithmetic_overflow)?;
    let allocated = if channel_count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(channel_count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_color_convert_preflight(storage_context)==Ok(((color_count,output_space,sycc),(layout.colors@,layout.alphas@),pixel_count)));
        let request=crate::specs::Part2ColorOutputCapacity::Channels {context:storage_context};
        crate::specs::part2_color_output_capacity_observed(request,crate::allocation::inspection_capacity_outcome(allocated));
        if let Err(error)=allocated {
            crate::specs::part2_color_convert_owner_present(storage_context);
            crate::specs::part2_color_convert_storage_refused(storage_context,request,error);
        }
    }
    let mut channels = allocated?;
    if sycc {
        let width = usize::try_from(image.width()).map_err(|_| arithmetic_overflow())?;
        if width == 0 {
            return Err(invalid_color_input());
        }
        let allocated = if pixel_count == 0 {
            Ok(Vec::new())
        } else {
            crate::allocation::empty_with_capacity(pixel_count)
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let request=crate::specs::Part2ColorOutputCapacity::Sycc {context:storage_context,role:0};
            crate::specs::part2_color_output_capacity_observed(request,crate::allocation::inspection_capacity_outcome(allocated));
            if let Err(error)=allocated {crate::specs::part2_color_convert_sycc_present(storage_context,0);
                crate::specs::part2_color_convert_storage_refused(storage_context,request,error);}
        }
        let mut red = allocated?;
        let allocated = if pixel_count == 0 {
            Ok(Vec::new())
        } else {
            crate::allocation::empty_with_capacity(pixel_count)
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let request=crate::specs::Part2ColorOutputCapacity::Sycc {context:storage_context,role:1};
            crate::specs::part2_color_output_capacity_observed(request,crate::allocation::inspection_capacity_outcome(allocated));
            if let Err(error)=allocated {crate::specs::part2_color_convert_sycc_present(storage_context,1);
                crate::specs::part2_color_convert_storage_refused(storage_context,request,error);}
        }
        let mut green = allocated?;
        let allocated = if pixel_count == 0 {
            Ok(Vec::new())
        } else {
            crate::allocation::empty_with_capacity(pixel_count)
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let request=crate::specs::Part2ColorOutputCapacity::Sycc {context:storage_context,role:2};
            crate::specs::part2_color_output_capacity_observed(request,crate::allocation::inspection_capacity_outcome(allocated));
            if let Err(error)=allocated {crate::specs::part2_color_convert_sycc_present(storage_context,2);
                crate::specs::part2_color_convert_storage_refused(storage_context,request,error);}
        }
        let mut blue = allocated?;
        let plan = plan_sycc_rows(image, &layout.colors);
        let mut row = SyccRow {
            base: None,
            chroma: None,
        };
        let mut pixel = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_color_sycc_empty(input, geometry, colors, width);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant pixel <= pixel_count,
                    !crate::specs::color_is_esrgb(crate::jp2::color_specification_method(color)),
                    storage_context==(crate::specs::Part2ColorConvertContext {
                        image:(geometry,input,crate::image::typed_image_definition_views(image)),method:crate::jp2::color_specification_method(color),
                        bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits)}),
                    crate::specs::part2_color_convert_storage_result(storage_context,crate::specs::part2_color_convert_value(storage_context)),
                    sycc,
                    input == crate::image::typed_image_component_views(image),
                    geometry == crate::image::typed_image_geometry(image),
                    colors == layout.colors@,
                    width as nat == geometry.0 as nat,
                    width > 0,
                    match plan {
                        Some(ref plan) => sycc_plan_matches(plan, input, colors, geometry)
                            && sycc_row_valid(plan, row),
                        None => true,
                    },
                    crate::specs::part2_layer_area(geometry.0, geometry.1) == Ok(pixel_count),
                    crate::specs::color_sycc_planes_prefix(input, geometry, colors, width, pixel as nat)
                        == Ok((red@, green@, blue@)),
                    crate::proofs::internal_specs::color_conversion_ready(
                        input, crate::image::typed_image_definition_views(image), geometry,
                        crate::jp2::color_specification_method(color), (layout.colors@, layout.alphas@),
                        (color_count, output_space, sycc), pixel_count,
                        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
                    ),
                decreases pixel_count - pixel,
            )
        )]
        while pixel < pixel_count {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_color_sycc_step(input, geometry, colors, width, pixel as nat);
            }
            let converted = match &plan {
                Some(plan) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(crate::specs::part2_layer_area);
                        assert(geometry == sycc_geometry(plan));
                        sycc_pixel_routing(plan, input, colors, geometry, pixel, width);
                    }
                    convert_sycc_row_pixel(plan, &mut row, pixel, width)
                }
                None => convert_sycc_pixel(image, &layout.colors, pixel, width),
            };
            let (r, g, b) = match converted {
                Ok(value) => value,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_color_sycc_error(
                            input, geometry, colors, width, pixel as nat + 1, pixel_count as nat, error,
                        );
                    }
                    return Err(error);
                }
            };
            red.push(r);
            green.push(g);
            blue.push(b);
            pixel = pixel.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost sycc_planes = (red@, green@, blue@); }
        channels.push(ConvertedChannel {
            channel_type: ConvertedChannelType::Red,
            samples: red,
        });
        channels.push(ConvertedChannel {
            channel_type: ConvertedChannelType::Green,
            samples: green,
        });
        channels.push(ConvertedChannel {
            channel_type: ConvertedChannelType::Blue,
            samples: blue,
        });
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(converted_channel_views(channels@) =~= seq![
                (ConvertedChannelType::Red, sycc_planes.0),
                (ConvertedChannelType::Green, sycc_planes.1),
                (ConvertedChannelType::Blue, sycc_planes.2),
            ]);
        }
    } else {
        let mut color_index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_color_channels_empty(input, geometry, colors, color_count);
            assert(converted_channel_views(channels@) =~= Seq::<crate::specs::ColorChannelModel>::empty());
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant color_index <= color_count,
                    !crate::specs::color_is_esrgb(crate::jp2::color_specification_method(color)),
                    storage_context==(crate::specs::Part2ColorConvertContext {
                        image:(geometry,input,crate::image::typed_image_definition_views(image)),method:crate::jp2::color_specification_method(color),
                        bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits)}),
                    crate::specs::part2_color_convert_storage_result(storage_context,crate::specs::part2_color_convert_value(storage_context)),
                    !sycc,
                    input == crate::image::typed_image_component_views(image),
                    geometry == crate::image::typed_image_geometry(image),
                    colors == layout.colors@,
                    crate::specs::color_convert_channels_prefix(input, geometry, colors, color_count, color_index as nat)
                        == Ok(converted_channel_views(channels@)),
                    crate::proofs::internal_specs::color_conversion_ready(
                        input, crate::image::typed_image_definition_views(image), geometry,
                        crate::jp2::color_specification_method(color), (layout.colors@, layout.alphas@),
                        (color_count, output_space, sycc), pixel_count,
                        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
                    ),
                decreases color_count - color_index,
            )
        )]
        while color_index < color_count {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_color_channels_step(
                    input, geometry, colors, color_count, color_index as nat,
                );
            }
            let channel = match convert_color_channel(
                image,
                &layout.colors,
                color_count,
                color_index,
            ) {
                Ok(channel) => channel,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        if crate::specs::color_convert_channel(input,geometry,colors,color_count,color_index)==Err(error) {
                            crate::proofs::production_impl::production_color_channels_error(
                                input, geometry, colors, color_count, color_index as nat + 1, color_count as nat, error,
                            );
                        }
                        crate::specs::part2_color_convert_channel_error(storage_context,(color_count,output_space,sycc),
                            (layout.colors@,layout.alphas@),pixel_count,color_index,error);
                    }
                    return Err(error);
                }
            };
            #[cfg(verus_keep_ghost)]
            proof! { converted_channel_views_push(channels@, channel); }
            channels.push(channel);
            color_index = color_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
    }

    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = converted_channel_views(channels@);
        let ghost alphas = layout.alphas@;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::color_convert_colors(input, geometry, colors, color_count, sycc) == Ok(initial));
        crate::proofs::production_impl::production_color_alphas_empty(input, geometry, alphas, initial);
    }
    let mut alpha_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant alpha_index <= layout.alphas.len(),
                !crate::specs::color_is_esrgb(crate::jp2::color_specification_method(color)),
                storage_context==(crate::specs::Part2ColorConvertContext {
                    image:(geometry,input,crate::image::typed_image_definition_views(image)),method:crate::jp2::color_specification_method(color),
                    bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits)}),
                crate::specs::part2_color_convert_storage_result(storage_context,crate::specs::part2_color_convert_value(storage_context)),
                input == crate::image::typed_image_component_views(image),
                geometry == crate::image::typed_image_geometry(image),
                colors == layout.colors@,
                alphas == layout.alphas@,
                crate::specs::color_convert_colors(input, geometry, colors, color_count, sycc) == Ok(initial),
                crate::specs::color_append_alphas_prefix(input, geometry, alphas, initial, alpha_index as nat)
                    == Ok(converted_channel_views(channels@)),
                crate::proofs::internal_specs::color_conversion_ready(
                    input, crate::image::typed_image_definition_views(image), geometry,
                    crate::jp2::color_specification_method(color), (layout.colors@, layout.alphas@),
                    (color_count, output_space, sycc), pixel_count,
                    crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
                ),
            decreases layout.alphas.len() - alpha_index,
        )
    )]
    while alpha_index < layout.alphas.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_color_alphas_step(input, geometry, alphas, initial, alpha_index as nat);
        }
        let alpha = *layout
            .alphas
            .get(alpha_index)
            .ok_or_else(invalid_color_input)?;
        let channel = match convert_alpha_channel(image, alpha) {
            Ok(channel) => channel,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    if crate::specs::color_convert_alpha(input,geometry,alpha)==Err(error) {
                        crate::proofs::production_impl::production_color_alphas_error(
                            input, geometry, alphas, initial, alpha_index as nat + 1, alphas.len(), error,
                        );
                    }
                    crate::specs::part2_color_convert_alpha_error(storage_context,(color_count,output_space,sycc),
                        (layout.colors@,layout.alphas@),pixel_count,initial,alpha_index as nat,error);
                }
                return Err(error);
            }
        };
        #[cfg(verus_keep_ghost)]
        proof! { converted_channel_views_push(channels@, channel); }
        channels.push(channel);
        alpha_index = alpha_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }

    Ok(ConvertedImage {
        width: image.width(),
        height: image.height(),
        color_space: output_space,
        precision: 16,
        channels,
    })
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::specs::part2_color_channel_storage_result(crate::image::typed_image_component_views(image),
            crate::image::typed_image_geometry(image),colors@,color_count,index,converted_channel_result(result)),
        result!=Err(DecodeError::AllocationFailed) ==> converted_channel_result(result) == crate::specs::color_convert_channel(
            crate::image::typed_image_component_views(image), crate::image::typed_image_geometry(image),
            colors@, color_count, index,
        ),
    )
)]
fn convert_color_channel(
    image: &TypedImage,
    colors: &[usize],
    color_count: usize,
    index: usize,
) -> Result<ConvertedChannel, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_color_channel_storage_normal(crate::image::typed_image_component_views(image),
    crate::image::typed_image_geometry(image),colors@,color_count,index);}
    let component_index = *colors.get(index).ok_or_else(invalid_color_input)?;
    let component = image
        .components()
        .get(component_index)
        .ok_or_else(invalid_color_input)?;
    let normalized = normalize_component(
        component,
        image.width(),
        image.height(),
        image.x_origin(),
        image.y_origin(),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=normalized {crate::specs::part2_color_channel_storage_normalize_error(
            crate::image::typed_image_component_views(image),crate::image::typed_image_geometry(image),colors@,color_count,index,error);}
    }
    let samples = normalized?;
    let channel_type = match (color_count, index) {
        (1, 0) => ConvertedChannelType::Gray,
        (3, 0) => ConvertedChannelType::Red,
        (3, 1) => ConvertedChannelType::Green,
        (3, 2) => ConvertedChannelType::Blue,
        _ => return Err(invalid_color_input()),
    };
    Ok(ConvertedChannel {
        channel_type,
        samples,
    })
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::specs::part2_color_alpha_storage_result(crate::image::typed_image_component_views(image),
            crate::image::typed_image_geometry(image),alpha,converted_channel_result(result)),
        result!=Err(DecodeError::AllocationFailed) ==> converted_channel_result(result) == crate::specs::color_convert_alpha(
            crate::image::typed_image_component_views(image), crate::image::typed_image_geometry(image), alpha,
        ),
    )
)]
fn convert_alpha_channel(
    image: &TypedImage,
    alpha: (usize, bool, ChannelAssociation),
) -> Result<ConvertedChannel, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_color_alpha_storage_normal(crate::image::typed_image_component_views(image),
    crate::image::typed_image_geometry(image),alpha);}
    let component = image
        .components()
        .get(alpha.0)
        .ok_or_else(invalid_color_input)?;
    let normalized = normalize_component(
        component,
        image.width(),
        image.height(),
        image.x_origin(),
        image.y_origin(),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=normalized {crate::specs::part2_color_alpha_storage_normalize_error(
            crate::image::typed_image_component_views(image),crate::image::typed_image_geometry(image),alpha,error);}
    }
    let samples = normalized?;
    Ok(ConvertedChannel {
        channel_type: ConvertedChannelType::Alpha {
            premultiplied: alpha.1,
            association: alpha.2,
        },
        samples,
    })
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_sycc_pixel(
            crate::image::typed_image_component_views(image),
            crate::image::typed_image_geometry(image).2, crate::image::typed_image_geometry(image).3,
            colors@, pixel, width,
        ),
    )
)]
fn convert_sycc_pixel(
    image: &TypedImage,
    colors: &[usize],
    pixel: usize,
    width: usize,
) -> Result<(u16, u16, u16), DecodeError> {
    let (x, y) = pixel_coordinates(pixel, width)?;
    let luminance = normalized_at(
        image,
        *colors.first().ok_or_else(invalid_color_input)?,
        x,
        y,
    )?;
    let cb =
        normalized_difference_at(image, *colors.get(1).ok_or_else(invalid_color_input)?, x, y)?;
    let cr =
        normalized_difference_at(image, *colors.get(2).ok_or_else(invalid_color_input)?, x, y)?;
    sycc_to_srgb(luminance, cb, cr)
}

struct SyccAxis {
    origin: u32,
    step: u8,
    registration: u16,
    first: u32,
    last: u32,
}

struct SyccPlan<'a> {
    luma: &'a TypedComponent,
    cb: &'a TypedComponent,
    cr: &'a TypedComponent,
    x: SyccAxis,
    y: SyccAxis,
}

struct SyccRow {
    base: Option<(u32, usize)>,
    chroma: Option<(usize, i32, i32)>,
}

#[cfg(verus_keep_ghost)]
verus! {
    use crate::specs::{
        ColorGeometry, Part1TypedComponentModel, color_chroma_at_index, color_registered_coordinate,
    };

    spec fn sycc_axis_matches(axis: SyccAxis, origin: u32, step: u8, registration: u16, size: u32) -> bool {
        &&& step > 0
        &&& size > 0
        &&& axis.origin == origin && axis.step == step && axis.registration == registration
        &&& color_registered_coordinate(origin, step as u32, registration, true) == Ok(axis.first)
        &&& axis.first as int + size as int == axis.last as int + 1 <= u32::MAX as int
    }

    spec fn sycc_axis_offset(axis: SyccAxis, coord: u32) -> int {
        let raw = crate::specs::part2_crg_component_predecessor(
            (axis.origin as int + coord as int) as u32, axis.step as u32, axis.registration) as u32 as int;
        (if raw < axis.first { axis.first as int } else if raw > axis.last { axis.last as int } else { raw })
            - axis.first as int
    }

    spec fn sycc_geometry(plan: &SyccPlan) -> ColorGeometry {
        let luma = typed_component_view(plan.luma);
        (luma.width, luma.height, plan.x.origin, plan.y.origin)
    }

    spec fn sycc_plan_geometry(plan: &SyccPlan, geometry: ColorGeometry) -> bool {
        let luma = typed_component_view(plan.luma);
        let cb = typed_component_view(plan.cb);
        let cr = typed_component_view(plan.cr);
        &&& 0 < geometry.0 && 0 < geometry.1
        &&& geometry.2 as int + geometry.0 as int <= u32::MAX as int
        &&& geometry.3 as int + geometry.1 as int <= u32::MAX as int
        &&& luma.width == geometry.0 && luma.height == geometry.1
        &&& luma.info.x_subsampling == 1 && luma.info.y_subsampling == 1
        &&& luma.info.x_registration == 0 && luma.info.y_registration == 0
        &&& 0 < luma.info.precision <= 38 && 0 < cb.info.precision <= 38 && 0 < cr.info.precision <= 38
        &&& cb.width == cr.width && cb.height == cr.height
        &&& cb.info.x_subsampling == cr.info.x_subsampling && cb.info.y_subsampling == cr.info.y_subsampling
        &&& cb.info.x_registration == cr.info.x_registration && cb.info.y_registration == cr.info.y_registration
        &&& sycc_axis_matches(plan.x, geometry.2, cb.info.x_subsampling, cb.info.x_registration, cb.width)
        &&& sycc_axis_matches(plan.y, geometry.3, cb.info.y_subsampling, cb.info.y_registration, cb.height)
        &&& cb.width as int * cb.height as int <= usize::MAX as int
    }

    spec fn sycc_plan_matches(
        plan: &SyccPlan, components: Seq<Part1TypedComponentModel>, colors: Seq<usize>, geometry: ColorGeometry,
    ) -> bool {
        &&& colors.len() == 3
        &&& colors[0] < components.len() && colors[1] < components.len() && colors[2] < components.len()
        &&& typed_component_view(plan.luma) == components[colors[0] as int]
        &&& typed_component_view(plan.cb) == components[colors[1] as int]
        &&& typed_component_view(plan.cr) == components[colors[2] as int]
        &&& plan.x.origin == geometry.2 && plan.y.origin == geometry.3
        &&& sycc_plan_geometry(plan, geometry)
    }

    spec fn sycc_row_valid(plan: &SyccPlan, row: SyccRow) -> bool {
        &&& match row.base {
            Some((y, base)) => y < sycc_geometry(plan).1
                && base as int == sycc_axis_offset(plan.y, y) * typed_component_view(plan.cb).width as int,
            None => true,
        }

        &&& match row.chroma {
            Some((index, cb, cr)) => color_chroma_at_index(typed_component_view(plan.cb), index) == Ok(cb)
                && color_chroma_at_index(typed_component_view(plan.cr), index) == Ok(cr),
            None => true,
        }
    }

    #[verifier::opaque]
    spec fn sycc_planned_pixel(plan: &SyccPlan, pixel: usize, width: usize)
        -> Result<(u16, u16, u16), DecodeError> {
        crate::specs::color_sycc_pixel(
            seq![typed_component_view(plan.luma), typed_component_view(plan.cb), typed_component_view(plan.cr)],
            plan.x.origin, plan.y.origin, seq![0usize, 1usize, 2usize], pixel, width,
        )
    }

    proof fn sycc_pixel_routing(
        plan: &SyccPlan, components: Seq<Part1TypedComponentModel>, colors: Seq<usize>,
        geometry: ColorGeometry, pixel: usize, width: usize,
    )
        requires sycc_plan_matches(plan, components, colors, geometry),
        ensures sycc_planned_pixel(plan, pixel, width)
            == crate::specs::color_sycc_pixel(components, geometry.2, geometry.3, colors, pixel, width),
    { reveal(sycc_planned_pixel); }

    #[verifier::opaque]
    spec fn sycc_indexed_pixel(plan: &SyccPlan, pixel: usize, chroma: usize)
        -> Result<(u16, u16, u16), DecodeError> {
        let luma = typed_component_view(plan.luma);
        match crate::specs::color_nominal_at_index(luma, pixel) {
            Err(error) => Err(error),
            Ok(value) => match crate::specs::color_normalize_unsigned(value, luma.info.precision) {
                Err(error) => Err(error),
                Ok(y) => match color_chroma_at_index(typed_component_view(plan.cb), chroma) {
                    Err(error) => Err(error),
                    Ok(cb) => match color_chroma_at_index(typed_component_view(plan.cr), chroma) {
                        Err(error) => Err(error),
                        Ok(cr) => crate::specs::color_sycc_to_srgb(y, cb, cr),
                    }
                },
            },
        }
    }

    proof fn sycc_indexed_pixel_matches(plan: &SyccPlan, pixel: usize, width: usize, x: u32, y: u32, index: usize)
        requires
            sycc_plan_geometry(plan, sycc_geometry(plan)),
            crate::specs::color_pixel_coordinates(pixel, width) == Ok((x, y)),
            crate::specs::color_component_index(typed_component_view(plan.luma), plan.x.origin, plan.y.origin, x, y) == Ok(pixel),
            crate::specs::color_component_index(typed_component_view(plan.cb), plan.x.origin, plan.y.origin, x, y) == Ok(index),
            crate::specs::color_component_index(typed_component_view(plan.cr), plan.x.origin, plan.y.origin, x, y) == Ok(index),
        ensures sycc_indexed_pixel(plan, pixel, index) == sycc_planned_pixel(plan, pixel, width),
    {
        reveal(sycc_indexed_pixel);
        reveal(sycc_planned_pixel);
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures match result {
        Some(plan) => sycc_plan_matches(&plan, typed_image_component_views(image), colors@, typed_image_geometry(image)),
        None => true,
    },
))]
fn plan_sycc_rows<'a>(image: &'a TypedImage, colors: &[usize]) -> Option<SyccPlan<'a>> {
    if colors.len() != 3 {
        return None;
    }
    let luma = image.components().get(colors[0])?;
    let cb = image.components().get(colors[1])?;
    let cr = image.components().get(colors[2])?;
    let width = image.width();
    let height = image.height();
    let yi = luma.info();
    let bi = cb.info();
    let ri = cr.info();
    if width == 0
        || height == 0
        || luma.width() != width
        || luma.height() != height
        || yi.x_subsampling != 1
        || yi.y_subsampling != 1
        || yi.x_registration != 0
        || yi.y_registration != 0
        || bi.x_subsampling != 2
        || (bi.y_subsampling != 1 && bi.y_subsampling != 2)
        || bi.x_subsampling != ri.x_subsampling
        || bi.y_subsampling != ri.y_subsampling
        || bi.x_registration != ri.x_registration
        || bi.y_registration != ri.y_registration
        || cb.width() != cr.width()
        || cb.height() != cr.height()
        || yi.precision == 0
        || yi.precision > 38
        || bi.precision == 0
        || bi.precision > 38
        || ri.precision == 0
        || ri.precision > 38
    {
        return None;
    }
    let ox = image.x_origin();
    let oy = image.y_origin();
    ox.checked_add(width)?;
    oy.checked_add(height)?;
    let Ok(_) = checked_area(cb.width(), cb.height()) else {
        return None;
    };
    // The converter has already admitted all selected components, including
    // sample storage lengths and alpha, before making any output reservation.
    let x = plan_sycc_axis(ox, bi.x_subsampling, bi.x_registration, cb.width())?;
    let y = plan_sycc_axis(oy, bi.y_subsampling, bi.y_registration, cb.height())?;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_layer_area); }
    Some(SyccPlan { luma, cb, cr, x, y })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures match result {
        Some(axis) => sycc_axis_matches(axis, origin, step, registration, size),
        None => true,
    },
))]
fn plan_sycc_axis(origin: u32, step: u8, registration: u16, size: u32) -> Option<SyccAxis> {
    if step == 0 || size == 0 {
        return None;
    }
    let Ok(first) = registered_ceil_div(origin, u32::from(step), registration) else {
        return None;
    };
    let last = first.checked_add(size)? - 1;
    Some(SyccAxis {
        origin,
        step,
        registration,
        first,
        last,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires axis.step > 0, axis.first <= axis.last, axis.origin as int + coord as int <= u32::MAX as int,
    ensures result == Ok(sycc_axis_offset(*axis, coord) as u32),
        match result { Ok(offset) => 0 <= offset <= axis.last - axis.first, Err(_) => false },
))]
fn sycc_axis_offset_at(axis: &SyccAxis, coord: u32) -> Result<u32, DecodeError> {
    let raw = registered_floor_div(axis.origin + coord, u32::from(axis.step), axis.registration)?;
    let clamped = if raw < axis.first {
        axis.first
    } else if raw > axis.last {
        axis.last
    } else {
        raw
    };
    Ok(clamped - axis.first)
}

#[cfg(verus_keep_ghost)]
verus! {
    proof fn sycc_row_indices(plan: &SyccPlan, pixel: usize, width: usize, x: u32, y: u32, index: usize)
        requires
            sycc_plan_geometry(plan, sycc_geometry(plan)),
            width == sycc_geometry(plan).0,
            x < sycc_geometry(plan).0, y < sycc_geometry(plan).1,
            crate::specs::color_pixel_coordinates(pixel, width) == Ok((x, y)),
            index as int == sycc_axis_offset(plan.y, y) * typed_component_view(plan.cb).width as int
                + sycc_axis_offset(plan.x, x),
        ensures
            crate::specs::color_component_index(typed_component_view(plan.luma), plan.x.origin, plan.y.origin, x, y) == Ok(pixel),
            crate::specs::color_component_index(typed_component_view(plan.cb), plan.x.origin, plan.y.origin, x, y) == Ok(index),
            crate::specs::color_component_index(typed_component_view(plan.cr), plan.x.origin, plan.y.origin, x, y) == Ok(index),
    {
        use crate::proofs::production_impl::production_color_unit_coordinate;
        use crate::specs::color_component_index;
        let ox = plan.x.origin;
        let oy = plan.y.origin;
        let luma = typed_component_view(plan.luma);
        let cb = typed_component_view(plan.cb);
        let cr = typed_component_view(plan.cr);
        let ax = (ox as int + x as int) as u32;
        let ay = (oy as int + y as int) as u32;
        assert(ox <= ax && (ax as int) < ox as int + luma.width as int);
        assert(oy <= ay && (ay as int) < oy as int + luma.height as int);
        production_color_unit_coordinate(plan.x.origin);
        production_color_unit_coordinate(plan.y.origin);
        production_color_unit_coordinate(ax);
        production_color_unit_coordinate(ay);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pixel as int, width as int);
        assert(x as int == pixel as int % width as int);
        assert(y as int == pixel as int / width as int);
        assert(y as int * luma.width as int + x as int == pixel as int) by(nonlinear_arith)
            requires y as int == pixel as int / width as int, x as int == pixel as int % width as int,
                pixel as int == width as int * (pixel as int / width as int) + pixel as int % width as int,
                width as int == luma.width as int;
        assert(color_component_index(luma, ox, oy, x, y) == Ok(pixel));
        sycc_chroma_index(cb, plan.x, plan.y, x, y, index);
        sycc_chroma_index(cr, plan.x, plan.y, x, y, index);
    }

    proof fn sycc_chroma_index(
        c: Part1TypedComponentModel, horizontal: SyccAxis, vertical: SyccAxis, x: u32, y: u32, index: usize,
    )
        requires
            0 < c.info.precision <= 38,
            sycc_axis_matches(horizontal, horizontal.origin, c.info.x_subsampling, c.info.x_registration, c.width),
            sycc_axis_matches(vertical, vertical.origin, c.info.y_subsampling, c.info.y_registration, c.height),
            horizontal.origin as int + x as int <= u32::MAX as int,
            vertical.origin as int + y as int <= u32::MAX as int,
            index as int == sycc_axis_offset(vertical, y) * c.width as int + sycc_axis_offset(horizontal, x),
        ensures crate::specs::color_component_index(c, horizontal.origin, vertical.origin, x, y) == Ok(index),
    {
        let ax = (horizontal.origin as int + x as int) as u32;
        let ay = (vertical.origin as int + y as int) as u32;
        let sx = crate::specs::part2_crg_component_predecessor(ax, horizontal.step as u32, horizontal.registration) as u32;
        let sy = crate::specs::part2_crg_component_predecessor(ay, vertical.step as u32, vertical.registration) as u32;
        assert(color_registered_coordinate(ax, c.info.x_subsampling as u32, c.info.x_registration, false) == Ok(sx));
        assert(color_registered_coordinate(ay, c.info.y_subsampling as u32, c.info.y_registration, false) == Ok(sy));
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        sycc_plan_geometry(plan, sycc_geometry(plan)),
        width == sycc_geometry(plan).0,
        (pixel as int) < width as int * sycc_geometry(plan).1 as int,
        sycc_row_valid(plan, *old(row)),
    ensures
        sycc_row_valid(plan, *final(row)),
        result == sycc_planned_pixel(plan, pixel, width),
))]
fn convert_sycc_row_pixel(
    plan: &SyccPlan<'_>,
    row: &mut SyccRow,
    pixel: usize,
    width: usize,
) -> Result<(u16, u16, u16), DecodeError> {
    let index = sycc_row_index(plan, row, pixel, width);
    #[cfg(verus_keep_ghost)]
    proof! { assert(index.is_ok()); }
    sycc_indexed_sample(plan, row, pixel, index?)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        sycc_plan_geometry(plan, sycc_geometry(plan)),
        width == sycc_geometry(plan).0,
        (pixel as int) < width as int * sycc_geometry(plan).1 as int,
        sycc_row_valid(plan, *old(row)),
    ensures
        sycc_row_valid(plan, *final(row)),
        match result {
            Ok(index) => sycc_indexed_pixel(plan, pixel, index) == sycc_planned_pixel(plan, pixel, width),
            Err(_) => false,
        },
))]
fn sycc_row_index(
    plan: &SyccPlan<'_>,
    row: &mut SyccRow,
    pixel: usize,
    width: usize,
) -> Result<usize, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        let w = width as int;
        let h = sycc_geometry(plan).1 as int;
        let p = pixel as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p, w);
        assert(0 <= p % w < w);
        assert(0 <= p / w < h) by(nonlinear_arith)
            requires w > 0, 0 <= p < w * h, 0 <= p % w < w, p == w * (p / w) + p % w, p / w >= 0;
    }
    let (x, y) = pixel_coordinates(pixel, width)?;
    let cw = plan.cb.width() as usize;
    let base = match row.base {
        Some((line, base)) if line == y => base,
        _ => {
            let iy = sycc_axis_offset_at(&plan.y, y)? as usize;
            #[cfg(verus_keep_ghost)]
            proof! {
                let h = typed_component_view(plan.cb).height as int;
                let w = typed_component_view(plan.cb).width as int;
                assert(0 <= iy < h);
                assert(iy as int * w <= w * h) by(nonlinear_arith)
                    requires 0 <= (iy as int) < h, w >= 0;
            }
            let base = iy * cw;
            row.base = Some((y, base));
            row.chroma = None;
            base
        }
    };
    let ix = sycc_axis_offset_at(&plan.x, x)? as usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        let h = typed_component_view(plan.cb).height as int;
        let w = typed_component_view(plan.cb).width as int;
        let iy = sycc_axis_offset(plan.y, y);
        assert(0 <= iy < h);
        assert(0 <= ix < w);
        assert(base as int + (ix as int) < w * h) by(nonlinear_arith)
            requires 0 <= iy < h, 0 <= (ix as int) < w, base as int == iy * w, w > 0;
    }
    let index = base + ix;
    #[cfg(verus_keep_ghost)]
    proof! {
        sycc_row_indices(plan, pixel, width, x, y, index);
        sycc_indexed_pixel_matches(plan, pixel, width, x, y, index);
    }
    Ok(index)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires sycc_plan_geometry(plan, sycc_geometry(plan)), sycc_row_valid(plan, *old(row)),
    ensures sycc_row_valid(plan, *final(row)),
        result == sycc_indexed_pixel(plan, pixel, index),
))]
fn sycc_indexed_sample(
    plan: &SyccPlan<'_>,
    row: &mut SyccRow,
    pixel: usize,
    index: usize,
) -> Result<(u16, u16, u16), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(sycc_indexed_pixel); }
    // Keep first sample errors in raster order, and Y before Cb before Cr.
    // Only a pair that already succeeded may be reused.
    let luminance = normalize_unsigned(
        nominal_at_index(plan.luma, pixel)?,
        plan.luma.info().precision,
    )?;
    let (cb, cr) = match row.chroma {
        Some((previous, cb, cr)) if previous == index => (cb, cr),
        _ => {
            let cb = chroma_at_index(plan.cb, index)?;
            let cr = chroma_at_index(plan.cr, index)?;
            row.chroma = Some((index, cb, cr));
            (cb, cr)
        }
    };
    sycc_to_srgb(luminance, cb, cr)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::color_sycc_to_srgb(y, cb, cr),)
)]
pub(super) fn sycc_to_srgb(y: u16, cb: i32, cr: i32) -> Result<(u16, u16, u16), DecodeError> {
    let y = i128::from(y);
    let cb = i128::from(cb);
    let cr = i128::from(cr);
    let red_delta = rounded_fixed(
        91_881_i128
            .checked_mul(cr)
            .ok_or_else(arithmetic_overflow)?,
    )?;
    let green_blue_delta = rounded_fixed(
        22_554_i128
            .checked_mul(cb)
            .ok_or_else(arithmetic_overflow)?,
    )?;
    let green_red_delta = rounded_fixed(
        46_802_i128
            .checked_mul(cr)
            .ok_or_else(arithmetic_overflow)?,
    )?;
    let blue_delta = rounded_fixed(
        116_130_i128
            .checked_mul(cb)
            .ok_or_else(arithmetic_overflow)?,
    )?;
    let red = y.checked_add(red_delta).ok_or_else(arithmetic_overflow)?;
    let green = y
        .checked_sub(green_blue_delta)
        .ok_or_else(arithmetic_overflow)?;
    let green = green
        .checked_sub(green_red_delta)
        .ok_or_else(arithmetic_overflow)?;
    let blue = y.checked_add(blue_delta).ok_or_else(arithmetic_overflow)?;
    Ok((clamp_u16(red), clamp_u16(green), clamp_u16(blue)))
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::color_rounded_fixed(value),)
)]
pub(super) fn rounded_fixed(value: i128) -> Result<i128, DecodeError> {
    if value < 0 {
        Ok(value
            .checked_sub(FIXED_ONE / 2)
            .ok_or_else(arithmetic_overflow)?
            / FIXED_ONE)
    } else {
        Ok(value
            .checked_add(FIXED_ONE / 2)
            .ok_or_else(arithmetic_overflow)?
            / FIXED_ONE)
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::color_clamp_u16(value as int),)
)]
fn clamp_u16(value: i128) -> u16 {
    if value <= 0 {
        0
    } else if value >= i128::from(u16::MAX) {
        u16::MAX
    } else {
        value as u16
    }
}
