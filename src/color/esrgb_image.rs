//! PIMA 7667:2001 Annex A.3 default encoded-RGB clipping to sRGB16.
//! Fractional sRGB codes survive until half-up output quantization.
use super::admission::{channel_layout, validate_components, validate_output_size};
use super::esrgb::esrgb_sample_to_srgb16;
use super::geometry::{
    arithmetic_overflow, checked_area, invalid_channel_layout, invalid_color_input, unsupported,
};
use super::normalization::{nominal_component_at, pixel_coordinates};
use super::{ConvertedChannel, ConvertedChannelType, ConvertedColorSpace, ConvertedImage};
#[cfg(verus_keep_ghost)]
use super::{converted_channel_views, converted_image_result, normalized_plane_result};
use crate::image::{TypedComponent, TypedImage, TypedSamples};
use crate::{DecodeError, ResourceLimits, UnsupportedColorConversion};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::color_esrgb_source_component(
        crate::image::typed_component_view(component),precision),
))]
fn validate_source_component(component: &TypedComponent, precision: u8) -> Result<(), DecodeError> {
    if component.info().precision != precision
        || component.info().signed
        || matches!(component.samples(), TypedSamples::Signed(_))
    {
        return Err(invalid_color_input());
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::color_esrgb_source(crate::image::typed_image_value_view(*image)),
))]
fn validate_source(image: &TypedImage) -> Result<(), DecodeError> {
    if image.width() == 0 || image.height() == 0 {
        return Err(invalid_color_input());
    }
    if image.components().len() != 3 {
        return Err(invalid_channel_layout());
    }
    let precision = image.components()[0].info().precision;
    if precision != 10 && precision != 12 && precision != 16 {
        return Err(unsupported(
            UnsupportedColorConversion::EnumeratedColorSpace,
        ));
    }
    validate_source_component(&image.components()[0], precision)?;
    validate_source_component(&image.components()[1], precision)?;
    validate_source_component(&image.components()[2], precision)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::color_esrgb_pixel(
        crate::image::typed_component_view(component),crate::image::typed_image_geometry(image),width,pixel),
))]
fn convert_pixel(
    image: &TypedImage,
    component: &TypedComponent,
    width: usize,
    pixel: usize,
) -> Result<u16, DecodeError> {
    let (x, y) = pixel_coordinates(pixel, width)?;
    let value = nominal_component_at(component, image.x_origin(), image.y_origin(), x, y)?;
    esrgb_sample_to_srgb16(value, component.info().precision)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_esrgb_plane_storage_result(crate::image::typed_image_value_view(*image),
        colors@,role,normalized_plane_result(result)),
    result != Err(DecodeError::AllocationFailed) ==> normalized_plane_result(result)
        == crate::specs::color_esrgb_plane(crate::image::typed_image_value_view(*image),colors@,role),
))]
fn convert_plane(
    image: &TypedImage,
    colors: &[usize],
    role: usize,
) -> Result<Vec<u16>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost source=crate::image::typed_image_value_view(*image);
        let ghost geometry=source.0;
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_esrgb_plane_normal(source,colors@,role); }
    let index = *colors.get(role).ok_or_else(invalid_color_input)?;
    let component = image
        .components()
        .get(index)
        .ok_or_else(invalid_color_input)?;
    let width = usize::try_from(image.width()).map_err(|_| arithmetic_overflow())?;
    if width == 0 {
        return Err(invalid_color_input());
    }
    let count = checked_area(image.width(), image.height())?;
    let allocated = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let request=crate::specs::Part2ColorOutputCapacity::EsrgbPlane {image:source,colors:colors@,role};
        crate::specs::part2_color_output_capacity_observed(request,crate::allocation::inspection_capacity_outcome(allocated));
        if let Err(error)=allocated {crate::specs::part2_esrgb_plane_refused(source,colors@,role,error);}
    }
    let mut output = allocated?;
    let mut pixel = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::color_esrgb_plane_prefix); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant pixel <= count,
            source == crate::image::typed_image_value_view(*image),
            geometry == source.0,
            role < colors.len(), index == colors@[role as int],
            index < source.1.len(),
            crate::image::typed_component_view(component) == source.1[index as int],
            crate::specs::color_esrgb_plane_admission(source,colors@,role)
                == Ok((crate::image::typed_component_view(component),width,count)),
            crate::specs::color_esrgb_plane_prefix(crate::image::typed_component_view(component),geometry,width,pixel as nat)
                == Ok(output@),
            crate::specs::part2_esrgb_plane_storage_result(source,colors@,role,crate::specs::color_esrgb_plane(source,colors@,role)),
        decreases count - pixel,
    ))]
    while pixel < count {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::color_esrgb_plane_prefix,1); }
        let value = match convert_pixel(image, component, width, pixel) {
            Ok(value) => value,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::color_esrgb_prefix_error(crate::image::typed_component_view(component),geometry,width,
                        pixel as nat+1,count as nat,error);
                }
                return Err(error);
            }
        };
        output.push(value);
        pixel += 1;
    }
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_color_convert_storage_result(crate::specs::Part2ColorConvertContext {
        image:crate::image::typed_image_value_view(*image),method:crate::jp2::ColorMethod::Enumerated {color_space:20},
        bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits),
    },converted_image_result(result)),
    result != Err(DecodeError::AllocationFailed) ==> converted_image_result(result)
        == crate::specs::color_convert_esrgb(crate::image::typed_image_value_view(*image),
            crate::limits::resource_decoded_bytes_limit(limits),crate::limits::resource_work_limit(limits)),
))]
pub(super) fn convert_esrgb_color(
    image: &TypedImage,
    limits: &ResourceLimits,
) -> Result<ConvertedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost source=crate::image::typed_image_value_view(*image);
        let ghost context=crate::specs::Part2ColorConvertContext {
            image:source,method:crate::jp2::ColorMethod::Enumerated {color_space:20},
            bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits)};
    }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_color_convert_storage_normal(context);}
    validate_source(image)?;
    let organized = channel_layout(image, 3);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=organized {crate::specs::part2_esrgb_layout_error(context,error);}
    }
    let layout = organized?;
    if layout.colors.len() != 3 {
        return Err(invalid_channel_layout());
    }
    if !layout.alphas.is_empty() {
        return Err(unsupported(UnsupportedColorConversion::AlphaAssociation));
    }
    validate_components(image, &layout)?;
    validate_output_size(image, 3, 0, limits)?;
    let _count = checked_area(image.width(), image.height())?;
    let allocated = crate::allocation::empty_with_capacity(3);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::color_esrgb_preflight(context)==Ok(((layout.colors@,layout.alphas@),_count)));
        let request=crate::specs::Part2ColorOutputCapacity::EsrgbChannels {context};
        crate::specs::part2_color_output_capacity_observed(request,crate::allocation::inspection_capacity_outcome(allocated));
        if let Err(error)=allocated {
            crate::specs::part2_esrgb_channels_present(context);
            crate::specs::part2_color_convert_storage_refused(context,request,error);
        }
    }
    let mut channels = allocated?;
    let red = match convert_plane(image, &layout.colors, 0) {
        Ok(value) => value,
        Err(error) => {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_esrgb_child_error(context,layout.colors@,0,error);}
            return Err(error);
        }
    };
    let green = match convert_plane(image, &layout.colors, 1) {
        Ok(value) => value,
        Err(error) => {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_esrgb_child_error(context,layout.colors@,1,error);}
            return Err(error);
        }
    };
    let blue = match convert_plane(image, &layout.colors, 2) {
        Ok(value) => value,
        Err(error) => {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_esrgb_child_error(context,layout.colors@,2,error);}
            return Err(error);
        }
    };
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
        assert(converted_channel_views(channels@) =~= crate::specs::color_esrgb_planes(source,layout.colors@).get_Ok_0());
    }
    Ok(ConvertedImage {
        width: image.width(),
        height: image.height(),
        color_space: ConvertedColorSpace::Srgb,
        precision: 16,
        channels,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codestream::ComponentInfo;
    use crate::image::{ChannelAssociation, ChannelDefinition, ChannelType};
    use crate::jp2::ColorSpecification;
    use crate::{MalformedKind, Resource};

    fn component(values: &[u64], precision: u8) -> TypedComponent {
        TypedComponent::from_parts(
            values.len() as u32,
            1,
            ComponentInfo {
                precision,
                signed: false,
                x_subsampling: 1,
                y_subsampling: 1,
                x_registration: 0,
                y_registration: 0,
            },
            TypedSamples::Unsigned(values.to_vec()),
        )
    }

    fn image(width: u32, components: Vec<TypedComponent>) -> TypedImage {
        TypedImage::from_components(width, 1, components, &ResourceLimits::default()).unwrap()
    }

    fn convert(image: &TypedImage, limits: &ResourceLimits) -> Result<ConvertedImage, DecodeError> {
        super::super::conversion::convert_jp2_color(
            image,
            &ColorSpecification::enumerated(20),
            limits,
        )
    }

    #[test]
    fn pima_images_clip_and_keep_fractional_codes_at_all_supported_precisions() {
        for (precision, black, white, maximum, half, last) in [
            (10, 384, 894, 1023, 1, 65407),
            (12, 1536, 3576, 4095, 4, 65503),
            (16, 24576, 57216, 65535, 64, 65533),
        ] {
            let values = [0, black - 1, black, black + half, white - 1, white, maximum];
            let input = image(7, (0..3).map(|_| component(&values, precision)).collect());
            let output = convert(&input, &ResourceLimits::default()).unwrap();
            assert_eq!(output.color_space, ConvertedColorSpace::Srgb);
            assert_eq!(output.precision, 16);
            assert_eq!((output.width, output.height), (7, 1));
            for channel in output.channels {
                assert_eq!(channel.samples, [0, 0, 0, 129, last, 65535, 65535]);
            }
        }
    }

    #[test]
    fn cdef_reorders_rgb_without_relabeling_bad_associations() {
        let mut components = vec![
            component(&[894, 384], 10),
            component(&[384, 894], 10),
            component(&[640, 640], 10),
        ];
        for (component, association) in components.iter_mut().zip([3, 1, 2]) {
            component.add_channel_definition(ChannelDefinition::new(
                ChannelType::Color,
                ChannelAssociation::Color(association),
            ));
        }
        let input = image(2, components);
        let output = convert(&input, &ResourceLimits::default()).unwrap();
        assert_eq!(output.channels[0].channel_type, ConvertedChannelType::Red);
        assert_eq!(output.channels[0].samples, [0, 65535]);
        assert_eq!(output.channels[1].channel_type, ConvertedChannelType::Green);
        assert_eq!(output.channels[1].samples, [32896, 32896]);
        assert_eq!(output.channels[2].channel_type, ConvertedChannelType::Blue);
        assert_eq!(output.channels[2].samples, [65535, 0]);

        let mut bad = component(&[384], 10);
        bad.add_channel_definition(ChannelDefinition::new(
            ChannelType::Color,
            ChannelAssociation::WholeImage,
        ));
        assert_eq!(
            convert(
                &image(1, vec![bad, component(&[384], 10), component(&[384], 10)]),
                &ResourceLimits::default()
            ),
            Err(invalid_channel_layout()),
        );
    }

    #[test]
    fn sampling_obeys_raw_origins_subsampling_and_registration() {
        for (registration, expected) in [
            (0, vec![0, 0, 0, 32896, 32896, 65535]),
            (32768, vec![0, 0, 0, 0, 32896, 32896]),
        ] {
            let components = (0..3)
                .map(|_| {
                    let mut info = component(&[], 10).info();
                    info.x_subsampling = 2;
                    info.x_registration = registration;
                    TypedComponent::from_parts(
                        3,
                        1,
                        info,
                        TypedSamples::Unsigned(vec![384, 640, 894]),
                    )
                })
                .collect();
            let input = TypedImage::from_components_with_origin(
                6,
                1,
                1,
                3,
                components,
                &ResourceLimits::default(),
            )
            .unwrap();
            let output = convert(&input, &ResourceLimits::default()).unwrap();
            for channel in output.channels {
                assert_eq!(channel.samples, expected);
            }
            let components = (0..3)
                .map(|_| {
                    let mut info = component(&[], 10).info();
                    info.x_subsampling = 2;
                    info.y_subsampling = 2;
                    TypedComponent::from_parts(
                        2,
                        2,
                        info,
                        TypedSamples::Unsigned(vec![384, 640, 894, 385]),
                    )
                })
                .collect();
            let input = TypedImage::from_components_with_origin(
                4,
                4,
                1,
                1,
                components,
                &ResourceLimits::default(),
            )
            .unwrap();
            let output = convert(&input, &ResourceLimits::default()).unwrap();
            for channel in output.channels {
                assert_eq!(
                    channel.samples,
                    [
                        0, 0, 0, 32896, 0, 0, 0, 32896, 0, 0, 0, 32896, 65535, 65535, 65535, 129,
                    ]
                );
            }
        }
    }

    #[test]
    fn source_preflight_rejects_precision_sign_count_and_shape_explicitly() {
        let limits = ResourceLimits::default();
        for precision in [0, 8, 9, 11, 13, 15, 17, 38] {
            let input = image(1, (0..3).map(|_| component(&[0], precision)).collect());
            crate::allocation::with_refusal(0, || {
                assert_eq!(
                    convert(&input, &limits),
                    Err(unsupported(
                        UnsupportedColorConversion::EnumeratedColorSpace
                    ))
                );
                assert_eq!(
                    crate::allocation::empty_with_capacity::<u8>(1),
                    Err(DecodeError::AllocationFailed)
                );
            });
        }
        let mixed = image(
            1,
            vec![
                component(&[384], 10),
                component(&[1536], 12),
                component(&[384], 10),
            ],
        );
        assert_eq!(convert(&mixed, &limits), Err(invalid_color_input()));
        for mismatch in [false, true] {
            let mut info = component(&[], 10).info();
            info.signed = !mismatch;
            let signed = TypedComponent::from_parts(1, 1, info, TypedSamples::Signed(vec![384]));
            assert_eq!(
                convert(
                    &image(
                        1,
                        vec![signed, component(&[384], 10), component(&[384], 10)]
                    ),
                    &limits
                ),
                Err(invalid_color_input())
            );
        }
        assert_eq!(
            convert(&image(1, Vec::new()), &limits),
            Err(invalid_channel_layout())
        );
        let wrong_shape = image(2, (0..3).map(|_| component(&[384], 10)).collect());
        assert_eq!(convert(&wrong_shape, &limits), Err(invalid_color_input()));
    }

    #[test]
    fn opacity_is_not_guessed_or_converted_as_premultiplied_rgb() {
        for kind in [ChannelType::Opacity, ChannelType::PremultipliedOpacity] {
            let mut components: Vec<_> = (0..3).map(|_| component(&[384], 10)).collect();
            for (index, c) in components.iter_mut().enumerate() {
                c.add_channel_definition(ChannelDefinition::new(
                    ChannelType::Color,
                    ChannelAssociation::Color(index as u16 + 1),
                ));
            }
            components[0].add_channel_definition(ChannelDefinition::new(
                kind,
                ChannelAssociation::WholeImage,
            ));
            assert_eq!(
                convert(&image(1, components), &ResourceLimits::default()),
                Err(unsupported(UnsupportedColorConversion::AlphaAssociation))
            );
        }
        let rgba = image(1, (0..4).map(|_| component(&[384], 10)).collect());
        assert_eq!(
            convert(&rgba, &ResourceLimits::default()),
            Err(invalid_channel_layout())
        );
    }

    #[test]
    fn every_reached_output_owner_can_refuse_and_retry_exactly() {
        let limits = ResourceLimits::default();
        let input = image(2, (0..3).map(|_| component(&[384, 894], 10)).collect());
        let expected = convert(&input, &limits).unwrap();
        for after in 0..5 {
            assert_eq!(
                crate::allocation::with_refusal(after, || convert(&input, &limits)),
                Err(DecodeError::AllocationFailed)
            );
            assert_eq!(convert(&input, &limits).unwrap(), expected);
        }
        assert_eq!(
            crate::allocation::with_refusal(5, || convert(&input, &limits)).unwrap(),
            expected
        );
        for (limits, resource, actual) in [
            (
                ResourceLimits::default()
                    .with_maximum_decoded_bytes(11)
                    .unwrap(),
                Resource::DecodedBytes,
                12,
            ),
            (
                ResourceLimits::default()
                    .with_maximum_work_units(5)
                    .unwrap(),
                Resource::WorkUnits,
                6,
            ),
        ] {
            crate::allocation::with_refusal(1, || {
                assert!(matches!(convert(&input, &limits),
                    Err(DecodeError::LimitExceeded { resource: r, actual: a, .. }) if r==resource && a==actual));
                assert_eq!(
                    crate::allocation::empty_with_capacity::<u8>(1),
                    Err(DecodeError::AllocationFailed)
                );
            });
        }
    }

    #[test]
    fn sample_error_prevents_later_plane_requests_and_retry_preserves_source() {
        for role in 0..3 {
            let mut components: Vec<_> = (0..3).map(|_| component(&[384, 894], 10)).collect();
            components[role] = component(&[384, 1024], 10);
            let input = image(2, components);
            let expected = Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::ContainerCodestreamMismatch,
            });
            crate::allocation::with_refusal(3 + role, || {
                assert_eq!(convert(&input, &ResourceLimits::default()), expected);
                assert_eq!(
                    crate::allocation::empty_with_capacity::<u8>(1),
                    Err(DecodeError::AllocationFailed)
                );
            });
            assert_eq!(convert(&input, &ResourceLimits::default()), expected);
        }
    }
}
