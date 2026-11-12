use super::*;
use crate::{
    codestream::ComponentInfo,
    image::{ChannelDefinition, ChannelType, TypedComponent, TypedImage, TypedSamples},
};

#[test]
fn sarah_engineering_crg_predecessor_uses_component_separation() {
    for sampling in [1_u32, 2, 4, 8, 255] {
        for registration in [0_u16, 1, 32_768, u16::MAX] {
            for value in 0..=2 * sampling + 3 {
                let position = u128::from(value) * 65_536;
                let phase = u128::from(sampling) * u128::from(registration);
                let expected =
                    (position.saturating_sub(phase) / (u128::from(sampling) * 65_536)) as u32;
                assert_eq!(
                    registered_floor_div(value, sampling, registration),
                    Ok(expected),
                    "value={value} sampling={sampling} registration={registration}"
                );
                assert_eq!(
                    registered_ceil_div(value, sampling, registration),
                    Ok(value.div_ceil(sampling))
                );
            }
        }
    }
}

#[test]
fn sarah_engineering_crg_context_and_full_sampling_select_identical_actual_values() {
    let info = ComponentInfo {
        precision: 8,
        signed: false,
        x_subsampling: 4,
        y_subsampling: 1,
        x_registration: 32_768,
        y_registration: 0,
    };
    let values = [0_u64, 64, 128, 255];
    let full = TypedComponent::from_parts(4, 1, info, TypedSamples::Unsigned(values.to_vec()));
    for (coordinate, origin, expected) in [
        (9_u32, 4_u32, 64_u64),
        (10, 8, 128),
        (13, 8, 128),
        (14, 12, 255),
    ] {
        let start = origin.div_ceil(4) as usize;
        let end = (coordinate + 1).div_ceil(4) as usize;
        let cropped = TypedComponent::from_parts(
            (end - start) as u32,
            1,
            info,
            TypedSamples::Unsigned(values[start..end].to_vec()),
        );
        assert_eq!(
            super::normalization::nominal_component_at(&full, 0, 0, coordinate, 0),
            Ok(expected)
        );
        assert_eq!(
            super::normalization::nominal_component_at(&cropped, origin, 0, coordinate - origin, 0),
            Ok(expected)
        );
    }
}

fn registered_coordinate_wide(value: u32, sampling: u8, registration: u16, ceil: bool) -> u128 {
    let phase = u128::from(registration) * if ceil { 1 } else { u128::from(sampling) };
    let numerator = (u128::from(value) * 65_536).saturating_sub(phase);
    let denominator = u128::from(sampling) * 65_536;
    if ceil {
        numerator.div_ceil(denominator)
    } else {
        numerator / denominator
    }
}

fn sampled_nominal_plane_wide_reference(
    nominal: &[u64],
    component_size: (u32, u32),
    info: ComponentInfo,
    output_size: (u32, u32),
    origin: (u32, u32),
) -> Result<Vec<u64>, DecodeError> {
    if output_size.0 == 0 {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ContainerCodestreamMismatch,
        });
    }
    let coordinate = registered_coordinate_wide;
    let x0 = coordinate(origin.0, info.x_subsampling, info.x_registration, true);
    let y0 = coordinate(origin.1, info.y_subsampling, info.y_registration, true);
    let mut result = Vec::new();
    for y in 0..output_size.1 {
        for x in 0..output_size.0 {
            let sx = coordinate(origin.0 + x, info.x_subsampling, info.x_registration, false)
                .clamp(x0, x0 + u128::from(component_size.0) - 1);
            let sy = coordinate(origin.1 + y, info.y_subsampling, info.y_registration, false)
                .clamp(y0, y0 + u128::from(component_size.1) - 1);
            let index =
                usize::try_from((sy - y0) * u128::from(component_size.0) + sx - x0).unwrap();
            result.push(nominal[index]);
        }
    }
    Ok(result)
}

fn sampled_plane_wide_reference(
    nominal: &[u64],
    component_size: (u32, u32),
    info: ComponentInfo,
    output_size: (u32, u32),
    origin: (u32, u32),
) -> Result<Vec<u16>, DecodeError> {
    let plane = sampled_nominal_plane_wide_reference(
        // Preserve the reference call's explicit argument boundaries.
        nominal,
        component_size,
        info,
        output_size,
        origin,
    )?;
    let maximum = (1_u128 << info.precision) - 1;
    Ok(plane
        .into_iter()
        .map(|value| {
            // Preserve the reference's explicit normalization block.
            u16::try_from((u128::from(value) * 65_535 + maximum / 2) / maximum).unwrap()
        })
        .collect())
}

fn chroma_wide_reference(value: u64, precision: u8) -> i32 {
    let midpoint = 1_u64 << (precision - 1);
    let maximum = 2 * midpoint - 1;
    let difference = i128::from(value) - i128::from(midpoint);
    let magnitude =
        (difference.unsigned_abs() * 65_535 + u128::from(maximum / 2)) / u128::from(maximum);
    i32::try_from(magnitude).unwrap() * if difference < 0 { -1 } else { 1 }
}

fn sycc_wide_reference(y: u16, cb: i32, cr: i32) -> (u16, u16, u16) {
    fn round(value: i64) -> i64 {
        let magnitude = (value.unsigned_abs() + 32_768) / 65_536;
        i64::try_from(magnitude).unwrap() * value.signum()
    }
    fn sample(value: i64) -> u16 {
        u16::try_from(value.clamp(0, 65_535)).unwrap()
    }
    let cb = i64::from(cb);
    let cr = i64::from(cr);
    (
        sample(i64::from(y) + round(91_881 * cr)),
        sample(i64::from(y) - round(22_554 * cb) - round(46_802 * cr)),
        sample(i64::from(y) + round(116_130 * cb)),
    )
}

#[test]
fn complete_crop_matches_independent_source_coordinate_masks_and_all_metadata() {
    fn reference(
        input: &ConvertedImage,
        x: u32,
        y: u32,
        width: u32,
        height: u32,
    ) -> Result<ConvertedImage, DecodeError> {
        let invalid = DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ContainerCodestreamMismatch,
        };
        let overflow = DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        };
        if width == 0 || height == 0 {
            return Err(invalid);
        }
        let x1 = u64::from(x) + u64::from(width);
        let y1 = u64::from(y) + u64::from(height);
        if x1 > u64::from(u32::MAX) || y1 > u64::from(u32::MAX) {
            return Err(overflow);
        }
        if x1 > u64::from(input.width) || y1 > u64::from(input.height) {
            return Err(invalid);
        }
        let identity = x == 0 && y == 0 && width == input.width && height == input.height;
        let area = u128::from(width) * u128::from(height);
        if !identity && area > usize::MAX as u128 {
            return Err(overflow);
        }
        let mut channels = Vec::new();
        for channel in &input.channels {
            let samples = if identity {
                channel.samples.clone()
            } else {
                channel
                    .samples
                    .iter()
                    .enumerate()
                    .filter_map(|(index, sample)| {
                        let row = (index as u128) / u128::from(input.width);
                        let column = (index as u128) % u128::from(input.width);
                        (row >= u128::from(y)
                            && row < u128::from(y1)
                            && column >= u128::from(x)
                            && column < u128::from(x1))
                        .then_some(*sample)
                    })
                    .collect::<Vec<_>>()
            };
            if !identity && samples.len() as u128 != area {
                return Err(invalid);
            }
            channels.push(ConvertedChannel {
                channel_type: channel.channel_type,
                samples,
            });
        }
        Ok(ConvertedImage {
            width,
            height,
            color_space: input.color_space,
            precision: input.precision,
            channels,
        })
    }
    let mut cases = 0;
    for (source_width, source_height) in [(0, 2), (1, 1), (3, 2), (4, 3)] {
        let area = usize::try_from(u64::from(source_width) * u64::from(source_height)).unwrap();
        for kinds in [
            vec![],
            vec![ConvertedChannelType::Gray],
            vec![
                ConvertedChannelType::Red,
                ConvertedChannelType::Green,
                ConvertedChannelType::Blue,
            ],
            vec![
                ConvertedChannelType::Gray,
                ConvertedChannelType::Alpha {
                    premultiplied: true,
                    association: ChannelAssociation::Color(3),
                },
            ],
        ] {
            for length in [0, 1, area.saturating_sub(1), area, area + 2] {
                for precision in [0, 16, 255] {
                    for x in 0..=source_width + 1 {
                        for y in 0..=source_height + 1 {
                            for width in 0..=source_width + 1 {
                                for height in 0..=source_height + 1 {
                                    let input = ConvertedImage {
                                        width: source_width,
                                        height: source_height,
                                        color_space: if kinds.len() == 1 {
                                            ConvertedColorSpace::Grayscale
                                        } else {
                                            ConvertedColorSpace::Srgb
                                        },
                                        precision,
                                        channels: kinds
                                            .iter()
                                            .enumerate()
                                            .map(|(role, kind)| ConvertedChannel {
                                                channel_type: *kind,
                                                samples: (0..length)
                                                    .map(|index| {
                                                        u16::try_from(index + role * 67).unwrap()
                                                    })
                                                    .collect(),
                                            })
                                            .collect(),
                                    };
                                    let expected = reference(&input, x, y, width, height);
                                    assert_eq!(input.crop(x, y, width, height), expected);
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 86_700);
}

#[test]
fn crop_identity_and_native_boundary_error_priority_are_exact() {
    let image = || ConvertedImage {
        width: u32::MAX,
        height: u32::MAX,
        color_space: ConvertedColorSpace::Grayscale,
        precision: 255,
        channels: vec![ConvertedChannel {
            channel_type: ConvertedChannelType::Gray,
            samples: vec![],
        }],
    };
    let identity = image().crop(0, 0, u32::MAX, u32::MAX).unwrap();
    assert_eq!(
        (identity.width(), identity.height(), identity.precision()),
        (u32::MAX, u32::MAX, 255)
    );
    assert!(identity.channels()[0].samples().is_empty());
    assert_eq!(
        image().crop(u32::MAX, u32::MAX, 0, 1),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ContainerCodestreamMismatch,
        })
    );
    assert_eq!(
        image().crop(u32::MAX, 0, 1, 1),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        })
    );
    assert_eq!(
        image().crop(0, u32::MAX, 1, 1),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        })
    );
    let partial = ConvertedImage::from_test_channels(
        2,
        2,
        ConvertedColorSpace::Grayscale,
        vec![(ConvertedChannelType::Gray, vec![10, 20])],
    );
    assert_eq!(
        partial.crop(0, 0, 2, 1).unwrap().channels()[0].samples(),
        &[10, 20]
    );
}

#[test]
fn complete_color_conversion_matches_independent_registered_planes_and_metadata() {
    let mut cases = 0;
    for precision in [1, 8, 16, 31, 38] {
        let maximum = (1_u64 << precision) - 1;
        let midpoint = 1_i64 << (precision - 1);
        for signed in [false, true] {
            for method in [ENUMERATED_GRAYSCALE, ENUMERATED_SRGB, ENUMERATED_SYCC] {
                let color_count = if method == ENUMERATED_GRAYSCALE { 1 } else { 3 };
                for size in [(3, 2), (5, 3)] {
                    for (origin, registration) in [
                        ((0, 0), (0, 0)),
                        ((0, 0), (32_768, 65_535)),
                        ((3, 5), (0, 0)),
                        ((3, 5), (32_768, 65_535)),
                    ] {
                        for alpha_mode in 0..3 {
                            for reverse in [false, true] {
                                let mut components = Vec::new();
                                let mut raw_planes = Vec::new();
                                let mut normalized_planes = Vec::new();
                                for role in 0..color_count + usize::from(alpha_mode != 0) {
                                    let info = ComponentInfo {
                                        precision,
                                        signed,
                                        x_subsampling: if role == 0 { 1 } else { 2 },
                                        y_subsampling: 1,
                                        x_registration: registration.0,
                                        y_registration: registration.1,
                                    };
                                    let width = u32::try_from(
                                        registered_coordinate_wide(
                                            origin.0 + size.0,
                                            info.x_subsampling,
                                            registration.0,
                                            true,
                                        ) - registered_coordinate_wide(
                                            origin.0,
                                            info.x_subsampling,
                                            registration.0,
                                            true,
                                        ),
                                    )
                                    .unwrap();
                                    let height = u32::try_from(
                                        registered_coordinate_wide(
                                            origin.1 + size.1,
                                            info.y_subsampling,
                                            registration.1,
                                            true,
                                        ) - registered_coordinate_wide(
                                            origin.1,
                                            info.y_subsampling,
                                            registration.1,
                                            true,
                                        ),
                                    )
                                    .unwrap();
                                    let nominal: Vec<u64> = (0..u64::from(width)
                                        * u64::from(height))
                                        .map(|index| {
                                            u64::try_from(
                                                ((u128::from(index) * 977
                                                    + (role as u128) * 113
                                                    + 1)
                                                    * u128::from(maximum)
                                                    / 13)
                                                    % (u128::from(maximum) + 1),
                                            )
                                            .unwrap()
                                        })
                                        .collect();
                                    raw_planes.push(
                                        sampled_nominal_plane_wide_reference(
                                            &nominal,
                                            (width, height),
                                            info,
                                            size,
                                            origin,
                                        )
                                        .unwrap(),
                                    );
                                    normalized_planes.push(
                                        sampled_plane_wide_reference(
                                            &nominal,
                                            (width, height),
                                            info,
                                            size,
                                            origin,
                                        )
                                        .unwrap(),
                                    );
                                    let samples = if signed {
                                        TypedSamples::Signed(
                                            nominal
                                                .iter()
                                                .map(|value| {
                                                    i64::try_from(*value).unwrap() - midpoint
                                                })
                                                .collect(),
                                        )
                                    } else {
                                        TypedSamples::Unsigned(nominal)
                                    };
                                    let mut component = TypedComponent::from_parts(
                                        // Preserve the reference call's explicit argument boundaries.
                                        width, height, info, samples,
                                    );
                                    let definition = if role < color_count {
                                        ChannelDefinition::new(
                                            ChannelType::Color,
                                            ChannelAssociation::Color(
                                                u16::try_from(role + 1).unwrap(),
                                            ),
                                        )
                                    } else if alpha_mode == 1 {
                                        ChannelDefinition::new(
                                            ChannelType::Opacity,
                                            ChannelAssociation::WholeImage,
                                        )
                                    } else {
                                        ChannelDefinition::new(
                                            ChannelType::PremultipliedOpacity,
                                            ChannelAssociation::Color(1),
                                        )
                                    };
                                    component.add_channel_definition(definition);
                                    components.push(component);
                                }
                                if reverse {
                                    components.reverse();
                                }
                                let image = TypedImage::from_components_with_origin(
                                    size.0,
                                    size.1,
                                    origin.0,
                                    origin.1,
                                    components,
                                    &ResourceLimits::default(),
                                )
                                .unwrap();
                                let converted = convert_jp2_color(
                                    &image,
                                    &ColorSpecification::enumerated(method),
                                    &ResourceLimits::default(),
                                )
                                .unwrap();
                                let color_planes = if method == ENUMERATED_SYCC {
                                    let mut planes = vec![Vec::new(), Vec::new(), Vec::new()];
                                    for ((y, cb), cr) in normalized_planes[0]
                                        .iter()
                                        .zip(&raw_planes[1])
                                        .zip(&raw_planes[2])
                                    {
                                        let (r, g, b) = sycc_wide_reference(
                                            *y,
                                            chroma_wide_reference(*cb, precision),
                                            chroma_wide_reference(*cr, precision),
                                        );
                                        planes[0].push(r);
                                        planes[1].push(g);
                                        planes[2].push(b);
                                    }
                                    planes
                                } else {
                                    normalized_planes[..color_count].to_vec()
                                };
                                let mut expected: Vec<_> = color_planes
                                    .into_iter()
                                    .enumerate()
                                    .map(|(index, samples)| {
                                        let kind = match (color_count, index) {
                                            (1, 0) => ConvertedChannelType::Gray,
                                            (3, 0) => ConvertedChannelType::Red,
                                            (3, 1) => ConvertedChannelType::Green,
                                            (3, 2) => ConvertedChannelType::Blue,
                                            _ => unreachable!(),
                                        };
                                        (kind, samples)
                                    })
                                    .collect();
                                if alpha_mode != 0 {
                                    expected.push((
                                        ConvertedChannelType::Alpha {
                                            premultiplied: alpha_mode == 2,
                                            association: if alpha_mode == 1 {
                                                ChannelAssociation::WholeImage
                                            } else {
                                                ChannelAssociation::Color(1)
                                            },
                                        },
                                        normalized_planes[color_count].clone(),
                                    ));
                                }
                                assert_eq!(
                                    (converted.width(), converted.height(), converted.precision()),
                                    (size.0, size.1, 16)
                                );
                                assert_eq!(
                                    converted.color_space(),
                                    if color_count == 1 {
                                        ConvertedColorSpace::Grayscale
                                    } else {
                                        ConvertedColorSpace::Srgb
                                    }
                                );
                                assert_eq!(
                                    converted
                                        .channels()
                                        .iter()
                                        .map(|channel| (
                                            channel.channel_type(),
                                            channel.samples().to_vec()
                                        ))
                                        .collect::<Vec<_>>(),
                                    expected
                                );
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 1_440);
}

#[test]
fn complete_color_admission_matches_wide_checked_count_and_limit_model() {
    let overflow = Err(DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    });
    let mut cases = 0;
    for (width, height) in [(0, 0), (1, 1), (3, 2), (u32::MAX, 1), (u32::MAX, u32::MAX)] {
        let image =
            TypedImage::from_components(width, height, Vec::new(), &ResourceLimits::default())
                .unwrap();
        for colors in [0, 1, 3, usize::MAX] {
            for alphas in [0, 1, usize::MAX] {
                for (byte_limit, work_limit) in [(0, 0), (2, 1), (24, 12)] {
                    let limits = ResourceLimits::default()
                        .with_maximum_decoded_bytes(byte_limit)
                        .unwrap()
                        .with_maximum_work_units(work_limit)
                        .unwrap();
                    let channels = (colors as u128) + alphas as u128;
                    let area = u128::from(width) * u128::from(height);
                    let expected = if channels > usize::MAX as u128 || area > usize::MAX as u128 {
                        overflow
                    } else {
                        let samples = channels * area;
                        if samples > usize::MAX as u128 {
                            overflow
                        } else {
                            let bytes = samples * 2;
                            if bytes > u128::from(u64::MAX) {
                                overflow
                            } else if bytes > u128::from(byte_limit) {
                                Err(DecodeError::LimitExceeded {
                                    resource: Resource::DecodedBytes,
                                    limit: byte_limit,
                                    actual: u64::try_from(bytes).unwrap(),
                                })
                            } else if samples > u128::from(work_limit) {
                                Err(DecodeError::LimitExceeded {
                                    resource: Resource::WorkUnits,
                                    limit: work_limit,
                                    actual: u64::try_from(samples).unwrap(),
                                })
                            } else {
                                Ok(())
                            }
                        }
                    };
                    assert_eq!(
                        validate_output_size(&image, colors, alphas, &limits),
                        expected
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 180);
}

#[test]
fn complete_color_conversion_preserves_format_metadata_budget_and_sample_error_priority() {
    let gray = ColorSpecification::enumerated(ENUMERATED_GRAYSCALE);
    let invalid = Err(DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ContainerCodestreamMismatch,
    });
    let empty = image(0, Vec::new());
    assert_eq!(
        convert_jp2_color(
            &empty,
            &ColorSpecification::enumerated(99),
            &ResourceLimits::default()
        ),
        invalid
    );
    let bad_sample = image(1, vec![component(&[256], 8, false, (1, 1), None)]);
    let limits = ResourceLimits::default()
        .with_maximum_decoded_bytes(1)
        .unwrap()
        .with_maximum_work_units(0)
        .unwrap();
    assert_eq!(
        convert_jp2_color(&bad_sample, &gray, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: 1,
            actual: 2,
        })
    );
    let limits = ResourceLimits::default()
        .with_maximum_decoded_bytes(2)
        .unwrap()
        .with_maximum_work_units(0)
        .unwrap();
    assert_eq!(
        convert_jp2_color(&bad_sample, &gray, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 0,
            actual: 1,
        })
    );
    assert_eq!(
        convert_jp2_color(&bad_sample, &gray, &ResourceLimits::default()),
        invalid
    );
    let bad_metadata = image(1, vec![component(&[0], 0, false, (1, 1), None)]);
    assert_eq!(convert_jp2_color(&bad_metadata, &gray, &limits), invalid);
    let bad_definition = image(
        1,
        vec![component(
            &[0],
            0,
            false,
            (1, 1),
            Some(ChannelDefinition::new(
                ChannelType::Opacity,
                ChannelAssociation::Color(0),
            )),
        )],
    );
    assert_eq!(
        convert_jp2_color(&bad_definition, &gray, &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidAlphaAssociation,
        })
    );
    assert_eq!(
        convert_jp2_color(
            &bad_definition,
            &ColorSpecification::enumerated(99),
            &limits
        ),
        Err(DecodeError::UnsupportedColorConversion {
            reason: UnsupportedColorConversion::EnumeratedColorSpace
        })
    );
    let mut icc = ColorSpecification::enumerated(ENUMERATED_GRAYSCALE);
    icc.method = ColorMethod::RestrictedIcc { profile_bytes: 0 };
    assert_eq!(
        convert_jp2_color(&bad_definition, &icc, &limits),
        Err(DecodeError::UnsupportedColorConversion {
            reason: UnsupportedColorConversion::IccProfile
        })
    );
}

#[test]
fn complete_normalized_component_planes_match_wide_registered_reference() {
    let mut cases = 0;
    for precision in [1, 2, 7, 8, 12, 16, 24, 31, 38] {
        let maximum = (1_u64 << precision) - 1;
        for signed in [false, true] {
            for sampling in [(1, 1), (2, 1), (1, 2), (2, 3)] {
                for origin in [(0, 0), (1, 3), (3, 5), (7, 2)] {
                    for registration in [(0, 0), (1, 65_535), (32_768, 12_345), (65_535, 32_768)] {
                        for size in [(1_u32, 1_u32), (3, 2)] {
                            let nominal = (0..size.0 * size.1)
                                .map(|i| match i {
                                    0 => 0,
                                    1 => maximum,
                                    2 => maximum / 2,
                                    _ => (u64::from(i) * 17 + 1) % (maximum + 1),
                                })
                                .collect::<Vec<_>>();
                            let info = ComponentInfo {
                                precision,
                                signed,
                                x_subsampling: sampling.0,
                                y_subsampling: sampling.1,
                                x_registration: registration.0,
                                y_registration: registration.1,
                            };
                            let samples = if signed {
                                let level = 1_i64 << (precision - 1);
                                TypedSamples::Signed(
                                    nominal
                                        .iter()
                                        .map(|&value| i64::try_from(value).unwrap() - level)
                                        .collect(),
                                )
                            } else {
                                TypedSamples::Unsigned(nominal.clone())
                            };
                            let input = TypedComponent::from_parts(size.0, size.1, info, samples);
                            for output in [(1, 1), (5, 4), (0, 3), (4, 0)] {
                                let expected = sampled_plane_wide_reference(
                                    &nominal, size, info, output, origin,
                                );
                                assert_eq!(
                                    normalize_component(
                                        &input, output.0, output.1, origin.0, origin.1
                                    ),
                                    expected,
                                    "precision={precision} signed={signed} sampling={sampling:?} origin={origin:?} registration={registration:?} size={size:?} output={output:?}",
                                );
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 9_216);
}

#[test]
fn registered_coordinates_match_wide_full_domain_boundaries() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ContainerCodestreamMismatch,
    };
    for value in [0, 1, 2, u32::MAX / 2, u32::MAX] {
        for divisor in [0, 1, 2, 255, 65_536, u32::MAX] {
            for registration in [0, 1, 32_768, u16::MAX] {
                let reference = |ceil: bool| {
                    if divisor == 0 {
                        return Err(invalid);
                    }
                    let phase =
                        u128::from(registration) * if ceil { 1 } else { u128::from(divisor) };
                    let numerator = (u128::from(value) * 65_536).saturating_sub(phase);
                    let denominator = u128::from(divisor) * 65_536;
                    let quotient = if ceil {
                        numerator.div_ceil(denominator)
                    } else {
                        numerator / denominator
                    };
                    Ok(u32::try_from(quotient).unwrap())
                };
                assert_eq!(
                    registered_ceil_div(value, divisor, registration),
                    reference(true)
                );
                assert_eq!(
                    registered_floor_div(value, divisor, registration),
                    reference(false)
                );
            }
        }
    }
}

#[test]
fn normalized_component_rejects_every_invalid_stage_input_in_order() {
    let invalid = Err(DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ContainerCodestreamMismatch,
    });
    let arithmetic = Err(DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    });
    let info = ComponentInfo {
        precision: 8,
        signed: false,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    for bad_info in [
        ComponentInfo {
            precision: 0,
            ..info
        },
        ComponentInfo {
            precision: 39,
            ..info
        },
        ComponentInfo {
            precision: u8::MAX,
            ..info
        },
        ComponentInfo {
            x_subsampling: 0,
            ..info
        },
        ComponentInfo {
            y_subsampling: 0,
            ..info
        },
    ] {
        let input = TypedComponent::from_parts(1, 1, bad_info, TypedSamples::Unsigned(vec![0]));
        assert_eq!(
            normalize_component(&input, 1, 1, u32::MAX, u32::MAX),
            invalid
        );
    }
    for size in [(0, 1), (1, 0)] {
        let input =
            TypedComponent::from_parts(size.0, size.1, info, TypedSamples::Unsigned(vec![]));
        assert_eq!(normalize_component(&input, 1, 1, 0, 0), invalid);
    }
    let wrong_tag = TypedComponent::from_parts(1, 1, info, TypedSamples::Signed(vec![0]));
    assert_eq!(normalize_component(&wrong_tag, 1, 1, 0, 0), invalid);
    let wrong_signed = TypedComponent::from_parts(
        1,
        1,
        ComponentInfo {
            signed: true,
            ..info
        },
        TypedSamples::Unsigned(vec![0]),
    );
    assert_eq!(normalize_component(&wrong_signed, 1, 1, 0, 0), invalid);
    for samples in [
        TypedSamples::Unsigned(vec![256]),
        TypedSamples::Unsigned(vec![]),
    ] {
        let input = TypedComponent::from_parts(1, 1, info, samples);
        assert_eq!(normalize_component(&input, 1, 1, 0, 0), invalid);
    }
    for value in [-129, 128] {
        let input = TypedComponent::from_parts(
            1,
            1,
            ComponentInfo {
                signed: true,
                ..info
            },
            TypedSamples::Signed(vec![value]),
        );
        assert_eq!(normalize_component(&input, 1, 1, 0, 0), invalid);
    }
    let short = TypedComponent::from_parts(3, 2, info, TypedSamples::Unsigned(vec![0; 5]));
    assert_eq!(normalize_component(&short, 3, 2, 0, 0), invalid);
    let extra = TypedComponent::from_parts(3, 2, info, TypedSamples::Unsigned(vec![0; 7]));
    assert_eq!(normalize_component(&extra, 3, 2, 0, 0), Ok(vec![0; 6]));
    let outside = TypedComponent::from_parts(1, 1, info, TypedSamples::Unsigned(vec![0]));
    assert_eq!(normalize_component(&outside, 1, 1, u32::MAX, 0), arithmetic);
    let late_origin_overflow = TypedComponent::from_parts(
        1,
        1,
        ComponentInfo {
            x_subsampling: 255,
            ..info
        },
        TypedSamples::Unsigned(vec![0]),
    );
    assert_eq!(
        normalize_component(&late_origin_overflow, 2, 1, u32::MAX, 0),
        arithmetic
    );
    let empty = TypedComponent::from_parts(
        0,
        0,
        ComponentInfo {
            precision: 0,
            x_subsampling: 0,
            ..info
        },
        TypedSamples::Unsigned(vec![]),
    );
    assert_eq!(normalize_component(&empty, 0, 0, 0, 0), invalid);
    assert_eq!(
        normalize_component(&empty, 1, 0, u32::MAX, u32::MAX),
        Ok(vec![])
    );
}

type LayoutMapResult = Result<(Vec<usize>, Vec<(usize, bool, ChannelAssociation)>), DecodeError>;

fn layout_map_reference(
    definitions: &[Vec<(ChannelType, ChannelAssociation)>],
    count: usize,
) -> LayoutMapResult {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidChannelLayout,
    };
    if definitions.iter().all(Vec::is_empty) {
        return if definitions.len() == count {
            Ok(((0..count).collect(), vec![]))
        } else {
            Err(invalid)
        };
    }
    let mut colors = std::collections::BTreeMap::new();
    let mut alphas = Vec::new();
    let flattened = definitions
        .iter()
        .enumerate()
        .flat_map(|(index, entries)| entries.iter().map(move |&entry| (index, entry)))
        .collect::<Vec<_>>();
    for (component, (kind, association)) in flattened {
        match kind {
            ChannelType::Color => {
                let ChannelAssociation::Color(color) = association else {
                    return Err(invalid);
                };
                if color == 0 || usize::from(color) > count {
                    return Err(invalid);
                }
                if let Some(previous) = colors.insert(color, component)
                    && previous != component
                {
                    return Err(invalid);
                }
            }
            ChannelType::Opacity | ChannelType::PremultipliedOpacity => {
                if matches!(association, ChannelAssociation::Color(color)
                        if color == 0 || usize::from(color) > count)
                {
                    return Err(DecodeError::MalformedInput {
                        offset: 0,
                        kind: MalformedKind::InvalidAlphaAssociation,
                    });
                }
                alphas.push((
                    component,
                    kind == ChannelType::PremultipliedOpacity,
                    association,
                ));
            }
            ChannelType::Unspecified => {}
        }
    }
    let mut ordered = Vec::new();
    for color in 1..=count {
        let index = colors.get(&u16::try_from(color).unwrap()).ok_or(invalid)?;
        ordered.push(*index);
    }
    Ok((ordered, alphas))
}

fn layout_test_image(definitions: &[Vec<(ChannelType, ChannelAssociation)>]) -> TypedImage {
    let components = definitions
        .iter()
        .enumerate()
        .map(|(index, entries)| {
            let mut input = TypedComponent::from_parts(
                1,
                1,
                ComponentInfo {
                    precision: 8,
                    signed: false,
                    x_subsampling: 1,
                    y_subsampling: 1,
                    x_registration: 0,
                    y_registration: 0,
                },
                TypedSamples::Unsigned(vec![u64::try_from(index).unwrap()]),
            );
            for &(kind, association) in entries {
                input.add_channel_definition(ChannelDefinition::new(kind, association));
            }
            input
        })
        .collect();
    TypedImage::from_components(1, 1, components, &ResourceLimits::default()).unwrap()
}

#[test]
fn complete_channel_layout_matches_independent_flat_map_metadata_model() {
    let options = [
        None,
        Some((ChannelType::Color, ChannelAssociation::Color(0))),
        Some((ChannelType::Color, ChannelAssociation::Color(1))),
        Some((ChannelType::Color, ChannelAssociation::Color(2))),
        Some((ChannelType::Color, ChannelAssociation::Color(3))),
        Some((ChannelType::Color, ChannelAssociation::Color(4))),
        Some((ChannelType::Color, ChannelAssociation::WholeImage)),
        Some((ChannelType::Color, ChannelAssociation::Unassociated)),
        Some((ChannelType::Opacity, ChannelAssociation::WholeImage)),
        Some((ChannelType::Opacity, ChannelAssociation::Color(0))),
        Some((ChannelType::Opacity, ChannelAssociation::Color(1))),
        Some((ChannelType::Opacity, ChannelAssociation::Color(4))),
        Some((
            ChannelType::PremultipliedOpacity,
            ChannelAssociation::WholeImage,
        )),
        Some((
            ChannelType::PremultipliedOpacity,
            ChannelAssociation::Color(2),
        )),
        Some((ChannelType::Unspecified, ChannelAssociation::Color(0))),
    ];
    let mut cases = 0;
    for components in 1..=3_u32 {
        for mut word in 0..options.len().pow(components) {
            let mut definitions = Vec::new();
            for _ in 0..components {
                definitions.push(
                    options[word % options.len()]
                        .into_iter()
                        .collect::<Vec<_>>(),
                );
                word /= options.len();
            }
            let image = layout_test_image(&definitions);
            for count in 0..=3 {
                let actual =
                    channel_layout(&image, count).map(|layout| (layout.colors, layout.alphas));
                assert_eq!(actual, layout_map_reference(&definitions, count));
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 14_460);
}

#[test]
fn channel_layout_duplicates_and_first_metadata_error_preserve_order() {
    use ChannelAssociation::{Color, Unassociated, WholeImage};
    use ChannelType::{Color as ColorKind, Opacity, PremultipliedOpacity, Unspecified};
    let cases = [
        vec![
            vec![(ColorKind, Color(1)), (ColorKind, Color(1))],
            vec![(Opacity, WholeImage)],
        ],
        vec![
            vec![(ColorKind, Color(1)), (ColorKind, Color(2))],
            vec![(ColorKind, Color(3))],
        ],
        vec![
            vec![(ColorKind, Color(1))],
            vec![(Opacity, Color(0))],
            vec![(ColorKind, Color(1))],
        ],
        vec![
            vec![(ColorKind, Color(1))],
            vec![(ColorKind, Color(1))],
            vec![(Opacity, Color(0))],
        ],
        vec![
            vec![(Unspecified, Unassociated)],
            vec![(Opacity, WholeImage)],
        ],
        vec![vec![
            (ColorKind, Color(1)),
            (PremultipliedOpacity, Color(1)),
            (PremultipliedOpacity, Color(1)),
        ]],
    ];
    for definitions in cases {
        let image = layout_test_image(&definitions);
        for count in 0..=3 {
            assert_eq!(
                channel_layout(&image, count).map(|layout| (layout.colors, layout.alphas)),
                layout_map_reference(&definitions, count),
            );
        }
    }
}

#[test]
fn fixed_rounding_matches_unsigned_magnitude_reference_at_native_boundaries() {
    let values = [
        i128::MIN,
        i128::MIN + 32_767,
        i128::MIN + 32_768,
        i128::MIN + 32_769,
        -98_305,
        -98_304,
        -98_303,
        -65_536,
        -32_769,
        -32_768,
        -32_767,
        -1,
        0,
        1,
        32_767,
        32_768,
        32_769,
        65_536,
        98_303,
        98_304,
        98_305,
        i128::MAX - 32_769,
        i128::MAX - 32_768,
        i128::MAX - 32_767,
        i128::MAX,
    ];
    for value in values {
        let magnitude = value.unsigned_abs() + 32_768;
        let bound = if value < 0 {
            1_u128 << 127
        } else {
            i128::MAX as u128
        };
        let expected = if magnitude > bound {
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::ArithmeticOverflow,
            })
        } else {
            let rounded = i128::try_from(magnitude / 65_536).unwrap();
            Ok(if value < 0 { -rounded } else { rounded })
        };
        assert_eq!(rounded_fixed(value), expected, "{value}");
    }
    assert_eq!(rounded_fixed(-32_768), Ok(-1));
    assert_eq!(rounded_fixed(32_768), Ok(1));
}

#[test]
fn chroma_normalization_matches_wide_signed_ratio_for_every_supported_precision() {
    let mut cases = 0;
    for precision in 1..=38 {
        let midpoint = 1_u64 << (precision - 1);
        let maximum = 2 * midpoint - 1;
        for signed in [false, true] {
            for value in [0, midpoint - 1, midpoint, maximum] {
                let input = if signed {
                    signed_component(
                        &[i64::try_from(value).unwrap() - i64::try_from(midpoint).unwrap()],
                        precision,
                        (1, 1),
                        None,
                    )
                } else {
                    component(&[value], precision, false, (1, 1), None)
                };
                let image = image(1, vec![input]);
                let expected = chroma_wide_reference(value, precision);
                assert_eq!(normalized_difference_at(&image, 0, 0, 0), Ok(expected));
                let normalized =
                    (u128::from(value) * 65_535 + u128::from(maximum / 2)) / u128::from(maximum);
                assert_eq!(
                    normalized_at(&image, 0, 0, 0),
                    Ok(u16::try_from(normalized).unwrap()),
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 304);
}

#[test]
fn chroma_sampling_preserves_typed_input_and_coordinate_error_order() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ContainerCodestreamMismatch,
    };
    for precision in [0, 39, 255] {
        let input = image(1, vec![component(&[0], precision, false, (0, 0), None)]);
        assert_eq!(
            normalized_difference_at(&input, 0, u32::MAX, u32::MAX),
            Err(invalid)
        );
    }
    for input in [
        component(&[256], 8, false, (1, 1), None),
        TypedComponent::from_parts(
            1,
            1,
            ComponentInfo {
                precision: 8,
                signed: true,
                x_subsampling: 1,
                y_subsampling: 1,
                x_registration: 0,
                y_registration: 0,
            },
            TypedSamples::Unsigned(vec![0]),
        ),
        signed_component(&[-129], 8, (1, 1), None),
        signed_component(&[128], 8, (1, 1), None),
    ] {
        assert_eq!(
            normalized_difference_at(&image(1, vec![input]), 0, 0, 0),
            Err(invalid)
        );
    }
    let input = TypedImage::from_components_with_origin(
        1,
        1,
        u32::MAX - 1,
        0,
        vec![component(&[0], 8, false, (1, 1), None)],
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(normalized_difference_at(&input, 1, 2, 0), Err(invalid));
    assert_eq!(
        normalized_difference_at(&input, 0, 2, 0),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        }),
    );
}

#[test]
fn sycc_conversion_matches_independent_wide_integer_reference() {
    let differences = [
        i32::MIN,
        i32::MIN + 1,
        -65_536,
        -65_535,
        -32_768,
        -1,
        0,
        1,
        32_767,
        32_768,
        65_534,
        65_535,
        65_536,
        i32::MAX - 1,
        i32::MAX,
    ];
    let mut cases = 0;
    for y in [0, 1, 32_767, 32_768, 65_534, 65_535_u16] {
        for cb in differences {
            for cr in differences {
                let expected = sycc_wide_reference(y, cb, cr);
                assert_eq!(sycc_to_srgb(y, cb, cr), Ok(expected),);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 1_350);
}

fn component(
    samples: &[u64],
    precision: u8,
    signed: bool,
    subsampling: (u8, u8),
    definition: Option<ChannelDefinition>,
) -> TypedComponent {
    let mut component = TypedComponent::from_parts(
        u32::try_from(samples.len()).unwrap(),
        1,
        ComponentInfo {
            precision,
            signed,
            x_subsampling: subsampling.0,
            y_subsampling: subsampling.1,
            x_registration: 0,
            y_registration: 0,
        },
        if signed {
            TypedSamples::Signed(samples.iter().map(|value| *value as i64).collect())
        } else {
            TypedSamples::Unsigned(samples.to_vec())
        },
    );
    if let Some(definition) = definition {
        component.add_channel_definition(definition);
    }
    component
}

fn color(association: u16) -> ChannelDefinition {
    ChannelDefinition::new(ChannelType::Color, ChannelAssociation::Color(association))
}

fn image(width: u32, components: Vec<TypedComponent>) -> TypedImage {
    TypedImage::from_components(width, 1, components, &ResourceLimits::default()).unwrap()
}

fn signed_component(
    samples: &[i64],
    precision: u8,
    subsampling: (u8, u8),
    definition: Option<ChannelDefinition>,
) -> TypedComponent {
    let mut component = TypedComponent::from_parts(
        u32::try_from(samples.len()).unwrap(),
        1,
        ComponentInfo {
            precision,
            signed: true,
            x_subsampling: subsampling.0,
            y_subsampling: subsampling.1,
            x_registration: 0,
            y_registration: 0,
        },
        TypedSamples::Signed(samples.to_vec()),
    );
    if let Some(definition) = definition {
        component.add_channel_definition(definition);
    }
    component
}

#[test]
fn registration_offset_changes_component_sample_location() {
    let registered = TypedComponent::from_parts(
        2,
        1,
        ComponentInfo {
            precision: 8,
            signed: false,
            x_subsampling: 2,
            y_subsampling: 1,
            x_registration: 32_768,
            y_registration: 0,
        },
        TypedSamples::Unsigned(vec![10, 20]),
    );
    assert_eq!(nominal_component_at(&registered, 0, 0, 2, 0).unwrap(), 10);
    assert_eq!(nominal_component_at(&registered, 0, 0, 3, 0).unwrap(), 20);
}

#[test]
fn srgb_reorders_associated_channels_and_preserves_alpha() {
    let alpha = component(
        &[0, 255],
        8,
        false,
        (1, 1),
        Some(ChannelDefinition::new(
            ChannelType::PremultipliedOpacity,
            ChannelAssociation::WholeImage,
        )),
    );
    let blue = component(&[255, 0], 8, false, (1, 1), Some(color(3)));
    let red = component(&[0, 255], 8, false, (1, 1), Some(color(1)));
    let green = component(&[128, 64], 8, false, (1, 1), Some(color(2)));
    let converted = convert_jp2_color(
        &image(2, vec![alpha, blue, red, green]),
        &ColorSpecification::enumerated(ENUMERATED_SRGB),
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(converted.color_space(), ConvertedColorSpace::Srgb);
    assert_eq!(converted.precision(), 16);
    assert_eq!(converted.channel(0).unwrap().samples(), &[0, 65_535]);
    assert_eq!(converted.channel(1).unwrap().samples(), &[32_896, 16_448]);
    assert_eq!(converted.channel(2).unwrap().samples(), &[65_535, 0]);
    assert_eq!(converted.channel(3).unwrap().samples(), &[0, 65_535]);
    assert_eq!(
        converted.channel(3).unwrap().channel_type(),
        ConvertedChannelType::Alpha {
            premultiplied: true,
            association: ChannelAssociation::WholeImage,
        }
    );
}

#[test]
fn grayscale_scales_full_declared_range() {
    let converted = convert_jp2_color(
        &image(2, vec![component(&[0, 1], 1, false, (1, 1), None)]),
        &ColorSpecification::enumerated(ENUMERATED_GRAYSCALE),
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(converted.color_space(), ConvertedColorSpace::Grayscale);
    assert_eq!(converted.channel(0).unwrap().samples(), &[0, 65_535]);
}

#[test]
fn sycc_neutral_chroma_is_deterministic_srgb() {
    let converted = convert_jp2_color(
        &image(
            3,
            vec![
                component(&[0, 128, 255], 8, false, (1, 1), None),
                component(&[128, 128, 128], 8, false, (1, 1), None),
                component(&[128, 128, 128], 8, false, (1, 1), None),
            ],
        ),
        &ColorSpecification::enumerated(ENUMERATED_SYCC),
        &ResourceLimits::default(),
    )
    .unwrap();
    for channel in converted.channels() {
        assert_eq!(channel.samples(), &[0, 32_896, 65_535]);
    }
}

#[test]
fn normalized_plane_constructor_preserves_all_metadata_and_rejects_each_shape_fault() {
    for space in [ConvertedColorSpace::Grayscale, ConvertedColorSpace::Srgb] {
        let kinds: &[ConvertedChannelType] = match space {
            ConvertedColorSpace::Grayscale => &[ConvertedChannelType::Gray],
            ConvertedColorSpace::Srgb => &[
                ConvertedChannelType::Red,
                ConvertedChannelType::Green,
                ConvertedChannelType::Blue,
            ],
        };
        for premultiplied in [false, true] {
            for (width, height) in [(0, 2), (2, 0), (2, 1)] {
                let pixels = width as usize * height as usize;
                let colors: Vec<Vec<u16>> = (0..kinds.len())
                    .map(|channel| {
                        (0..pixels)
                            .map(|pixel| (100 * channel + pixel) as u16)
                            .collect()
                    })
                    .collect();
                let alpha: Vec<u16> = (0..pixels).map(|pixel| 32_768 + pixel as u16).collect();
                let image = from_layer(
                    width,
                    height,
                    space,
                    colors.clone(),
                    alpha.clone(),
                    premultiplied,
                )
                .unwrap();
                assert_eq!(
                    (
                        image.width(),
                        image.height(),
                        image.color_space(),
                        image.precision()
                    ),
                    (width, height, space, 16)
                );
                assert_eq!(image.channels().len(), kinds.len() + 1);
                for (index, kind) in kinds.iter().enumerate() {
                    assert_eq!(image.channel(index as u16).unwrap().channel_type(), *kind);
                    assert_eq!(
                        image.channel(index as u16).unwrap().samples(),
                        colors[index]
                    );
                }
                assert_eq!(
                    image.channel(kinds.len() as u16).unwrap().channel_type(),
                    ConvertedChannelType::Alpha {
                        premultiplied,
                        association: ChannelAssociation::WholeImage,
                    }
                );
                assert_eq!(image.channel(kinds.len() as u16).unwrap().samples(), alpha);
                let mut wrong_colors = colors.clone();
                wrong_colors.push(vec![0; pixels]);
                assert_eq!(
                    from_layer(
                        width,
                        height,
                        space,
                        wrong_colors,
                        alpha.clone(),
                        premultiplied
                    )
                    .err(),
                    Some(invalid_color_input())
                );
                assert_eq!(
                    from_layer(
                        width,
                        height,
                        space,
                        colors.clone(),
                        vec![0; pixels + 1],
                        premultiplied
                    )
                    .err(),
                    Some(invalid_color_input())
                );
                for index in 0..kinds.len() {
                    let mut wrong_colors = colors.clone();
                    wrong_colors[index].push(0);
                    assert_eq!(
                        from_layer(
                            width,
                            height,
                            space,
                            wrong_colors,
                            alpha.clone(),
                            premultiplied
                        )
                        .err(),
                        Some(invalid_color_input())
                    );
                }
            }
        }
    }
}

#[test]
fn converted_crop_preserves_color_and_alpha_metadata_and_checks_bounds() {
    let make_image = || {
        from_composited(
            3,
            2,
            ConvertedColorSpace::Srgb,
            vec![
                vec![0, 1, 2, 3, 4, 5],
                vec![10, 11, 12, 13, 14, 15],
                vec![20, 21, 22, 23, 24, 25],
            ],
            vec![0, 100, 200, 300, 400, 500],
        )
        .unwrap()
    };
    let cropped = make_image().crop(1, 0, 2, 2).unwrap();
    assert_eq!(
        (cropped.width(), cropped.height(), cropped.precision()),
        (2, 2, 16)
    );
    assert_eq!(cropped.color_space(), ConvertedColorSpace::Srgb);
    assert_eq!(cropped.channel(0).unwrap().samples(), &[1, 2, 4, 5]);
    assert_eq!(cropped.channel(3).unwrap().samples(), &[100, 200, 400, 500]);
    assert_eq!(
        cropped.channel(0).unwrap().channel_type(),
        ConvertedChannelType::Red
    );
    assert_eq!(
        cropped.channel(3).unwrap().channel_type(),
        ConvertedChannelType::Alpha {
            premultiplied: false,
            association: ChannelAssociation::WholeImage,
        }
    );
    assert_eq!(make_image().crop(0, 0, 3, 2).unwrap(), make_image());
    for (x, y, width, height) in [
        (0, 0, 0, 1),
        (3, 0, 1, 1),
        (0, 2, 1, 1),
        (u32::MAX, 0, 1, 1),
    ] {
        assert!(make_image().crop(x, y, width, height).is_err());
    }
}

#[test]
fn signed_subsampled_sycc_and_alpha_resample_to_image_grid() {
    let alpha = signed_component(
        &[-128, 127],
        8,
        (2, 1),
        Some(ChannelDefinition::new(
            ChannelType::Opacity,
            ChannelAssociation::WholeImage,
        )),
    );
    let converted = convert_jp2_color(
        &image(
            4,
            vec![
                signed_component(&[-128, -43, 42, 127], 8, (1, 1), Some(color(1))),
                signed_component(&[-128, 127], 8, (2, 1), Some(color(2))),
                signed_component(&[0, 0], 8, (2, 1), Some(color(3))),
                alpha,
            ],
        ),
        &ColorSpecification::enumerated(ENUMERATED_SYCC),
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(converted.channels().len(), 4);
    assert_eq!(converted.channel(0).unwrap().samples().len(), 4);
    assert_eq!(converted.channel(1).unwrap().samples().len(), 4);
    assert_eq!(converted.channel(2).unwrap().samples().len(), 4);
    assert_eq!(
        converted.channel(3).unwrap().samples(),
        &[0, 0, 65_535, 65_535]
    );
}

#[test]
fn subsampling_respects_nonzero_image_origin() {
    let image = TypedImage::from_components_with_origin(
        4,
        1,
        1,
        0,
        vec![component(&[0, 255], 8, false, (2, 1), None)],
        &ResourceLimits::default(),
    )
    .unwrap();
    let converted = convert_jp2_color(
        &image,
        &ColorSpecification::enumerated(ENUMERATED_GRAYSCALE),
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(converted.channel(0).unwrap().samples(), &[0, 0, 0, 65_535]);
}

#[test]
fn conversion_validates_alpha_association_samples_and_output_bound() {
    let invalid_alpha = component(
        &[255],
        8,
        false,
        (1, 1),
        Some(ChannelDefinition::new(
            ChannelType::Opacity,
            ChannelAssociation::Color(2),
        )),
    );
    let gray = component(&[0], 8, false, (1, 1), Some(color(1)));
    assert!(matches!(
        convert_jp2_color(
            &image(1, vec![gray, invalid_alpha]),
            &ColorSpecification::enumerated(ENUMERATED_GRAYSCALE),
            &ResourceLimits::default()
        ),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidAlphaAssociation,
            ..
        })
    ));

    let out_of_range = image(1, vec![component(&[256], 8, false, (1, 1), None)]);
    assert!(matches!(
        convert_jp2_color(
            &out_of_range,
            &ColorSpecification::enumerated(ENUMERATED_GRAYSCALE),
            &ResourceLimits::default()
        ),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::ContainerCodestreamMismatch,
            ..
        })
    ));

    let limit = ResourceLimits::default()
        .with_maximum_decoded_bytes(1)
        .unwrap();
    assert!(matches!(
        convert_jp2_color(
            &image(1, vec![component(&[0], 8, false, (1, 1), None)]),
            &ColorSpecification::enumerated(ENUMERATED_GRAYSCALE),
            &limit
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: 1,
            actual: 2
        })
    ));
}

#[test]
fn unknown_enumerated_space_is_typed_unsupported() {
    assert!(matches!(
        convert_jp2_color(
            &image(1, vec![component(&[0], 8, false, (1, 1), None)]),
            &ColorSpecification::enumerated(4_294_967_295),
            &ResourceLimits::default()
        ),
        Err(DecodeError::UnsupportedColorConversion {
            reason: UnsupportedColorConversion::EnumeratedColorSpace
        })
    ));
}
