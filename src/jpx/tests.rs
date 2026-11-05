#[cfg(test)]
mod tests {
    use super::*;
    use crate::jp2::{Composition, CompositionInstructionSet};
    use crate::refinement::{
        compose_planar_pixel, gather_composition_pixel, scatter_composition_pixel,
        source_over_alpha_numerator, source_over_color_numerator, source_over_rounded_ratio,
    };

    fn source_layer_bytes(packet: &[u8], signed: bool) -> (Vec<u8>, usize) {
        fn boxed(kind: [u8; 4], payload: &[u8]) -> Vec<u8> {
            let mut bytes = u32::try_from(payload.len() + 8).unwrap().to_be_bytes().to_vec();
            bytes.extend_from_slice(&kind);
            bytes.extend_from_slice(payload);
            bytes
        }
        let depth = if signed { 0x87 } else { 7 };
        let mut source = vec![
            0xff, 0x4f, 0xff, 0x51, 0, 41, 0, 0,
            0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 1, depth, 1, 1,
            0xff, 0x52, 0, 12, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1,
            0xff, 0x5c, 0, 4, 0x40, 0x40,
            0xff, 0x90, 0, 10, 0, 0,
        ];
        source.extend_from_slice(&u32::try_from(packet.len() + 14).unwrap().to_be_bytes());
        source.extend_from_slice(&[0, 1, 0xff, 0x93]);
        source.extend_from_slice(packet);
        source.extend_from_slice(&[0xff, 0xd9]);
        let source_length = source.len();
        let mut bytes = boxed(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
        bytes.extend(boxed(*b"ftyp", b"jpxb\0\0\0\0jpxb"));
        let mut header = boxed(*b"ihdr", &[0, 0, 0, 1, 0, 0, 0, 1, 0, 1, depth, 7, 0, 0]);
        header.extend(boxed(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
        bytes.extend(boxed(*b"jp2h", &header));
        bytes.extend(boxed(*b"jp2c", &source));
        (bytes, source_length)
    }

    #[test]
    fn actual_jpx_layer_color_source_derives_literal_signed_and_unsigned_planes_from_bytes() {
        let options = DecodeOptions::default();
        for signed in [false, true] {
            for (packet, expected) in [
                (&[0xcf, 0xb4, 0x04, 0x09][..], 257),
                (&[0xc0, 0x21, 0x03][..], 33_153),
                (&[0xcf, 0xb4, 0x08, 0x04, 0x4f][..], 51_400),
            ] {
                let (bytes, _) = source_layer_bytes(packet, signed);
                let file = jp2::parse(&bytes, options.limits()).unwrap();
                let image = super::layer_decode::decode_layer(&file, 0, None, &options).unwrap();
                assert_eq!((image.width(), image.height()), (1, 1));
                assert_eq!(image.color_space(), ConvertedColorSpace::Grayscale);
                assert_eq!(image.channels().len(), 1);
                assert_eq!(image.channel(0).unwrap().channel_type(), crate::ConvertedChannelType::Gray);
                assert_eq!(image.channel(0).unwrap().samples(), &[expected]);
            }
        }
    }

    #[test]
    fn actual_jpx_layer_color_source_uses_real_header_and_actual_optional_override() {
        let (bytes, _) = source_layer_bytes(&[0xcf, 0xb4, 0x04, 0x09], false);
        let options = DecodeOptions::default();
        let mut file = jp2::parse(&bytes, options.limits()).unwrap();
        file.header.color.method = jp2::ColorMethod::AnyIcc { profile_bytes: 123 };
        let gray = jp2::ColorSpecification::enumerated(jp2::ENUMERATED_GRAYSCALE);
        assert_eq!(
            super::layer_decode::decode_layer(&file, 0, None, &options),
            Err(DecodeError::UnsupportedColorConversion { reason: crate::UnsupportedColorConversion::IccProfile }),
        );
        let image = super::layer_decode::decode_layer(&file, 0, Some(&gray), &options).unwrap();
        assert_eq!(image.channel(0).unwrap().samples(), &[257]);
        let unknown = jp2::ColorSpecification::enumerated(u32::MAX);
        assert_eq!(
            super::layer_decode::decode_layer(&file, 0, Some(&unknown), &options),
            Err(DecodeError::UnsupportedColorConversion {
                reason: crate::UnsupportedColorConversion::EnumeratedColorSpace,
            }),
        );
        file.header.color = gray;
        let mut icc = jp2::ColorSpecification::enumerated(0);
        icc.method = jp2::ColorMethod::RestrictedIcc { profile_bytes: u64::MAX };
        assert_eq!(
            super::layer_decode::decode_layer(&file, 0, Some(&icc), &options),
            Err(DecodeError::UnsupportedColorConversion { reason: crate::UnsupportedColorConversion::IccProfile }),
        );
    }

    #[test]
    fn actual_jpx_layer_color_source_preserves_source_errors_before_override_and_conversion() {
        let (bytes, source_length) = source_layer_bytes(&[0xcf, 0xb4, 0x04, 0x09], false);
        let file = jp2::parse(&bytes, &ResourceLimits::default()).unwrap();
        let unknown = jp2::ColorSpecification::enumerated(u32::MAX);
        let input_limited = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_input_bytes(0).unwrap());
        assert_eq!(
            super::layer_decode::decode_layer(&file, usize::MAX, Some(&unknown), &input_limited),
            Err(DecodeError::CodestreamIndexOutOfRange { index: usize::MAX, codestreams: 1 }),
        );
        assert_eq!(
            super::layer_decode::decode_layer(&file, 0, Some(&unknown), &input_limited),
            Err(DecodeError::LimitExceeded { resource: Resource::InputBytes, limit: 0, actual: source_length as u64 }),
        );
        let packet_limited = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(0).unwrap());
        assert_eq!(
            super::layer_decode::decode_layer(&file, 0, Some(&unknown), &packet_limited),
            Err(DecodeError::LimitExceeded { resource: Resource::Packets, limit: 0, actual: 1 }),
        );
        let mut mismatch = file.clone();
        mismatch.header.image.width = 2;
        assert_eq!(
            super::layer_decode::decode_layer(&mismatch, 0, Some(&unknown), &packet_limited),
            Err(DecodeError::MalformedInput {
                offset: mismatch.codestream(0).unwrap().box_header().offset(),
                kind: crate::MalformedKind::ContainerCodestreamMismatch,
            }),
        );
    }

    #[test]
    fn actual_jpx_layer_color_source_applies_source_channel_mapping_before_color_choice() {
        let (bytes, _) = source_layer_bytes(&[0xcf, 0xb4, 0x04, 0x09], false);
        let options = DecodeOptions::default();
        let mut file = jp2::parse(&bytes, options.limits()).unwrap();
        file.header.component_mappings = vec![
            jp2::ComponentMapping { component: 0, mapping_type: jp2::MappingType::Direct },
            jp2::ComponentMapping { component: 0, mapping_type: jp2::MappingType::Direct },
            jp2::ComponentMapping { component: 0, mapping_type: jp2::MappingType::Direct },
        ];
        let rgb = jp2::ColorSpecification::enumerated(jp2::ENUMERATED_SRGB);
        let image = super::layer_decode::decode_layer(&file, 0, Some(&rgb), &options).unwrap();
        assert_eq!(image.color_space(), ConvertedColorSpace::Srgb);
        assert_eq!(image.channels().len(), 3);
        for channel in image.channels() {
            assert_eq!(channel.samples(), &[257]);
        }
        file.header.component_mappings[0].component = 1;
        let unknown = jp2::ColorSpecification::enumerated(u32::MAX);
        assert_eq!(
            super::layer_decode::decode_layer(&file, 0, Some(&unknown), &options),
            Err(DecodeError::MalformedInput {
                offset: 0, kind: crate::MalformedKind::InvalidImageGeometry,
            }),
        );
    }

    fn opacity_source_bytes(opacity: Option<&[u8]>, association: bool) -> Vec<u8> {
        fn boxed(kind: [u8; 4], payload: &[u8]) -> Vec<u8> {
            let mut bytes = u32::try_from(payload.len() + 8).unwrap().to_be_bytes().to_vec();
            bytes.extend_from_slice(&kind);
            bytes.extend_from_slice(payload);
            bytes
        }
        let (mut bytes, length) = source_layer_bytes(&[0xcf, 0xb4, 0x04, 0x09], false);
        let source = bytes.split_off(bytes.len() - length - 8);
        if association {
            bytes.extend(boxed(*b"jpch", &[]));
        }
        let mut layer = boxed(*b"creg", &[0, 1, 0, 1, 0, 0, 1, 1, 0, 0]);
        if let Some(opacity) = opacity {
            layer.extend(boxed(*b"opct", opacity));
        }
        bytes.extend(boxed(*b"jplh", &layer));
        bytes.extend(source);
        bytes
    }

    fn opacity_source_owned() -> OwnedLayer {
        OwnedLayer {
            width: 2,
            height: 2,
            color_space: ConvertedColorSpace::Grayscale,
            colors: vec![vec![257, 12, 13, 14]],
            alpha: Some((vec![7, 8, 9, 10], true)),
        }
    }

    fn opacity_source_snapshot(layer: &OwnedLayer)
        -> (u32, u32, ConvertedColorSpace, Vec<Vec<u16>>, Option<(Vec<u16>, bool)>)
    {
        (layer.width, layer.height, layer.color_space, layer.colors.clone(), layer.alpha.clone())
    }

    #[test]
    fn actual_source_opacity_keeps_no_op_and_existing_alpha_mode_frames() {
        let tight = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_input_bytes(0).unwrap());
        for mode in [None, Some(&[0][..]), Some(&[1][..])] {
            let bytes = opacity_source_bytes(mode, false);
            let file = jp2::parse(&bytes, &ResourceLimits::default()).unwrap();
            let layer = file.compositing_layer(0).unwrap();
            let mut owned = opacity_source_owned();
            let old = opacity_source_snapshot(&owned);
            super::opacity::apply_layer_opacity(&file, layer, usize::MAX, &mut owned, None, &tight).unwrap();
            assert_eq!(owned.colors, old.3);
            assert_eq!((owned.width, owned.height, owned.color_space), (old.0, old.1, old.2));
            let expected = match mode { None => true, Some(mode) => mode[0] == 1 };
            assert_eq!(owned.alpha, Some((vec![7, 8, 9, 10], expected)));
            if mode.is_some() {
                owned.alpha = None;
                let old = opacity_source_snapshot(&owned);
                assert_eq!(
                    super::opacity::apply_layer_opacity(&file, layer, 0, &mut owned, None, &tight),
                    Err(DecodeError::MalformedInput {
                        offset: layer.box_header().offset(), kind: crate::MalformedKind::MissingRequiredStructure,
                    }),
                );
                assert_eq!(opacity_source_snapshot(&owned), old);
            }
        }
    }

    #[test]
    fn actual_source_opacity_decodes_registers_real_alpha_and_preserves_every_error_frame() {
        for (mode, premultiplied) in [(0, false), (1, true)] {
            let bytes = opacity_source_bytes(Some(&[mode]), false);
            let file = jp2::parse(&bytes, &ResourceLimits::default()).unwrap();
            let layer = file.compositing_layer(0).unwrap();
            let registration = &layer.registrations()[0];
            let mut owned = opacity_source_owned();
            let old = opacity_source_snapshot(&owned);
            super::opacity::apply_layer_opacity(
                &file, layer, 0, &mut owned, Some(registration), &DecodeOptions::default(),
            ).unwrap();
            assert_eq!(owned.alpha, Some((vec![257, 0, 0, 0], premultiplied)));
            assert_eq!((owned.width, owned.height, owned.color_space, &owned.colors), (old.0, old.1, old.2, &old.3));
            let old = opacity_source_snapshot(&owned);
            let tight = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_input_bytes(0).unwrap());
            assert_eq!(
                super::opacity::apply_layer_opacity(&file, layer, 0, &mut owned, Some(registration), &tight),
                Err(DecodeError::LimitExceeded {
                    resource: Resource::InputBytes, limit: 0,
                    actual: file.codestream(0).unwrap().data().len() as u64,
                }),
            );
            assert_eq!(opacity_source_snapshot(&owned), old);
            let invalid = jp2::CodestreamRegistration { codestream_index: u16::MAX, ..*registration };
            assert_eq!(
                super::opacity::apply_layer_opacity(
                    &file, layer, 0, &mut owned, Some(&invalid), &DecodeOptions::default(),
                ),
                Err(DecodeError::CodestreamIndexOutOfRange { index: usize::from(u16::MAX), codestreams: 1 }),
            );
            assert_eq!(opacity_source_snapshot(&owned), old);
        }
    }

    #[test]
    fn actual_source_opacity_uses_actual_chroma_header_and_association_fallback() {
        let options = DecodeOptions::default();
        for association in [false, true] {
            let bytes = opacity_source_bytes(Some(&[2, 1, 1]), association);
            let mut file = jp2::parse(&bytes, options.limits()).unwrap();
            if association {
                file.header.image.bit_depth = jp2::ComponentBitDepth::Variable;
            }
            let layer = file.compositing_layer(0).unwrap();
            let mut owned = opacity_source_owned();
            let old = opacity_source_snapshot(&owned);
            super::opacity::apply_layer_opacity(&file, layer, 0, &mut owned, None, &options).unwrap();
            assert_eq!(owned.alpha, Some((vec![0, u16::MAX, u16::MAX, u16::MAX], false)));
            assert_eq!((owned.width, owned.height, owned.color_space, &owned.colors), (old.0, old.1, old.2, &old.3));
            if !association {
                let mut file = file;
                file.header.image.bit_depth = jp2::ComponentBitDepth::Variable;
                let old = opacity_source_snapshot(&owned);
                assert_eq!(
                    super::opacity::apply_layer_opacity(
                        &file, file.compositing_layer(0).unwrap(), 0, &mut owned, None, &options,
                    ),
                    Err(DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::MissingRequiredStructure }),
                );
                assert_eq!(opacity_source_snapshot(&owned), old);
            }
        }
    }

    #[test]
    fn actual_source_opacity_preserves_chroma_count_lookup_and_missing_sample_error_order() {
        let bytes = opacity_source_bytes(Some(&[2, 1, 1]), false);
        let file = jp2::parse(&bytes, &ResourceLimits::default()).unwrap();
        let layer = file.compositing_layer(0).unwrap();
        let options = DecodeOptions::default();
        let mut owned = opacity_source_owned();
        owned.colors.push(vec![1, 2, 3, 4]);
        let old = opacity_source_snapshot(&owned);
        assert_eq!(
            super::opacity::apply_layer_opacity(&file, layer, usize::MAX, &mut owned, None, &options),
            Err(DecodeError::MalformedInput { offset: layer.box_header().offset(), kind: crate::MalformedKind::InvalidBoxContents }),
        );
        assert_eq!(opacity_source_snapshot(&owned), old);
        owned.colors.pop();
        let old = opacity_source_snapshot(&owned);
        assert_eq!(
            super::opacity::apply_layer_opacity(&file, layer, usize::MAX, &mut owned, None, &options),
            Err(DecodeError::CodestreamIndexOutOfRange { index: usize::MAX, codestreams: 1 }),
        );
        assert_eq!(opacity_source_snapshot(&owned), old);
        owned.colors[0].pop();
        let old = opacity_source_snapshot(&owned);
        assert!(super::opacity::apply_layer_opacity(&file, layer, 0, &mut owned, None, &options).is_err());
        assert_eq!(opacity_source_snapshot(&owned), old);
    }

    fn independent_chroma_normalization(
        values: &[u8],
        channels: u8,
        depth: ComponentBitDepth,
    ) -> Result<Vec<u16>, DecodeError> {
        let ComponentBitDepth::Uniform { bits, signed } = depth else {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::MissingRequiredStructure,
            });
        };
        if bits == 0 || bits > 38 {
            return Err(invalid_layer());
        }
        let bytes = usize::from(bits).div_ceil(8);
        if values.len() != bytes * usize::from(channels) {
            return Err(invalid_layer());
        }
        let modulus = 1_u128 << bits;
        let maximum = modulus - 1;
        Ok(values
            .chunks_exact(bytes)
            .map(|chunk| {
                let raw = chunk
                    .iter()
                    .fold(0_u128, |value, &byte| value * 256 + u128::from(byte));
                let residue = raw % modulus;
                let nominal = if signed {
                    (residue + modulus / 2) % modulus
                } else {
                    residue
                };
                u16::try_from((nominal * 65_535 + maximum / 2) / maximum).unwrap()
            })
            .collect())
    }

    #[test]
    fn external_opacity_matches_raw_min_rectangle_and_commits_owner_only_on_success() {
        let mut cases = 0;
        for width in 0..=2 {
            for height in 0..=2 {
                for source_width in 0..=2 {
                    for source_height in 0..=2 {
                        let source_pixels = usize::try_from(source_width * source_height).unwrap();
                        for source_channels in [0, 1, 3] {
                            for source_length in [
                                0,
                                source_pixels.saturating_sub(1),
                                source_pixels,
                                source_pixels + 1,
                            ] {
                                for channels in [0, 4] {
                                    for space in
                                        [ConvertedColorSpace::Grayscale, ConvertedColorSpace::Srgb]
                                    {
                                        for prior_alpha in [None, Some((vec![5, 7], true))] {
                                            for source_alpha in [None, Some((vec![11], true))] {
                                                for premultiplied in [false, true] {
                                                    let source = OwnedLayer {
                                                        width: source_width,
                                                        height: source_height,
                                                        color_space: ConvertedColorSpace::Srgb,
                                                        colors: vec![
                                                                (0..source_length)
                                                                    .map(|index| (index * 31 + 7)
                                                                        as u16)
                                                                    .collect();
                                                                source_channels
                                                            ],
                                                        alpha: source_alpha.clone(),
                                                    };
                                                    let colors = vec![vec![17, 19, 23]; channels];
                                                    let mut owned = OwnedLayer {
                                                        width,
                                                        height,
                                                        color_space: space,
                                                        colors: colors.clone(),
                                                        alpha: prior_alpha.clone(),
                                                    };
                                                    let expected =
                                                        (|| -> Result<Vec<u16>, DecodeError> {
                                                            let samples = source
                                                                .colors
                                                                .first()
                                                                .ok_or_else(invalid_layer)?;
                                                            let count = usize::try_from(
                                                                u128::from(width)
                                                                    * u128::from(height),
                                                            )
                                                            .map_err(|_| arithmetic_overflow())?;
                                                            let mut alpha = vec![0; count];
                                                            for y in 0..height.min(source_height) {
                                                                for x in 0..width.min(source_width)
                                                                {
                                                                    let destination =
                                                                        usize::try_from(
                                                                            u128::from(y)
                                                                                * u128::from(width)
                                                                                + u128::from(x),
                                                                        )
                                                                        .map_err(|_| {
                                                                            arithmetic_overflow()
                                                                        })?;
                                                                    let source_index =
                                                                        usize::try_from(
                                                                            u128::from(y)
                                                                                * u128::from(
                                                                                    source_width,
                                                                                )
                                                                                + u128::from(x),
                                                                        )
                                                                        .map_err(|_| {
                                                                            arithmetic_overflow()
                                                                        })?;
                                                                    let sample = *samples
                                                                        .get(source_index)
                                                                        .ok_or_else(
                                                                            invalid_layer,
                                                                        )?;
                                                                    *alpha.get_mut(destination).ok_or_else(invalid_layer)? = sample;
                                                                }
                                                            }
                                                            Ok(alpha)
                                                        })(
                                                        );
                                                    let actual = copy_registered_layer_opacity(
                                                        &mut owned,
                                                        &source,
                                                        premultiplied,
                                                    );
                                                    assert_eq!(
                                                        (
                                                            owned.width,
                                                            owned.height,
                                                            owned.color_space
                                                        ),
                                                        (width, height, space)
                                                    );
                                                    assert_eq!(owned.colors, colors);
                                                    match expected {
                                                        Err(error) => {
                                                            assert_eq!(actual, Err(error));
                                                            assert_eq!(owned.alpha, prior_alpha);
                                                        }
                                                        Ok(alpha) => {
                                                            actual.unwrap();
                                                            assert_eq!(
                                                                owned.alpha,
                                                                Some((alpha, premultiplied))
                                                            );
                                                        }
                                                    }
                                                    cases += 1;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 31104);
        let mut owned = OwnedLayer {
            width: u32::MAX,
            height: u32::MAX,
            color_space: ConvertedColorSpace::Srgb,
            colors: vec![],
            alpha: Some((vec![29], false)),
        };
        let source = OwnedLayer {
            width: 0,
            height: 0,
            color_space: ConvertedColorSpace::Grayscale,
            colors: vec![],
            alpha: Some((vec![31], false)),
        };
        assert_eq!(
            copy_registered_layer_opacity(&mut owned, &source, true),
            Err(invalid_layer())
        );
        assert_eq!(owned.alpha, Some((vec![29], false)));
    }

    #[test]
    fn opacity_pixel_and_row_preserve_wide_indices_and_prior_scratch_updates() {
        let mut cases = 0;
        for source_width in [0, 1, 2, u32::MAX] {
            for width in [0, 1, 2, u32::MAX] {
                for x in [0, 1, 2, u32::MAX] {
                    for y in [0, 1, 2, u32::MAX] {
                        for source_length in 0..=3 {
                            for output_length in 0..=3 {
                                let samples = (0..source_length)
                                    .map(|index| (index * 13 + 11) as u16)
                                    .collect::<Vec<_>>();
                                let mut alpha = vec![37; output_length];
                                let mut expected_alpha = alpha.clone();
                                let expected = (|| {
                                    let destination = usize::try_from(
                                        u128::from(y) * u128::from(width) + u128::from(x),
                                    )
                                    .map_err(|_| arithmetic_overflow())?;
                                    let source = usize::try_from(
                                        u128::from(y) * u128::from(source_width) + u128::from(x),
                                    )
                                    .map_err(|_| arithmetic_overflow())?;
                                    let sample = *samples.get(source).ok_or_else(invalid_layer)?;
                                    *expected_alpha
                                        .get_mut(destination)
                                        .ok_or_else(invalid_layer)? = sample;
                                    Ok(())
                                })();
                                assert_eq!(
                                    copy_opacity_pixel(
                                        &samples,
                                        (source_width, width, x, y),
                                        &mut alpha
                                    ),
                                    expected
                                );
                                assert_eq!(alpha, expected_alpha);
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 4096);
        let mut alpha = vec![41, 43, 47];
        assert_eq!(
            copy_opacity_row(&[11, 13], 2, (3, 0, 3), &mut alpha),
            Err(invalid_layer())
        );
        assert_eq!(alpha, vec![11, 13, 47]);
    }

    #[test]
    fn opacity_chroma_policy_preserves_strict_rejection_and_general_nonmatches() {
        let mut cases = 0;
        for space in [ConvertedColorSpace::Grayscale, ConvertedColorSpace::Srgb] {
            for width in 0..=2 {
                for height in 0..=2 {
                    let pixels = usize::try_from(width * height).unwrap();
                    for channels in 0..=3 {
                        for missing in 0..=channels {
                            let colors = (0..channels)
                                .map(|channel| {
                                    (0..pixels.saturating_sub(usize::from(channel < missing)))
                                        .map(|pixel| if pixel % 2 == 0 { 17 } else { u16::MAX })
                                        .collect::<Vec<_>>()
                                })
                                .collect::<Vec<_>>();
                            for key in [0, 17, u16::MAX] {
                                for key_count in 0..=channels + 1 {
                                    let keys = vec![key; key_count];
                                    for prior_alpha in
                                        [None, Some((vec![], false)), Some((vec![123, 456], true))]
                                    {
                                        for reject_missing in [false, true] {
                                            let mut layer = OwnedLayer {
                                                width,
                                                height,
                                                color_space: space,
                                                colors: colors.clone(),
                                                alpha: prior_alpha.clone(),
                                            };
                                            let expected_error = key_count != channels
                                                || (reject_missing
                                                    && colors
                                                        .iter()
                                                        .any(|plane| plane.len() < pixels));
                                            let result = apply_chroma_key_with_policy(
                                                &mut layer,
                                                &keys,
                                                reject_missing,
                                            );
                                            assert_eq!(
                                                (layer.width, layer.height, layer.color_space),
                                                (width, height, space)
                                            );
                                            assert_eq!(layer.colors, colors);
                                            if expected_error {
                                                assert_eq!(result, Err(invalid_layer()));
                                                assert_eq!(layer.alpha, prior_alpha);
                                            } else {
                                                result.unwrap();
                                                let expected = (0..pixels)
                                                    .map(|pixel| {
                                                        if colors.iter().all(|plane| {
                                                            plane.get(pixel) == Some(&key)
                                                        }) {
                                                            0
                                                        } else {
                                                            u16::MAX
                                                        }
                                                    })
                                                    .collect::<Vec<_>>();
                                                assert_eq!(layer.alpha, Some((expected, false)));
                                            }
                                            cases += 1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 12960);
        let mut layer = OwnedLayer {
            width: 1,
            height: 1,
            color_space: ConvertedColorSpace::Srgb,
            colors: vec![vec![17], vec![]],
            alpha: Some((vec![19], true)),
        };
        assert_eq!(
            apply_chroma_key_with_policy(&mut layer, &[0, 0], true),
            Err(invalid_layer())
        );
        assert_eq!(layer.alpha, Some((vec![19], true)));
    }

    #[test]
    fn local_alpha_mode_changes_only_representation_or_reports_actual_offset() {
        let colors = [
            vec![],
            vec![vec![]],
            vec![vec![7], vec![11, 13], vec![], vec![17]],
        ];
        let mut cases = 0;
        for width in [0, 1, u32::MAX] {
            for height in [0, 2, u32::MAX] {
                for space in [ConvertedColorSpace::Grayscale, ConvertedColorSpace::Srgb] {
                    for planes in &colors {
                        for prior_alpha in [
                            None,
                            Some((vec![], false)),
                            Some((vec![1, u16::MAX], false)),
                            Some((vec![3, 5, 7], true)),
                        ] {
                            for premultiplied in [false, true] {
                                for offset in [0, 7, u64::MAX] {
                                    let mut layer = OwnedLayer {
                                        width,
                                        height,
                                        color_space: space,
                                        colors: planes.clone(),
                                        alpha: prior_alpha.clone(),
                                    };
                                    let result =
                                        set_layer_alpha_mode(&mut layer, premultiplied, offset);
                                    assert_eq!(
                                        (layer.width, layer.height, layer.color_space),
                                        (width, height, space)
                                    );
                                    assert_eq!(layer.colors, *planes);
                                    match &prior_alpha {
                                        None => {
                                            assert_eq!(
                                                result,
                                                Err(DecodeError::MalformedInput {
                                                    offset,
                                                    kind: MalformedKind::MissingRequiredStructure
                                                })
                                            );
                                            assert_eq!(layer.alpha, None);
                                        }
                                        Some((samples, _)) => {
                                            result.unwrap();
                                            assert_eq!(
                                                layer.alpha,
                                                Some((samples.clone(), premultiplied))
                                            );
                                        }
                                    }
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 1296);
    }

    #[test]
    fn component_chroma_preparation_preserves_descriptor_before_payload_validation() {
        let choices = [0, 1, 7, 8, 9, 16, 31, 32, 38, 39, u8::MAX]
            .into_iter()
            .flat_map(|bits| [(bits, false), (bits, true)])
            .collect::<Vec<_>>();
        let mut descriptors = vec![vec![]];
        for &first in &choices {
            descriptors.push(vec![first]);
            for &second in &choices {
                descriptors.push(vec![first, second]);
            }
        }
        let mut cases = 0;
        for description in descriptors {
            let expected_length = description
                .iter()
                .map(|&(bits, _)| usize::from(bits).div_ceil(8))
                .sum::<usize>();
            for pattern in 0..3 {
                for length in [
                    0,
                    expected_length.saturating_sub(1),
                    expected_length,
                    expected_length + 1,
                ] {
                    let values = (0..length)
                        .map(|index| match pattern {
                            0 => 0,
                            1 => u8::MAX,
                            _ => (index * 19 + 5) as u8,
                        })
                        .collect::<Vec<_>>();
                    let expected = (|| -> Result<Vec<u16>, DecodeError> {
                        if description.iter().any(|&(bits, _)| bits == 0 || bits > 38) {
                            return Err(invalid_layer());
                        }
                        if length != expected_length {
                            return Err(invalid_layer());
                        }
                        let mut result = vec![];
                        let mut cursor = 0;
                        for &(bits, signed) in &description {
                            let end = cursor + usize::from(bits).div_ceil(8);
                            let keys = independent_chroma_normalization(
                                &values[cursor..end],
                                1,
                                ComponentBitDepth::Uniform { bits, signed },
                            )?;
                            result.extend(keys);
                            cursor = end;
                        }
                        Ok(result)
                    })();
                    assert_eq!(
                        normalized_chroma_keys_for_components(&values, &description),
                        expected
                    );
                    cases += 1;
                }
            }
        }
        assert_eq!(cases, 6084);
    }

    #[test]
    fn component_chroma_append_keeps_keys_and_offset_on_every_first_error() {
        let mut cases = 0;
        for length in 0..=6 {
            let values = (0..length)
                .map(|index| (index * 13 + 7) as u8)
                .collect::<Vec<_>>();
            for bits in [0, 1, 8, 9, 38, 39, u8::MAX] {
                for signed in [false, true] {
                    for initial_offset in [0, 1, 2, usize::MAX - 1, usize::MAX] {
                        for initial_keys in [vec![], vec![17], vec![19, 23]] {
                            let mut expected_keys = initial_keys.clone();
                            let mut expected_offset = initial_offset;
                            let expected = (|| {
                                let bytes = usize::from(bits.saturating_add(7) / 8);
                                let end = initial_offset
                                    .checked_add(bytes)
                                    .ok_or_else(arithmetic_overflow)?;
                                let data =
                                    values.get(initial_offset..end).ok_or_else(invalid_layer)?;
                                let normalized = independent_chroma_normalization(
                                    data,
                                    1,
                                    ComponentBitDepth::Uniform { bits, signed },
                                )?;
                                expected_keys.push(*normalized.first().ok_or_else(invalid_layer)?);
                                expected_offset = end;
                                Ok(())
                            })();
                            let mut keys = initial_keys;
                            let mut offset = initial_offset;
                            assert_eq!(
                                append_component_chroma_key(
                                    &values,
                                    (bits, signed),
                                    &mut keys,
                                    &mut offset
                                ),
                                expected
                            );
                            assert_eq!(keys, expected_keys);
                            assert_eq!(offset, expected_offset);
                            cases += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 1470);
    }

    #[test]
    fn raw_chroma_normalization_preserves_all_depth_length_and_channel_frontiers() {
        let mut cases = 0;
        for bits in 0..=u8::MAX {
            for signed in [false, true] {
                for channels in [0, 1, 2, 3, u8::MAX] {
                    let expected_length = usize::from(bits).div_ceil(8) * usize::from(channels);
                    for pattern in 0..3 {
                        for length in [
                            expected_length.saturating_sub(1),
                            expected_length,
                            expected_length + 1,
                        ] {
                            let values = (0..length)
                                .map(|index| match pattern {
                                    0 => 0,
                                    1 => u8::MAX,
                                    _ => (index * 17 + 3) as u8,
                                })
                                .collect::<Vec<_>>();
                            let depth = ComponentBitDepth::Uniform { bits, signed };
                            assert_eq!(
                                normalized_chroma_keys(&values, channels, depth),
                                independent_chroma_normalization(&values, channels, depth)
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 23040);
        for channels in [0, 1, u8::MAX] {
            for values in [vec![], vec![0], vec![255; 3]] {
                assert_eq!(
                    normalized_chroma_keys(&values, channels, ComponentBitDepth::Variable),
                    Err(DecodeError::MalformedInput {
                        offset: 0,
                        kind: MalformedKind::MissingRequiredStructure
                    })
                );
            }
        }
    }

    #[test]
    fn raw_chroma_normalization_matches_all_u16_words_and_38_bit_padding() {
        for raw in 0..=u16::MAX {
            for signed in [false, true] {
                let values = raw.to_be_bytes();
                let depth = ComponentBitDepth::Uniform { bits: 16, signed };
                assert_eq!(
                    normalized_chroma_keys(&values, 1, depth),
                    independent_chroma_normalization(&values, 1, depth)
                );
            }
        }
        for raw in [
            0_u64,
            1,
            (1 << 37) - 1,
            1 << 37,
            (1 << 38) - 1,
            (1 << 40) - 1,
        ] {
            for signed in [false, true] {
                let bytes = raw.to_be_bytes();
                let depth = ComponentBitDepth::Uniform { bits: 38, signed };
                assert_eq!(
                    normalized_chroma_keys(&bytes[3..], 1, depth),
                    independent_chroma_normalization(&bytes[3..], 1, depth)
                );
            }
        }
    }

    #[test]
    fn complete_registration_matches_independent_wide_raster_and_representation() {
        let mut cases = 0;
        for width in 0..=2 {
            for height in 0..=2 {
                let source_pixels = usize::try_from(width * height).unwrap();
                for horizontal_subsampling in 0..=2 {
                    for vertical_subsampling in 0..=2 {
                        for horizontal_grid in 0..=3 {
                            for vertical_grid in 0..=3 {
                                for horizontal_offset in [0, 1, 3] {
                                    for vertical_offset in [0, 1, 3] {
                                        for channels in [0, 1, 4] {
                                            for space in [
                                                ConvertedColorSpace::Grayscale,
                                                ConvertedColorSpace::Srgb,
                                            ] {
                                                for alpha_kind in 0..3 {
                                                    let colors = (0..channels)
                                                        .map(|channel| {
                                                            (0..source_pixels)
                                                                .map(|pixel| {
                                                                    u16::try_from(
                                                                        17 * channel
                                                                            + 3 * pixel
                                                                            + 1,
                                                                    )
                                                                    .unwrap()
                                                                })
                                                                .collect::<Vec<_>>()
                                                        })
                                                        .collect::<Vec<_>>();
                                                    let alpha = match alpha_kind {
                                                        0 => None,
                                                        1 => Some((
                                                            vec![32_768; source_pixels],
                                                            false,
                                                        )),
                                                        _ => Some((vec![], true)),
                                                    };
                                                    let source = OwnedLayer {
                                                        width,
                                                        height,
                                                        color_space: space,
                                                        colors,
                                                        alpha,
                                                    };
                                                    let registration =
                                                        jp2::CodestreamRegistration {
                                                            codestream_index: u16::MAX,
                                                            horizontal_subsampling,
                                                            vertical_subsampling,
                                                            horizontal_offset,
                                                            vertical_offset,
                                                        };
                                                    let expected = (|| {
                                                        if horizontal_subsampling == 0
                                                            || vertical_subsampling == 0
                                                            || horizontal_grid == 0
                                                            || vertical_grid == 0
                                                        {
                                                            return Err(invalid_layer());
                                                        }
                                                        let output_width =
                                                            independent_registered_extent(
                                                                width,
                                                                u32::from(horizontal_subsampling),
                                                                u32::from(horizontal_grid),
                                                                horizontal_offset,
                                                            )?;
                                                        let output_height =
                                                            independent_registered_extent(
                                                                height,
                                                                u32::from(vertical_subsampling),
                                                                u32::from(vertical_grid),
                                                                vertical_offset,
                                                            )?;
                                                        let count = usize::try_from(
                                                            u128::from(output_width)
                                                                * u128::from(output_height),
                                                        )
                                                        .map_err(|_| arithmetic_overflow())?;
                                                        let mut output =
                                                            vec![vec![0; count]; channels];
                                                        let mut output_alpha = vec![0; count];
                                                        for y in 0..output_height {
                                                            let numerator_y = u128::from(y)
                                                                * u128::from(vertical_grid);
                                                            if numerator_y > u128::from(u32::MAX) {
                                                                return Err(arithmetic_overflow());
                                                            }
                                                            if numerator_y
                                                                < u128::from(vertical_offset)
                                                            {
                                                                continue;
                                                            }
                                                            let source_y = (numerator_y
                                                                - u128::from(vertical_offset))
                                                                / u128::from(vertical_subsampling);
                                                            if source_y >= u128::from(height) {
                                                                continue;
                                                            }
                                                            for x in 0..output_width {
                                                                let numerator_x = u128::from(x)
                                                                    * u128::from(horizontal_grid);
                                                                if numerator_x
                                                                    > u128::from(u32::MAX)
                                                                {
                                                                    return Err(
                                                                        arithmetic_overflow(),
                                                                    );
                                                                }
                                                                if numerator_x
                                                                    < u128::from(horizontal_offset)
                                                                {
                                                                    continue;
                                                                }
                                                                let source_x = (numerator_x
                                                                    - u128::from(
                                                                        horizontal_offset,
                                                                    ))
                                                                    / u128::from(
                                                                        horizontal_subsampling,
                                                                    );
                                                                if source_x >= u128::from(width) {
                                                                    continue;
                                                                }
                                                                let input_index = usize::try_from(
                                                                    source_y * u128::from(width)
                                                                        + source_x,
                                                                )
                                                                .unwrap();
                                                                let output_index = usize::try_from(
                                                                    u128::from(y)
                                                                        * u128::from(output_width)
                                                                        + u128::from(x),
                                                                )
                                                                .unwrap();
                                                                for (channel, samples) in
                                                                    output.iter_mut().enumerate()
                                                                {
                                                                    samples[output_index] = *source
                                                                        .colors[channel]
                                                                        .get(input_index)
                                                                        .ok_or_else(
                                                                            invalid_layer,
                                                                        )?;
                                                                }
                                                                output_alpha[output_index] =
                                                                    match &source.alpha {
                                                                        None => u16::MAX,
                                                                        Some((samples, _)) => {
                                                                            *samples
                                                                                .get(input_index)
                                                                                .ok_or_else(
                                                                                    invalid_layer,
                                                                                )?
                                                                        }
                                                                    };
                                                            }
                                                        }
                                                        let premultiplied = source
                                                            .alpha
                                                            .as_ref()
                                                            .is_some_and(|(_, flag)| *flag);
                                                        Ok((
                                                            output_width,
                                                            output_height,
                                                            space,
                                                            output,
                                                            Some((output_alpha, premultiplied)),
                                                        ))
                                                    })(
                                                    );
                                                    let actual = register_layer(
                                                        &source,
                                                        &registration,
                                                        horizontal_grid,
                                                        vertical_grid,
                                                    )
                                                    .map(|layer| {
                                                        (
                                                            layer.width,
                                                            layer.height,
                                                            layer.color_space,
                                                            layer.colors,
                                                            layer.alpha,
                                                        )
                                                    });
                                                    assert_eq!(actual, expected);
                                                    cases += 1;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 209_952);
    }

    #[test]
    fn registered_row_preserves_prior_alpha_before_late_coordinate_overflow() {
        let source = OwnedLayer {
            width: 1,
            height: 1,
            color_space: ConvertedColorSpace::Grayscale,
            colors: vec![],
            alpha: None,
        };
        let registration = jp2::CodestreamRegistration {
            codestream_index: 0,
            horizontal_subsampling: 1,
            vertical_subsampling: 1,
            horizontal_offset: 0,
            vertical_offset: 0,
        };
        let mut colors = vec![];
        let mut alpha = vec![7];
        assert_eq!(
            copy_registered_row(
                &source,
                &registration,
                (u16::MAX, 1),
                (u32::MAX, 0),
                &mut colors,
                &mut alpha
            ),
            Err(arithmetic_overflow())
        );
        assert_eq!(alpha, vec![u16::MAX]);
        alpha[0] = 11;
        assert_eq!(
            copy_registered_row(
                &source,
                &registration,
                (1, 2),
                (1, u32::MAX),
                &mut colors,
                &mut alpha
            ),
            Err(arithmetic_overflow())
        );
        assert_eq!(alpha, vec![11]);
    }

    #[test]
    fn registered_pixel_preserves_ordered_partial_colors_and_alpha_errors() {
        let sources = [
            vec![],
            vec![vec![]],
            vec![vec![7, 11], vec![13]],
            vec![vec![17, 19, 23, 29]; 4],
        ];
        let destinations = [
            vec![],
            vec![vec![]],
            vec![vec![101]],
            vec![vec![103, 107], vec![]],
            vec![vec![109, 113, 127]; 4],
        ];
        let mut cases = 0;
        for source_width in [0, 1, 2, u32::MAX] {
            for source_position in [(0, 0), (1, 0), (0, 1), (2, 1), (u32::MAX, u32::MAX)] {
                for destination_position in [
                    (0, 0, 0),
                    (1, 0, 0),
                    (2, 1, 0),
                    (2, 0, 1),
                    (u32::MAX, u32::MAX, u32::MAX),
                ] {
                    for source_colors in &sources {
                        for initial_colors in &destinations {
                            for source_alpha in [
                                None,
                                Some((vec![], false)),
                                Some((vec![0, 31, 37, u16::MAX], false)),
                                Some((vec![41, 43, 47, 53], true)),
                            ] {
                                for initial_alpha in [vec![], vec![131], vec![137, 139, 149]] {
                                    let source = OwnedLayer {
                                        width: source_width,
                                        height: 1,
                                        color_space: ConvertedColorSpace::Srgb,
                                        colors: source_colors.clone(),
                                        alpha: source_alpha.clone(),
                                    };
                                    let mut expected_colors = initial_colors.clone();
                                    let mut expected_alpha = initial_alpha.clone();
                                    let expected = (|| -> Result<(), DecodeError> {
                                        let source_index = usize::try_from(
                                            u128::from(source_position.1)
                                                * u128::from(source_width)
                                                + u128::from(source_position.0),
                                        )
                                        .map_err(|_| arithmetic_overflow())?;
                                        let destination = usize::try_from(
                                            u128::from(destination_position.2)
                                                * u128::from(destination_position.0)
                                                + u128::from(destination_position.1),
                                        )
                                        .map_err(|_| arithmetic_overflow())?;
                                        for (channel, output) in
                                            expected_colors.iter_mut().enumerate()
                                        {
                                            let value = source_colors
                                                .get(channel)
                                                .and_then(|samples| samples.get(source_index))
                                                .ok_or_else(invalid_layer)?;
                                            *output
                                                .get_mut(destination)
                                                .ok_or_else(invalid_layer)? = *value;
                                        }
                                        let value = match &source_alpha {
                                            None => u16::MAX,
                                            Some((samples, _)) => *samples
                                                .get(source_index)
                                                .ok_or_else(invalid_layer)?,
                                        };
                                        *expected_alpha
                                            .get_mut(destination)
                                            .ok_or_else(invalid_layer)? = value;
                                        Ok(())
                                    })();
                                    let mut colors = initial_colors.clone();
                                    let mut alpha = initial_alpha;
                                    assert_eq!(
                                        copy_registered_pixel(
                                            &source,
                                            source_position,
                                            destination_position,
                                            &mut colors,
                                            &mut alpha
                                        ),
                                        expected
                                    );
                                    assert_eq!(colors, expected_colors);
                                    assert_eq!(alpha, expected_alpha);
                                    assert_eq!(source.colors, *source_colors);
                                    assert_eq!(source.alpha, source_alpha);
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 24000);
    }

    fn independent_registered_extent(
        samples: u32,
        subsampling: u32,
        grid: u32,
        offset: u32,
    ) -> Result<u32, DecodeError> {
        if grid == 0 {
            return Err(invalid_layer());
        }
        let numerator = u128::from(samples) * u128::from(subsampling) + u128::from(offset);
        let extent = numerator.div_ceil(u128::from(grid));
        u32::try_from(extent).map_err(|_| arithmetic_overflow())
    }

    #[test]
    fn registered_extent_matches_wide_ceil_at_every_native_frontier() {
        let values = [0, 1, 2, 3, 255, 65_535, u32::MAX - 1, u32::MAX];
        let mut cases = 0;
        for samples in values {
            for subsampling in values {
                for grid in values {
                    for offset in values {
                        assert_eq!(
                            registered_extent(samples, subsampling, grid, offset),
                            independent_registered_extent(samples, subsampling, grid, offset),
                        );
                        cases += 1;
                    }
                }
            }
        }
        assert_eq!(cases, 4096);
    }

    #[test]
    fn registration_geometry_preserves_raw_admission_and_axis_order() {
        let mut cases = 0;
        for width in [0, 1, 3, u32::MAX] {
            for height in [0, 1, 3, u32::MAX] {
                for horizontal_subsampling in [0, 1, 2, u8::MAX] {
                    for vertical_subsampling in [0, 1, 2, u8::MAX] {
                        for horizontal_grid in [0, 1, 2, u16::MAX] {
                            for vertical_grid in [0, 1, 2, u16::MAX] {
                                for horizontal_offset in [0, u32::MAX] {
                                    for vertical_offset in [0, u32::MAX] {
                                        let registration = jp2::CodestreamRegistration {
                                            codestream_index: u16::MAX,
                                            horizontal_subsampling,
                                            vertical_subsampling,
                                            horizontal_offset,
                                            vertical_offset,
                                        };
                                        let expected =
                                            if horizontal_subsampling == 0
                                                || vertical_subsampling == 0
                                                || horizontal_grid == 0
                                                || vertical_grid == 0
                                            {
                                                Err(invalid_layer())
                                            } else {
                                                independent_registered_extent(
                                                    width,
                                                    u32::from(horizontal_subsampling),
                                                    u32::from(horizontal_grid),
                                                    horizontal_offset,
                                                )
                                                .and_then(|width| {
                                                    independent_registered_extent(
                                                        height,
                                                        u32::from(vertical_subsampling),
                                                        u32::from(vertical_grid),
                                                        vertical_offset,
                                                    )
                                                    .and_then(|height| {
                                                        usize::try_from(
                                                            u128::from(width) * u128::from(height),
                                                        )
                                                        .map(|pixels| (width, height, pixels))
                                                        .map_err(|_| arithmetic_overflow())
                                                    })
                                                })
                                            };
                                        assert_eq!(
                                            registered_layer_geometry(
                                                width,
                                                height,
                                                &registration,
                                                horizontal_grid,
                                                vertical_grid
                                            ),
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
        }
        assert_eq!(cases, 16384);
    }

    #[test]
    fn chroma_key_preserves_raw_planes_and_replaces_alpha_at_exact_matches() {
        let mut cases = 0;
        for space in [ConvertedColorSpace::Grayscale, ConvertedColorSpace::Srgb] {
            for width in 0..=2 {
                for height in 0..=2 {
                    let pixels = usize::try_from(width * height).unwrap();
                    for channels in 0..=3 {
                        for missing in 0..=channels {
                            let colors = (0..channels)
                                .map(|channel| {
                                    (0..pixels.saturating_sub(usize::from(channel < missing)))
                                        .map(|pixel| if pixel % 2 == 0 { 17 } else { u16::MAX })
                                        .collect::<Vec<_>>()
                                })
                                .collect::<Vec<_>>();
                            for key in [0, 17, u16::MAX] {
                                for key_count in 0..=channels + 1 {
                                    let keys = vec![key; key_count];
                                    for prior_alpha in [
                                        None,
                                        Some((vec![], false)),
                                        Some((vec![123, 456, 789], true)),
                                    ] {
                                        let mut layer = OwnedLayer {
                                            width,
                                            height,
                                            color_space: space,
                                            colors: colors.clone(),
                                            alpha: prior_alpha.clone(),
                                        };
                                        let result = apply_chroma_key(&mut layer, &keys);
                                        assert_eq!(layer.width, width);
                                        assert_eq!(layer.height, height);
                                        assert_eq!(layer.color_space, space);
                                        assert_eq!(layer.colors, colors);
                                        if key_count != channels {
                                            assert_eq!(result, Err(invalid_layer()));
                                            assert_eq!(layer.alpha, prior_alpha);
                                        } else {
                                            result.unwrap();
                                            let transparent = (0..pixels)
                                                .filter(|&pixel| {
                                                    colors
                                                        .iter()
                                                        .all(|plane| plane.get(pixel) == Some(&key))
                                                })
                                                .collect::<std::collections::BTreeSet<_>>();
                                            let expected = (0..pixels)
                                                .map(|pixel| {
                                                    if transparent.contains(&pixel) {
                                                        0
                                                    } else {
                                                        u16::MAX
                                                    }
                                                })
                                                .collect::<Vec<_>>();
                                            assert_eq!(layer.alpha, Some((expected, false)));
                                        }
                                        cases += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 6480);
    }

    #[test]
    fn chroma_key_retains_zero_geometry_and_all_u16_key_values() {
        for sample in 0..=u16::MAX {
            for key in [sample, sample.wrapping_add(1)] {
                let mut layer = OwnedLayer {
                    width: 1,
                    height: 1,
                    color_space: ConvertedColorSpace::Srgb,
                    colors: vec![vec![sample]],
                    alpha: Some((vec![42], true)),
                };
                apply_chroma_key(&mut layer, &[key]).unwrap();
                assert_eq!(
                    layer.alpha,
                    Some((vec![if sample == key { 0 } else { u16::MAX }], false))
                );
                assert_eq!(layer.colors, vec![vec![sample]]);
            }
        }
        let mut layer = OwnedLayer {
            width: u32::MAX,
            height: 0,
            color_space: ConvertedColorSpace::Grayscale,
            colors: vec![vec![]],
            alpha: Some((vec![1, 2], true)),
        };
        apply_chroma_key(&mut layer, &[0]).unwrap();
        assert_eq!(layer.alpha, Some((vec![], false)));
        layer.height = u32::MAX;
        assert_eq!(apply_chroma_key(&mut layer, &[]), Err(invalid_layer()));
        assert_eq!(layer.alpha, Some((vec![], false)));
    }

    fn visit_channel_permutations(
        order: &mut [usize],
        fixed: usize,
        visit: &mut impl FnMut(&[usize]),
    ) {
        if fixed == order.len() {
            visit(order);
            return;
        }
        for index in fixed..order.len() {
            order.swap(fixed, index);
            visit_channel_permutations(order, fixed + 1, visit);
            order.swap(fixed, index);
        }
    }

    #[test]
    fn layer_input_permutations_preserve_complete_planes_and_metadata() {
        let expected_colors = [vec![101, 103], vec![211, 223], vec![307, 311]];
        let first_alpha = vec![1_u16, 40_001];
        let second_alpha = vec![32_768_u16, 50_003];
        let expected_alpha = first_alpha
            .iter()
            .zip(&second_alpha)
            .map(|(&first, &second)| {
                u16::try_from((u128::from(first) * u128::from(second) + 32_767) / 65_535).unwrap()
            })
            .collect::<Vec<_>>();
        let mut cases = 0;
        for association in [
            ChannelAssociation::WholeImage,
            ChannelAssociation::Color(1),
            ChannelAssociation::Unassociated,
        ] {
            for first_premultiplied in [false, true] {
                for second_premultiplied in [false, true] {
                    let channels = [
                        (ConvertedChannelType::Red, expected_colors[0].clone()),
                        (ConvertedChannelType::Green, expected_colors[1].clone()),
                        (ConvertedChannelType::Blue, expected_colors[2].clone()),
                        (
                            ConvertedChannelType::Alpha {
                                premultiplied: first_premultiplied,
                                association,
                            },
                            first_alpha.clone(),
                        ),
                        (
                            ConvertedChannelType::Alpha {
                                premultiplied: second_premultiplied,
                                association,
                            },
                            second_alpha.clone(),
                        ),
                    ];
                    visit_channel_permutations(&mut [0, 1, 2, 3, 4], 0, &mut |order| {
                        let image = ConvertedImage::from_test_channels(
                            2,
                            1,
                            ConvertedColorSpace::Srgb,
                            order.iter().map(|&index| channels[index].clone()).collect(),
                        );
                        let borrowed = layer_channels(&image).unwrap();
                        assert_eq!((borrowed.width, borrowed.height), (2, 1));
                        assert_eq!(
                            borrowed.colors,
                            expected_colors
                                .iter()
                                .map(Vec::as_slice)
                                .collect::<Vec<_>>(),
                        );
                        assert_eq!(borrowed.alpha, Some((expected_alpha.clone(), false)));
                        let owned = owned_layer_from_image(&image).unwrap();
                        drop(image);
                        assert_eq!((owned.width, owned.height), (2, 1));
                        assert_eq!(owned.color_space, ConvertedColorSpace::Srgb);
                        assert_eq!(owned.colors, expected_colors);
                        assert_eq!(owned.alpha, Some((expected_alpha.clone(), false)));
                        cases += 1;
                    });
                }
            }
        }
        assert_eq!(cases, 1_440);
    }

    #[test]
    fn layer_input_absent_and_single_alpha_preserve_representation_and_color_aliases() {
        for space in [ConvertedColorSpace::Grayscale, ConvertedColorSpace::Srgb] {
            for first_kind in [ConvertedChannelType::Gray, ConvertedChannelType::Red] {
                let mut colors = vec![(first_kind, vec![17, 19])];
                if space == ConvertedColorSpace::Srgb {
                    colors.push((ConvertedChannelType::Blue, vec![29, 31]));
                    colors.push((ConvertedChannelType::Green, vec![23, 27]));
                }
                let image = ConvertedImage::from_test_channels(2, 1, space, colors.clone());
                let absent = owned_layer_from_image(&image).unwrap();
                assert_eq!(absent.color_space, space);
                assert_eq!(absent.alpha, None);
                let expected = if space == ConvertedColorSpace::Srgb {
                    vec![vec![17, 19], vec![23, 27], vec![29, 31]]
                } else {
                    vec![vec![17, 19]]
                };
                assert_eq!(absent.colors, expected);
                for premultiplied in [false, true] {
                    for position in 0..=colors.len() {
                        let mut with_alpha = colors.clone();
                        with_alpha.insert(
                            position,
                            (
                                ConvertedChannelType::Alpha {
                                    premultiplied,
                                    association: ChannelAssociation::WholeImage,
                                },
                                vec![0, u16::MAX],
                            ),
                        );
                        let image = ConvertedImage::from_test_channels(2, 1, space, with_alpha);
                        let layer = owned_layer_from_image(&image).unwrap();
                        assert_eq!(layer.colors, expected);
                        assert_eq!(layer.alpha, Some((vec![0, u16::MAX], premultiplied)));
                    }
                }
            }
        }
    }

    #[test]
    fn layer_input_alpha_combination_rounds_each_ordered_step() {
        let construct = |values: &[u16]| {
            let mut channels = vec![(ConvertedChannelType::Gray, vec![0])];
            channels.extend(values.iter().map(|&value| {
                (
                    ConvertedChannelType::Alpha {
                        premultiplied: true,
                        association: ChannelAssociation::WholeImage,
                    },
                    vec![value],
                )
            }));
            ConvertedImage::from_test_channels(1, 1, ConvertedColorSpace::Grayscale, channels)
        };
        let first = owned_layer_from_image(&construct(&[1, 32_768, 32_768])).unwrap();
        let second = owned_layer_from_image(&construct(&[32_768, 32_768, 1])).unwrap();
        assert_eq!(first.alpha, Some((vec![1], false)));
        assert_eq!(second.alpha, Some((vec![0], false)));
    }

    #[test]
    fn layer_input_rejects_missing_duplicate_out_of_range_and_malformed_planes() {
        let alpha = ConvertedChannelType::Alpha {
            premultiplied: false,
            association: ChannelAssociation::WholeImage,
        };
        let invalid = DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidBoxContents,
        };
        let cases = [
            (ConvertedColorSpace::Grayscale, vec![]),
            (ConvertedColorSpace::Grayscale, vec![(alpha, vec![1, 2])]),
            (
                ConvertedColorSpace::Grayscale,
                vec![
                    (ConvertedChannelType::Gray, vec![1, 2]),
                    (ConvertedChannelType::Red, vec![3, 4]),
                ],
            ),
            (
                ConvertedColorSpace::Grayscale,
                vec![(ConvertedChannelType::Green, vec![1, 2])],
            ),
            (
                ConvertedColorSpace::Grayscale,
                vec![(ConvertedChannelType::Blue, vec![1, 2])],
            ),
            (
                ConvertedColorSpace::Grayscale,
                vec![(ConvertedChannelType::Gray, vec![1])],
            ),
            (
                ConvertedColorSpace::Grayscale,
                vec![(ConvertedChannelType::Gray, vec![1, 2, 3])],
            ),
            (
                ConvertedColorSpace::Grayscale,
                vec![(ConvertedChannelType::Gray, vec![1, 2]), (alpha, vec![])],
            ),
            (
                ConvertedColorSpace::Grayscale,
                vec![
                    (ConvertedChannelType::Gray, vec![1, 2]),
                    (alpha, vec![1, 2]),
                    (alpha, vec![1]),
                ],
            ),
            (
                ConvertedColorSpace::Srgb,
                vec![
                    (ConvertedChannelType::Red, vec![1, 2]),
                    (ConvertedChannelType::Green, vec![3, 4]),
                ],
            ),
            (
                ConvertedColorSpace::Srgb,
                vec![
                    (ConvertedChannelType::Red, vec![1, 2]),
                    (ConvertedChannelType::Green, vec![3]),
                    (ConvertedChannelType::Blue, vec![5, 6]),
                ],
            ),
        ];
        for (space, channels) in cases {
            let image = ConvertedImage::from_test_channels(2, 1, space, channels);
            assert_eq!(layer_channels(&image).err(), Some(invalid));
            assert_eq!(owned_layer_from_image(&image).err(), Some(invalid));
        }
        let empty = ConvertedImage::from_test_channels(
            0,
            u32::MAX,
            ConvertedColorSpace::Grayscale,
            vec![(ConvertedChannelType::Gray, vec![]), (alpha, vec![])],
        );
        let layer = owned_layer_from_image(&empty).unwrap();
        assert_eq!((layer.width, layer.height), (0, u32::MAX));
        assert_eq!(layer.colors, vec![Vec::<u16>::new()]);
        assert_eq!(layer.alpha, Some((vec![], false)));
    }

    #[test]
    fn normalized_alpha_products_match_wide_integer_reference_at_boundaries() {
        for first in 0..=u16::MAX {
            for second in [0, 1, 32_767, 32_768, 65_534, u16::MAX] {
                let expected =
                    u16::try_from((u128::from(first) * u128::from(second) + 32_767) / 65_535)
                        .unwrap();
                assert_eq!(
                    crate::refinement::normalized_sample_product(first, second),
                    Some(expected),
                );
            }
        }
    }

    #[test]
    fn complete_planar_transition_matches_independent_read_rational_and_store_oracle() {
        let shapes: [&[usize]; 8] = [
            &[],
            &[0],
            &[1],
            &[2],
            &[2, 1, 2],
            &[2, 2, 0],
            &[2, 2, 2],
            &[2, 2, 2, 2],
        ];
        let planes = |shape: &[usize], base: u16| {
            shape
                .iter()
                .enumerate()
                .map(|(channel, &len)| {
                    (0..len)
                        .map(|i| base + u16::try_from(10 * channel + i).unwrap())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        };
        let alphas = [
            None,
            Some((vec![], false)),
            Some((vec![], true)),
            Some((vec![41], false)),
            Some((vec![41], true)),
            Some((vec![41, 43], false)),
            Some((vec![41, 43], true)),
            Some((vec![0, 1], false)),
            Some((vec![0, 1], true)),
            Some((vec![32_768, u16::MAX], false)),
            Some((vec![32_768, u16::MAX], true)),
            Some((vec![u16::MAX, u16::MAX], false)),
            Some((vec![u16::MAX, u16::MAX], true)),
        ];
        let spaces = [ConvertedColorSpace::Grayscale, ConvertedColorSpace::Srgb];
        let mut cases = 0;
        for source_shape in shapes {
            for destination_shape in shapes {
                for source_alpha in &alphas {
                    for alpha_length in 0..=2 {
                        for source_space in spaces {
                            for output_space in spaces {
                                let source = OwnedLayer {
                                    width: 2,
                                    height: 1,
                                    color_space: source_space,
                                    colors: planes(source_shape, 100),
                                    alpha: source_alpha.clone(),
                                };
                                let colors = planes(destination_shape, 200);
                                let alpha = vec![47; alpha_length];
                                for source_index in [0, 1, 2, usize::MAX] {
                                    for destination_index in [0, 1, 2, usize::MAX] {
                                        let expected = (|| {
                                            if colors.len() > 3 {
                                                return None;
                                            }
                                            let mut input = [0; 3];
                                            let mut destination = [0; 3];
                                            for (channel, samples) in colors.iter().enumerate() {
                                                let selected = if output_space
                                                    == ConvertedColorSpace::Srgb
                                                    && source_space
                                                        == ConvertedColorSpace::Grayscale
                                                {
                                                    0
                                                } else {
                                                    channel
                                                };
                                                input[channel] = *source
                                                    .colors
                                                    .get(selected)?
                                                    .get(source_index)?;
                                                destination[channel] =
                                                    *samples.get(destination_index)?;
                                            }
                                            let (a, premultiplied) = match &source.alpha {
                                                Some((samples, flag)) => {
                                                    (*samples.get(source_index)?, *flag)
                                                }
                                                None => (u16::MAX, false),
                                            };
                                            Some((
                                                input,
                                                destination,
                                                a,
                                                *alpha.get(destination_index)?,
                                                premultiplied,
                                            ))
                                        })();
                                        assert_eq!(
                                            gather_composition_pixel(
                                                &source.colors,
                                                source.alpha.as_ref().map(|(samples, flag)| (
                                                    samples.as_slice(),
                                                    *flag
                                                )),
                                                &colors,
                                                &alpha,
                                                source_index,
                                                destination_index,
                                                output_space == ConvertedColorSpace::Srgb
                                                    && source_space
                                                        == ConvertedColorSpace::Grayscale,
                                            ),
                                            expected
                                        );
                                        let mut expected_colors = colors.clone();
                                        let mut expected_alpha = alpha.clone();
                                        let composed = match expected {
                                            Some((s, d, sa, da, premultiplied))
                                                if !premultiplied
                                                    || s[..colors.len()]
                                                        .iter()
                                                        .all(|&sample| sample <= sa) =>
                                            {
                                                let maximum = u128::from(u16::MAX);
                                                let sa = u128::from(sa);
                                                let da = u128::from(da);
                                                let denominator =
                                                    sa * maximum + da * (maximum - sa);
                                                for (channel, samples) in
                                                    expected_colors.iter_mut().enumerate()
                                                {
                                                    let source = u128::from(s[channel]);
                                                    let numerator = if premultiplied {
                                                        source * maximum * maximum
                                                    } else {
                                                        source * sa * maximum
                                                    } + u128::from(d[channel])
                                                        * da
                                                        * (maximum - sa);
                                                    samples[destination_index] =
                                                        u16::try_from(if denominator == 0 {
                                                            0
                                                        } else {
                                                            (numerator + denominator / 2)
                                                                / denominator
                                                        })
                                                        .unwrap();
                                                }
                                                expected_alpha[destination_index] = u16::try_from(
                                                    (denominator + maximum / 2) / maximum,
                                                )
                                                .unwrap();
                                                true
                                            }
                                            _ => false,
                                        };
                                        let mut actual_colors = colors.clone();
                                        let mut actual_alpha = alpha.clone();
                                        let actual = compose_planar_pixel(
                                            &source.colors,
                                            source
                                                .alpha
                                                .as_ref()
                                                .map(|(samples, flag)| (samples.as_slice(), *flag)),
                                            &mut actual_colors,
                                            &mut actual_alpha,
                                            source_index,
                                            destination_index,
                                            output_space == ConvertedColorSpace::Srgb
                                                && source_space == ConvertedColorSpace::Grayscale,
                                        );
                                        assert_eq!(actual, composed);
                                        assert_eq!(actual_colors, expected_colors);
                                        assert_eq!(actual_alpha, expected_alpha);
                                        cases += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 159_744);
    }

    #[test]
    fn planar_scatter_matches_exact_success_and_partial_failure_states() {
        let shapes: [&[usize]; 8] = [
            &[],
            &[0],
            &[1],
            &[2],
            &[2, 1, 2],
            &[2, 2, 0],
            &[2, 2, 2],
            &[2, 2, 2, 2],
        ];
        let mut cases = 0;
        for shape in shapes {
            for alpha_length in 0..=2 {
                for index in [0, 1, 2, usize::MAX] {
                    for pixel in [[0; 3], [u16::MAX; 3], [200, 210, 220]] {
                        for alpha in [0, 47, u16::MAX] {
                            let mut colors = shape
                                .iter()
                                .enumerate()
                                .map(|(channel, &len)| {
                                    (0..len)
                                        .map(|i| 200 + u16::try_from(channel * 10 + i).unwrap())
                                        .collect::<Vec<_>>()
                                })
                                .collect::<Vec<_>>();
                            let mut alphas = vec![47; alpha_length];
                            let mut expected_colors = colors.clone();
                            let mut expected_alpha = alphas.clone();
                            let mut stored = colors.len() <= 3;
                            if stored {
                                for (channel, samples) in expected_colors.iter_mut().enumerate() {
                                    match samples.get_mut(index) {
                                        Some(sample) => *sample = pixel[channel],
                                        None => {
                                            stored = false;
                                            break;
                                        }
                                    }
                                }
                                if stored {
                                    match expected_alpha.get_mut(index) {
                                        Some(sample) => *sample = alpha,
                                        None => stored = false,
                                    }
                                }
                            }
                            assert_eq!(
                                scatter_composition_pixel(
                                    &mut colors,
                                    &mut alphas,
                                    index,
                                    pixel,
                                    alpha,
                                ),
                                stored
                            );
                            assert_eq!(colors, expected_colors);
                            assert_eq!(alphas, expected_alpha);
                            cases += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 864);
    }

    #[test]
    fn missing_late_planar_sample_preserves_current_pixel_and_work_order() {
        for missing_source in [false, true] {
            let mut source = OwnedLayer {
                width: 2,
                height: 1,
                color_space: ConvertedColorSpace::Srgb,
                colors: vec![vec![101, 201], vec![102, 202], vec![103, 203]],
                alpha: None,
            };
            let mut colors = vec![vec![0, 17], vec![0, 23], vec![0, 29]];
            if missing_source {
                source.colors[2].truncate(1);
            } else {
                colors[2].truncate(1);
            }
            let mut expected = colors.clone();
            for (channel, samples) in expected.iter_mut().enumerate() {
                samples[0] = 101 + u16::try_from(channel).unwrap();
            }
            let instruction = JpxInstructionInfo {
                layer_index: 0,
                target_x: 0,
                target_y: 0,
                target_width: 2,
                target_height: 1,
                source_x: 0,
                source_y: 0,
                source_width: 0,
                source_height: 0,
                persistent: true,
                next_reuse: 0,
            };
            let mut alpha = vec![0, 31];
            let mut work = 0;
            assert_eq!(
                composite_placed_layer(
                    2,
                    1,
                    ConvertedColorSpace::Srgb,
                    &source,
                    instruction,
                    &mut colors,
                    &mut alpha,
                    &mut work,
                    &ResourceLimits::default(),
                ),
                Err(invalid_layer())
            );
            assert_eq!(colors, expected);
            assert_eq!(alpha, [u16::MAX, 31]);
            assert_eq!(work, 4);
        }
    }

    #[test]
    fn complete_pixel_stage_matches_independent_rational_rounding() {
        let maximum = u128::from(u16::MAX);
        let nearest = |n: u128, d: u128| {
            if d == 0 {
                0
            } else {
                u16::try_from(n / d + u128::from(2 * (n % d) >= d)).unwrap()
            }
        };
        for channels in 0..=4 {
            for premultiplied in [false, true] {
                for source_alpha in [0, 1, 32_767, 32_768, u16::MAX] {
                    for destination_alpha in [0, 1, 32_767, 32_768, u16::MAX] {
                        for source in [[0, source_alpha / 2, source_alpha], [u16::MAX, 1, 32_768]] {
                            for destination in [[0, 1, u16::MAX], [u16::MAX, 32_768, 0]] {
                                let actual = crate::refinement::source_over_pixel(
                                    source,
                                    destination,
                                    source_alpha,
                                    destination_alpha,
                                    premultiplied,
                                    channels,
                                );
                                if channels > 3
                                    || (premultiplied
                                        && source[..channels]
                                            .iter()
                                            .any(|value| *value > source_alpha))
                                {
                                    assert_eq!(actual, None);
                                    continue;
                                }
                                let a = u128::from(source_alpha);
                                let d = u128::from(destination_alpha);
                                let alpha_numerator = a * maximum + d * (maximum - a);
                                let mut expected = destination;
                                for i in 0..channels {
                                    let s = u128::from(source[i]);
                                    let c = u128::from(destination[i]);
                                    let source_term = if premultiplied {
                                        s * maximum * maximum
                                    } else {
                                        s * a * maximum
                                    };
                                    expected[i] = nearest(
                                        source_term + c * d * (maximum - a),
                                        alpha_numerator,
                                    );
                                }
                                assert_eq!(
                                    actual,
                                    Some((expected, nearest(alpha_numerator, maximum)))
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn invalid_late_channel_rejects_only_the_current_pixel_before_any_store() {
        let source = OwnedLayer {
            width: 2,
            height: 1,
            color_space: ConvertedColorSpace::Srgb,
            colors: vec![vec![32_768, 32_768], vec![0, 1], vec![16_384, 32_769]],
            alpha: Some((vec![32_768, 32_768], true)),
        };
        let instruction = JpxInstructionInfo {
            layer_index: 0,
            target_x: 0,
            target_y: 0,
            target_width: 2,
            target_height: 1,
            source_x: 0,
            source_y: 0,
            source_width: 0,
            source_height: 0,
            persistent: true,
            next_reuse: 0,
        };
        let mut colors = vec![vec![0, 17], vec![0, 23], vec![0, 29]];
        let mut alpha = vec![0, 31];
        let mut work = 0;
        assert_eq!(
            composite_placed_layer(
                2,
                1,
                ConvertedColorSpace::Srgb,
                &source,
                instruction,
                &mut colors,
                &mut alpha,
                &mut work,
                &ResourceLimits::default()
            ),
            Err(invalid_layer())
        );
        assert_eq!(colors, [vec![u16::MAX, 17], vec![0, 23], vec![32_768, 29]]);
        assert_eq!(alpha, [32_768, 31]);
        assert_eq!(work, 4);
    }

    #[test]
    fn composition_mapped_offsets_match_wide_floor_division() {
        let check = |position: u32, source: u32, target: u32| {
            let mapped = crate::refinement::composition_mapped_offset(position, source, target);
            let numerator = u128::from(position) * u128::from(source);
            let denominator = u128::from(target);
            assert_eq!(u128::from(mapped), numerator / denominator);
            assert!(u128::from(mapped) * denominator <= numerator);
            assert!(numerator < (u128::from(mapped) + 1) * denominator);
            if position < target && source > 0 {
                assert!(mapped < u64::from(source));
            }
        };
        for source in 0..=16 {
            for target in 1..=16 {
                for position in 0..=target + 1 {
                    check(position, source, target);
                }
            }
        }
        for position in [0, 1, 2, 65_535, 65_536, u32::MAX - 1, u32::MAX] {
            for source in [0, 1, 2, 65_535, 65_536, u32::MAX - 1, u32::MAX] {
                for target in [1, 2, 65_535, 65_536, u32::MAX] {
                    check(position, source, target);
                }
            }
        }
    }

    #[test]
    fn composition_pixel_indices_match_wide_row_major_arithmetic() {
        for width in [0, 1, 2, 65_535, 65_536, u32::MAX - 1, u32::MAX] {
            for x in [0, 1, 2, 65_535, 65_536, u32::MAX - 1, u32::MAX] {
                for y in [0, 1, 2, 65_535, 65_536, u32::MAX - 1, u32::MAX] {
                    let wide = u128::from(y) * u128::from(width) + u128::from(x);
                    assert!(wide <= u128::from(u64::MAX));
                    let expected = usize::try_from(wide).ok();
                    assert_eq!(
                        crate::refinement::composition_pixel_index(width, x, y),
                        expected
                    );
                    let actual = index_of(width, x, y);
                    assert_eq!(actual.as_ref().ok().copied(), expected);
                    if expected.is_none() {
                        assert_eq!(actual, Err(arithmetic_overflow()));
                    }
                }
            }
        }
        for width in 1..=16 {
            for height in 1..=16 {
                for y in 0..height {
                    for x in 0..width {
                        let index = index_of(width, x, y).unwrap();
                        assert!((index as u128) < u128::from(width) * u128::from(height));
                        assert_eq!(
                            u32::try_from(index / usize::try_from(width).unwrap()).unwrap(),
                            y
                        );
                        assert_eq!(
                            u32::try_from(index % usize::try_from(width).unwrap()).unwrap(),
                            x
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn placed_composition_scaled_crop_and_clipping_match_coordinate_oracle() {
        let source_values: Vec<u16> = (0..20).map(|i| i * 1999 + 31).collect();
        let source = OwnedLayer {
            width: 5,
            height: 4,
            color_space: ConvertedColorSpace::Grayscale,
            colors: vec![source_values.clone()],
            alpha: None,
        };
        let base = JpxInstructionInfo {
            layer_index: 0,
            target_x: 4,
            target_y: 3,
            target_width: 6,
            target_height: 4,
            source_x: 1,
            source_y: 1,
            source_width: 3,
            source_height: 2,
            persistent: true,
            next_reuse: 0,
        };
        for (instruction, crop) in [
            (base, [1_u32, 1, 3, 2]),
            (
                JpxInstructionInfo {
                    source_x: 4,
                    source_y: 3,
                    source_width: 99,
                    source_height: 99,
                    target_width: u32::MAX,
                    target_height: u32::MAX,
                    ..base
                },
                [4, 3, 1, 1],
            ),
            (
                JpxInstructionInfo {
                    source_y: 0,
                    source_width: 0,
                    source_height: 0,
                    target_x: 0,
                    target_y: 0,
                    target_width: 2,
                    target_height: 2,
                    ..base
                },
                [1, 0, 4, 4],
            ),
            (
                JpxInstructionInfo {
                    source_x: 0,
                    source_y: 0,
                    source_width: 0,
                    source_height: 0,
                    target_x: 1,
                    target_y: 1,
                    target_width: 5,
                    target_height: 4,
                    ..base
                },
                [0, 0, 5, 4],
            ),
        ] {
            let before: Vec<Vec<u16>> = (0..3)
                .map(|channel| (0..42).map(|i| 10_000 + channel * 1000 + i).collect())
                .collect();
            let before_alpha: Vec<u16> = (0..42).map(|i| 3 + i * 7).collect();
            let mut colors = before.clone();
            let mut alpha = before_alpha.clone();
            let mut work = 7;
            composite_placed_layer(
                7,
                6,
                ConvertedColorSpace::Srgb,
                &source,
                instruction,
                &mut colors,
                &mut alpha,
                &mut work,
                &ResourceLimits::default(),
            )
            .unwrap();
            let mut copied = 0;
            for y in 0..6_u32 {
                for x in 0..7_u32 {
                    let index = usize::try_from(y * 7 + x).unwrap();
                    let covered = x >= instruction.target_x
                        && y >= instruction.target_y
                        && x - instruction.target_x < instruction.target_width
                        && y - instruction.target_y < instruction.target_height;
                    if covered {
                        let sx = u128::from(crop[0])
                            + u128::from(x - instruction.target_x) * u128::from(crop[2])
                                / u128::from(instruction.target_width);
                        let sy = u128::from(crop[1])
                            + u128::from(y - instruction.target_y) * u128::from(crop[3])
                                / u128::from(instruction.target_height);
                        let sample = source_values[usize::try_from(sy * 5 + sx).unwrap()];
                        for samples in &colors {
                            assert_eq!(samples[index], sample);
                        }
                        assert_eq!(alpha[index], u16::MAX);
                        copied += 1;
                    } else {
                        for (samples, previous) in colors.iter().zip(&before) {
                            assert_eq!(samples[index], previous[index]);
                        }
                        assert_eq!(alpha[index], before_alpha[index]);
                    }
                }
            }
            assert_eq!(work, 7 + copied * 4);
        }
    }

    #[test]
    fn placed_layer_zero_width_clip_does_not_traverse_unvisited_rows() {
        let (sender, receiver) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            let source = OwnedLayer {
                width: 1,
                height: 1,
                color_space: ConvertedColorSpace::Grayscale,
                colors: vec![],
                alpha: Some((vec![], true)),
            };
            let instruction = JpxInstructionInfo {
                layer_index: 0,
                target_x: 1,
                target_y: 0,
                target_width: 1,
                target_height: u32::MAX,
                source_x: 0,
                source_y: 0,
                source_width: 0,
                source_height: 0,
                persistent: true,
                next_reuse: 0,
            };
            let mut colors = vec![vec![17], vec![], vec![23, 29], vec![31]];
            let mut alpha = vec![];
            let mut work = u64::MAX;
            let result = composite_placed_layer(
                1,
                u32::MAX,
                ConvertedColorSpace::Srgb,
                &source,
                instruction,
                &mut colors,
                &mut alpha,
                &mut work,
                &ResourceLimits::default()
                    .with_maximum_work_units(0)
                    .unwrap(),
            );
            sender.send((result, colors, alpha, work)).unwrap();
        });
        let (result, colors, alpha, work) = receiver
            .recv_timeout(std::time::Duration::from_secs(5))
            .expect("an empty clipped rectangle must not traverse unvisited rows");
        worker.join().unwrap();
        assert_eq!(result, Ok(()));
        assert_eq!(colors, [vec![17], vec![], vec![23, 29], vec![31]]);
        assert!(alpha.is_empty());
        assert_eq!(work, u64::MAX);
    }

    #[test]
    fn placed_layer_work_rejections_preserve_post_store_order() {
        let source = OwnedLayer {
            width: 1,
            height: 1,
            color_space: ConvertedColorSpace::Grayscale,
            colors: vec![vec![2_345]],
            alpha: None,
        };
        let instruction = JpxInstructionInfo {
            layer_index: 0,
            target_x: 0,
            target_y: 0,
            target_width: 1,
            target_height: 1,
            source_x: 0,
            source_y: 0,
            source_width: 0,
            source_height: 0,
            persistent: true,
            next_reuse: 0,
        };
        for (initial, limit, expected, final_work) in [
            (u64::MAX, 7, Err(arithmetic_overflow()), u64::MAX),
            (5, 6, Err(DecodeError::limit(Resource::WorkUnits, 6, 7)), 7),
            (5, 7, Ok(()), 7),
        ] {
            let mut colors = vec![vec![111]];
            let mut alpha = vec![0];
            let mut work = initial;
            assert_eq!(
                composite_placed_layer(
                    1,
                    1,
                    ConvertedColorSpace::Grayscale,
                    &source,
                    instruction,
                    &mut colors,
                    &mut alpha,
                    &mut work,
                    &ResourceLimits::default()
                        .with_maximum_work_units(limit)
                        .unwrap(),
                ),
                expected
            );
            assert_eq!(colors, [vec![2_345]]);
            assert_eq!(alpha, [u16::MAX]);
            assert_eq!(work, final_work);
        }
    }

    #[test]
    fn placed_layer_exact_error_precedence_matches_independent_replay() {
        let mut cases = 0;
        for initial_work in [0, 9, u64::MAX - 4, u64::MAX - 3, u64::MAX] {
            for missing_at in 0..=6 {
                for missing_alpha in [false, true] {
                    for limit in [
                        0, 3, 4, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 32, 33, 37,
                    ] {
                        let mut source = OwnedLayer {
                            width: 3,
                            height: 2,
                            color_space: ConvertedColorSpace::Srgb,
                            colors: (0..3)
                                .map(|channel| {
                                    (0..6)
                                        .map(|i| u16::try_from((channel + 1) * 100 + i).unwrap())
                                        .collect::<Vec<_>>()
                                })
                                .collect(),
                            alpha: if missing_alpha {
                                Some((vec![u16::MAX; missing_at], false))
                            } else {
                                None
                            },
                        };
                        if !missing_alpha {
                            source.colors[2].truncate(missing_at);
                        }
                        let instruction = JpxInstructionInfo {
                            layer_index: 0,
                            target_x: 1,
                            target_y: 1,
                            target_width: 3,
                            target_height: 2,
                            source_x: 0,
                            source_y: 0,
                            source_width: 0,
                            source_height: 0,
                            persistent: true,
                            next_reuse: 0,
                        };
                        let mut colors = vec![vec![31; 20], vec![32; 20], vec![33; 20]];
                        let mut alpha = vec![17; 20];
                        let mut expected_colors = colors.clone();
                        let mut expected_alpha = alpha.clone();
                        let mut expected_work = initial_work;
                        let mut expected_result = Ok(());
                        for rank in 0..6 {
                            if rank == missing_at {
                                expected_result = Err(DecodeError::MalformedInput {
                                    offset: 0,
                                    kind: MalformedKind::InvalidBoxContents,
                                });
                                break;
                            }
                            let index = (rank / 3 + 1) * 5 + rank % 3 + 1;
                            for (channel, samples) in expected_colors.iter_mut().enumerate() {
                                samples[index] = source.colors[channel][rank];
                            }
                            expected_alpha[index] = u16::MAX;
                            let wide_work = u128::from(expected_work) + 4;
                            if wide_work > u128::from(u64::MAX) {
                                expected_result = Err(DecodeError::MalformedInput {
                                    offset: 0,
                                    kind: MalformedKind::ArithmeticOverflow,
                                });
                                break;
                            }
                            expected_work = u64::try_from(wide_work).unwrap();
                            if expected_work > limit {
                                expected_result = Err(DecodeError::LimitExceeded {
                                    resource: Resource::WorkUnits,
                                    limit,
                                    actual: expected_work,
                                });
                                break;
                            }
                        }
                        let mut work = initial_work;
                        assert_eq!(
                            composite_placed_layer(
                                5,
                                4,
                                ConvertedColorSpace::Srgb,
                                &source,
                                instruction,
                                &mut colors,
                                &mut alpha,
                                &mut work,
                                &ResourceLimits::default()
                                    .with_maximum_work_units(limit)
                                    .unwrap(),
                            ),
                            expected_result
                        );
                        assert_eq!(colors, expected_colors);
                        assert_eq!(alpha, expected_alpha);
                        assert_eq!(work, expected_work);
                        cases += 1;
                    }
                }
            }
        }
        assert_eq!(cases, 1_260);
    }

    #[test]
    fn placed_layer_failures_preserve_multirow_raster_prefixes() {
        let mut cases = Vec::new();
        for count in 1..=6_usize {
            let work = 9 + u64::try_from(count).unwrap() * 4;
            cases.push((
                count,
                9,
                work - 1,
                false,
                Err(DecodeError::limit(Resource::WorkUnits, work - 1, work)),
                work,
            ));
        }
        cases.push((4, 9, 1_000, true, Err(invalid_layer()), 25));
        cases.push((
            1,
            u64::MAX - 3,
            1_000,
            false,
            Err(arithmetic_overflow()),
            u64::MAX - 3,
        ));
        cases.push((6, 9, 33, false, Ok(()), 33));
        for (stored, initial_work, limit, missing_sample, expected_result, expected_work) in cases {
            let mut source = OwnedLayer {
                width: 3,
                height: 2,
                color_space: ConvertedColorSpace::Srgb,
                colors: (0..3)
                    .map(|channel| {
                        (0..6)
                            .map(|i| u16::try_from((channel + 1) * 100 + i).unwrap())
                            .collect::<Vec<_>>()
                    })
                    .collect(),
                alpha: None,
            };
            if missing_sample {
                source.colors[2].truncate(4);
            }
            let instruction = JpxInstructionInfo {
                layer_index: 0,
                target_x: 1,
                target_y: 1,
                target_width: 3,
                target_height: 2,
                source_x: 0,
                source_y: 0,
                source_width: 0,
                source_height: 0,
                persistent: true,
                next_reuse: 0,
            };
            let mut colors = vec![vec![31; 20], vec![32; 20], vec![33; 20]];
            let mut alpha = vec![17; 20];
            let mut expected_colors = colors.clone();
            let mut expected_alpha = alpha.clone();
            for rank in 0..stored {
                let destination = (rank / 3 + 1) * 5 + rank % 3 + 1;
                for (channel, samples) in expected_colors.iter_mut().enumerate() {
                    samples[destination] = source.colors[channel][rank];
                }
                expected_alpha[destination] = u16::MAX;
            }
            let mut work = initial_work;
            assert_eq!(
                composite_placed_layer(
                    5,
                    4,
                    ConvertedColorSpace::Srgb,
                    &source,
                    instruction,
                    &mut colors,
                    &mut alpha,
                    &mut work,
                    &ResourceLimits::default()
                        .with_maximum_work_units(limit)
                        .unwrap(),
                ),
                expected_result
            );
            assert_eq!(colors, expected_colors);
            assert_eq!(alpha, expected_alpha);
            assert_eq!(work, expected_work);
        }
    }

    #[test]
    fn placed_composition_preserves_empty_zero_target_and_off_canvas_behavior() {
        let source = OwnedLayer {
            width: 1,
            height: 1,
            color_space: ConvertedColorSpace::Grayscale,
            colors: vec![vec![123]],
            alpha: None,
        };
        let base = JpxInstructionInfo {
            layer_index: 0,
            target_x: 0,
            target_y: 0,
            target_width: 1,
            target_height: 1,
            source_x: 0,
            source_y: 0,
            source_width: 0,
            source_height: 0,
            persistent: true,
            next_reuse: 0,
        };
        for (instruction, expected) in [
            (
                JpxInstructionInfo {
                    source_x: 1,
                    target_width: 0,
                    target_height: 0,
                    ..base
                },
                Ok(()),
            ),
            (
                JpxInstructionInfo {
                    target_width: 0,
                    ..base
                },
                Err(invalid_layer()),
            ),
            (
                JpxInstructionInfo {
                    target_height: 0,
                    ..base
                },
                Err(invalid_layer()),
            ),
            (
                JpxInstructionInfo {
                    target_x: u32::MAX,
                    ..base
                },
                Ok(()),
            ),
            (
                JpxInstructionInfo {
                    target_y: u32::MAX,
                    ..base
                },
                Ok(()),
            ),
        ] {
            let mut colors = vec![vec![17]];
            let mut alpha = vec![23];
            let mut work = 29;
            assert_eq!(
                composite_placed_layer(
                    1,
                    1,
                    ConvertedColorSpace::Grayscale,
                    &source,
                    instruction,
                    &mut colors,
                    &mut alpha,
                    &mut work,
                    &ResourceLimits::default()
                ),
                expected
            );
            assert_eq!(colors, [vec![17]]);
            assert_eq!(alpha, [23]);
            assert_eq!(work, 29);
        }
    }

    #[test]
    fn composition_store_has_exact_single_slot_effect() {
        for length in 0..=8 {
            let before: Vec<u16> = (0..length)
                .map(|i| u16::try_from(i).unwrap() * 4093)
                .collect();
            for index in (0..length + 2).chain(std::iter::once(usize::MAX)) {
                for value in [0, 1, 255, 32_768, u16::MAX] {
                    let mut samples = before.clone();
                    let stored =
                        crate::refinement::try_store_composition_sample(&mut samples, index, value);
                    let mut expected = before.clone();
                    if index < length {
                        expected[index] = value;
                    }
                    assert_eq!(stored, index < length);
                    assert_eq!(samples.len(), before.len());
                    assert_eq!(samples, expected);
                }
            }
        }
    }

    #[test]
    fn composition_store_respects_subslice_offsets_and_repeated_writes() {
        let mut samples = vec![111, 222, 3, 4, 5, 666, 777];
        assert!(crate::refinement::try_store_composition_sample(
            &mut samples[2..5],
            0,
            u16::MAX
        ));
        assert!(crate::refinement::try_store_composition_sample(
            &mut samples[2..5],
            2,
            0
        ));
        assert!(!crate::refinement::try_store_composition_sample(
            &mut samples[2..5],
            3,
            999
        ));
        assert!(!crate::refinement::try_store_composition_sample(
            &mut samples[2..5],
            usize::MAX,
            999
        ));
        assert_eq!(samples, [111, 222, u16::MAX, 4, 0, 666, 777]);
        assert!(crate::refinement::try_store_composition_sample(
            &mut samples[2..5],
            0,
            17
        ));
        assert_eq!(samples, [111, 222, 17, 4, 0, 666, 777]);
    }

    #[test]
    fn placed_source_over_samples_match_wide_rational_rounding_and_preserve_guards() {
        let maximum = u128::from(u16::MAX);
        let nearest = |numerator: u128, denominator: u128| {
            if denominator == 0 {
                0
            } else {
                u16::try_from(
                    numerator / denominator
                        + u128::from(2 * (numerator % denominator) >= denominator),
                )
                .unwrap()
            }
        };
        let instruction = JpxInstructionInfo {
            layer_index: 0,
            target_x: 1,
            target_y: 0,
            target_width: 5,
            target_height: 1,
            source_x: 0,
            source_y: 0,
            source_width: 0,
            source_height: 0,
            persistent: true,
            next_reuse: 0,
        };
        for premultiplied in [false, true] {
            let samples = if premultiplied {
                vec![0, 1, 16_384, 12_345, 0]
            } else {
                vec![u16::MAX, 1, 32_767, 12_345, 0]
            };
            let source_alpha = vec![0, 1, 32_768, u16::MAX, 32_767];
            let mut source = OwnedLayer {
                width: 5,
                height: 1,
                color_space: ConvertedColorSpace::Grayscale,
                colors: vec![samples.clone()],
                alpha: Some((source_alpha.clone(), premultiplied)),
            };
            let before_colors = vec![
                vec![7, u16::MAX, 3, 32_768, 34_567, 60_000, 11],
                vec![13, 1, u16::MAX, 123, 45_678, 2, 19],
                vec![17, 32_767, 1, 54_321, 0, u16::MAX, 23],
            ];
            let before_alpha = vec![17, 0, u16::MAX, 32_767, 0, 12_345, 19];
            let mut colors = before_colors.clone();
            let mut alpha = before_alpha.clone();
            let mut work = 0;
            composite_placed_layer(
                7,
                1,
                ConvertedColorSpace::Srgb,
                &source,
                instruction,
                &mut colors,
                &mut alpha,
                &mut work,
                &ResourceLimits::default(),
            )
            .unwrap();
            assert_eq!(work, 20);
            for index in 0..7 {
                if index == 0 || index == 6 {
                    assert_eq!(alpha[index], before_alpha[index]);
                    for channel in 0..3 {
                        assert_eq!(colors[channel][index], before_colors[channel][index]);
                    }
                    continue;
                }
                let a = u128::from(source_alpha[index - 1]);
                let d = u128::from(before_alpha[index]);
                let alpha_numerator = a * maximum + d * (maximum - a);
                assert_eq!(alpha[index], nearest(alpha_numerator, maximum));
                for channel in 0..3 {
                    let s = u128::from(samples[index - 1]);
                    let c = u128::from(before_colors[channel][index]);
                    let source_term = if premultiplied {
                        s * maximum * maximum
                    } else {
                        s * a * maximum
                    };
                    assert_eq!(
                        colors[channel][index],
                        nearest(source_term + c * d * (maximum - a), alpha_numerator)
                    );
                }
            }
            if premultiplied {
                source.colors[0][0] = 1;
                let before_invalid_colors = colors.clone();
                let before_invalid_alpha = alpha.clone();
                assert_eq!(
                    composite_placed_layer(
                        7,
                        1,
                        ConvertedColorSpace::Srgb,
                        &source,
                        instruction,
                        &mut colors,
                        &mut alpha,
                        &mut work,
                        &ResourceLimits::default(),
                    ),
                    Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents)),
                );
                assert_eq!(colors, before_invalid_colors);
                assert_eq!(alpha, before_invalid_alpha);
                assert_eq!(work, 20);
            }
        }
    }

    #[test]
    fn source_over_alpha_bounds_cover_every_source_alpha() {
        let maximum = u64::from(u16::MAX);
        for source_alpha in 0..=u16::MAX {
            for destination_alpha in [0, 1, 2, 32_767, 32_768, 65_534, u16::MAX] {
                let numerator = source_over_alpha_numerator(source_alpha, destination_alpha);
                let expected = u128::from(source_alpha) * u128::from(u16::MAX)
                    + u128::from(destination_alpha) * u128::from(u16::MAX - source_alpha);
                assert_eq!(u128::from(numerator), expected);
                assert!(numerator <= maximum * maximum);
                assert_eq!(numerator == 0, source_alpha == 0 && destination_alpha == 0);
                assert!(source_over_rounded_ratio(numerator, maximum) <= u128::from(u16::MAX));
            }
        }
    }

    #[test]
    fn source_over_color_bounds_and_representations_match_wide_arithmetic() {
        let values = [
            0,
            1,
            2,
            127,
            128,
            255,
            256,
            32_767,
            32_768,
            65_534,
            u16::MAX,
        ];
        let maximum = u128::from(u16::MAX);
        for source in values {
            for destination in values {
                for source_alpha in values {
                    for destination_alpha in values {
                        let alpha = source_over_alpha_numerator(source_alpha, destination_alpha);
                        for premultiplied in [false, true] {
                            let numerator = source_over_color_numerator(
                                source,
                                destination,
                                source_alpha,
                                destination_alpha,
                                premultiplied,
                            );
                            let source_term = if premultiplied {
                                u128::from(source) * maximum * maximum
                            } else {
                                u128::from(source) * u128::from(source_alpha) * maximum
                            };
                            let expected = source_term
                                + u128::from(destination)
                                    * u128::from(destination_alpha)
                                    * u128::from(u16::MAX - source_alpha);
                            assert_eq!(u128::from(numerator), expected);
                            if !premultiplied || source <= source_alpha {
                                assert!(expected <= maximum * u128::from(alpha));
                                let output = source_over_rounded_ratio(numerator, alpha);
                                assert!(output <= maximum);
                                if source_alpha == u16::MAX {
                                    assert_eq!(output, u128::from(source));
                                }
                                if source_alpha == 0 {
                                    assert_eq!(
                                        output,
                                        if destination_alpha == 0 {
                                            0
                                        } else {
                                            u128::from(destination)
                                        }
                                    );
                                }
                            }
                        }
                        if source == 0 || source == u16::MAX {
                            let premultiplied_source = if source == 0 { 0 } else { source_alpha };
                            assert_eq!(
                                source_over_color_numerator(
                                    source,
                                    destination,
                                    source_alpha,
                                    destination_alpha,
                                    false,
                                ),
                                source_over_color_numerator(
                                    premultiplied_source,
                                    destination,
                                    source_alpha,
                                    destination_alpha,
                                    true,
                                ),
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn source_over_rounding_handles_ties_zero_and_full_width_inputs() {
        let values = [0, 1, 2, 3, 4, u64::MAX / 2, u64::MAX - 1, u64::MAX];
        for numerator in values {
            for denominator in values {
                let actual = source_over_rounded_ratio(numerator, denominator);
                let expected = if denominator == 0 {
                    0
                } else {
                    let n = u128::from(numerator);
                    let d = u128::from(denominator);
                    n / d + u128::from(2 * (n % d) >= d)
                };
                assert_eq!(actual, expected);
                if denominator > 0 {
                    let n = u128::from(numerator);
                    let d = u128::from(denominator);
                    assert!(2 * d * actual <= 2 * n + d);
                    assert!(2 * n < 2 * d * actual + d);
                }
            }
        }
        assert_eq!(source_over_rounded_ratio(1, 2), 1);
        assert_eq!(source_over_rounded_ratio(3, 2), 2);
        assert_eq!(source_over_rounded_ratio(1, 3), 0);
        assert_eq!(source_over_rounded_ratio(2, 3), 1);
    }

    #[test]
    fn single_layer_output_preserves_fractional_premultiplied_representation() {
        let layer = OwnedLayer {
            width: 2,
            height: 1,
            color_space: ConvertedColorSpace::Grayscale,
            colors: vec![vec![1, 12_345]],
            alpha: Some((vec![2, 32_768], true)),
        };
        let image = layer.into_image().unwrap();
        assert_eq!(image.channel(0).unwrap().samples(), &[1, 12_345]);
        assert_eq!(image.channel(1).unwrap().samples(), &[2, 32_768]);
        assert_eq!(
            image.channel(1).unwrap().channel_type(),
            ConvertedChannelType::Alpha {
                premultiplied: true,
                association: crate::image::ChannelAssociation::WholeImage,
            }
        );
    }

    #[test]
    fn source_over_is_deterministic_and_crops_to_canvas() {
        let black = crate::color::from_composited(
            2,
            1,
            ConvertedColorSpace::Grayscale,
            vec![vec![0, 0]],
            vec![u16::MAX, u16::MAX],
        )
        .unwrap();
        let white = crate::color::from_composited(
            2,
            1,
            ConvertedColorSpace::Grayscale,
            vec![vec![u16::MAX, 1]],
            vec![32_768, u16::MAX],
        )
        .unwrap();
        let black_channels = layer_channels(&black).unwrap();
        let white_channels = layer_channels(&white).unwrap();
        let mut colors = vec![vec![0_u16; 2]];
        let mut alpha = vec![0_u16; 2];
        let limits = ResourceLimits::default();
        let mut work = 0_u64;
        composite_layer(
            2,
            1,
            0,
            0,
            &black_channels,
            &mut colors,
            &mut alpha,
            &mut work,
            &limits,
        )
        .unwrap();
        composite_layer(
            2,
            1,
            1,
            0,
            &white_channels,
            &mut colors,
            &mut alpha,
            &mut work,
            &limits,
        )
        .unwrap();
        assert_eq!(colors[0], [0, 32_768]);
        assert_eq!(alpha, [u16::MAX, u16::MAX]);

        let tight = ResourceLimits::default()
            .with_maximum_work_units(1)
            .unwrap();
        let mut bounded_colors = vec![vec![0_u16; 2]];
        let mut bounded_alpha = vec![0_u16; 2];
        assert!(matches!(
            composite_layer(
                2,
                1,
                0,
                0,
                &black_channels,
                &mut bounded_colors,
                &mut bounded_alpha,
                &mut 0,
                &tight,
            ),
            Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                ..
            })
        ));
    }

    #[test]
    fn rejects_premultiplied_sample_above_alpha() {
        let source = LayerChannels {
            width: 1,
            height: 1,
            colors: vec![&[2_u16]],
            alpha: Some((vec![1_u16], true)),
        };
        let mut colors = vec![vec![0_u16]];
        let mut alpha = vec![0_u16];
        assert!(matches!(
            composite_layer(
                1,
                1,
                0,
                0,
                &source,
                &mut colors,
                &mut alpha,
                &mut 0,
                &ResourceLimits::default(),
            ),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::InvalidBoxContents,
                ..
            })
        ));
    }

    #[test]
    fn timeline_matches_independent_flat_schedule_and_grouping_model() {
        fn reference(
            composition: &Composition,
            layers: usize,
            maximum_frames: u32,
        ) -> Result<Vec<JpxFrameInfo>, DecodeError> {
            let limit = (maximum_frames as usize).checked_mul(layers.max(1)).ok_or(
                DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::ArithmeticOverflow,
                },
            )?;
            let program: Vec<_> = composition
                .instruction_sets
                .iter()
                .flat_map(|set| {
                    (0..=set.repeat).flat_map(move |_| set.instructions.iter().copied())
                })
                .collect();
            let mut scheduled = std::collections::BTreeMap::new();
            let mut unused = 0..layers;
            let mut frames: Vec<JpxFrameInfo> = Vec::new();
            let mut time = 0;
            for (index, instruction) in program.into_iter().enumerate() {
                if index >= limit {
                    return Err(DecodeError::LimitExceeded {
                        resource: Resource::WorkUnits,
                        limit: limit as u64,
                        actual: index as u64 + 1,
                    });
                }
                let layer = match scheduled.get(&index).copied().or_else(|| unused.next()) {
                    Some(layer) => layer,
                    None => break,
                };
                let open = frames
                    .last()
                    .is_some_and(|frame| frame.duration_milliseconds == 0);
                if !open {
                    if frames.len() == maximum_frames as usize {
                        return Err(DecodeError::LimitExceeded {
                            resource: Resource::Frames,
                            limit: maximum_frames as u64,
                            actual: frames.len() as u64 + 1,
                        });
                    }
                    frames.push(JpxFrameInfo {
                        index: frames.len(),
                        start_milliseconds: time,
                        duration_milliseconds: 0,
                        persistent: true,
                        instructions: Vec::new(),
                    });
                }
                let frame = frames.last_mut().unwrap();
                frame.instructions.push(JpxInstructionInfo {
                    layer_index: layer,
                    target_x: instruction.target_x,
                    target_y: instruction.target_y,
                    target_width: instruction.target_width,
                    target_height: instruction.target_height,
                    source_x: instruction.source_x,
                    source_y: instruction.source_y,
                    source_width: instruction.source_width,
                    source_height: instruction.source_height,
                    persistent: instruction.persistent,
                    next_reuse: instruction.next_reuse,
                });
                frame.duration_milliseconds = instruction.life;
                frame.persistent = instruction.persistent;
                time += u64::from(instruction.life);
                if instruction.next_reuse != 0 {
                    let target = index + instruction.next_reuse as usize;
                    if target >= limit {
                        return Err(DecodeError::LimitExceeded {
                            resource: Resource::WorkUnits,
                            limit: limit as u64,
                            actual: target as u64 + 1,
                        });
                    }
                    if scheduled.get(&target).is_some_and(|&prior| prior != layer) {
                        return Err(DecodeError::MalformedInput {
                            offset: 0,
                            kind: MalformedKind::InvalidBoxContents,
                        });
                    }
                    scheduled.insert(target, layer);
                }
            }
            Ok(frames)
        }
        let make = |life, persistent, next_reuse, offset| CompositionInstruction {
            target_x: offset,
            target_y: offset + 1,
            target_width: offset + 2,
            target_height: offset + 3,
            source_x: offset + 4,
            source_y: offset + 5,
            source_width: offset + 6,
            source_height: offset + 7,
            life,
            persistent,
            next_reuse,
        };
        for layers in 0..4 {
            for maximum_frames in 0..5 {
                for repeat in 0..3 {
                    for first_life in [0, 1, u32::MAX] {
                        for second_life in [0, 7] {
                            for first_reuse in 0..4 {
                                for second_reuse in 0..4 {
                                    for persistent in [false, true] {
                                        let composition = Composition {
                                            width: 1,
                                            height: 1,
                                            loop_count: 2,
                                            has_unknown_boxes: true,
                                            instruction_sets: vec![
                                                CompositionInstructionSet {
                                                    flags: 7,
                                                    repeat,
                                                    tick: 11,
                                                    instructions: vec![
                                                        make(
                                                            first_life,
                                                            persistent,
                                                            first_reuse,
                                                            10,
                                                        ),
                                                        make(
                                                            second_life,
                                                            !persistent,
                                                            second_reuse,
                                                            20,
                                                        ),
                                                    ],
                                                },
                                                CompositionInstructionSet {
                                                    flags: 0,
                                                    repeat: 1,
                                                    tick: 99,
                                                    instructions: vec![],
                                                },
                                                CompositionInstructionSet {
                                                    flags: 7,
                                                    repeat: 0,
                                                    tick: 1,
                                                    instructions: vec![make(9, false, 0, 30)],
                                                },
                                            ],
                                        };
                                        assert_eq!(
                                            build_timeline(&composition, layers, maximum_frames),
                                            reference(&composition, layers, maximum_frames),
                                            "layers={layers}, frames={maximum_frames}, repeat={repeat}, life={first_life}/{second_life}, reuse={first_reuse}/{second_reuse}, persistent={persistent}"
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        let empty = Composition {
            width: 0,
            height: 0,
            loop_count: 0,
            instruction_sets: vec![],
            has_unknown_boxes: false,
        };
        assert_eq!(build_timeline(&empty, 1, 0).unwrap(), []);
        assert_eq!(
            build_timeline(&empty, usize::MAX, 2).err(),
            Some(arithmetic_overflow())
        );
    }

    #[test]
    fn timeline_checked_errors_precede_later_reuse_and_layer_exhaustion() {
        let make = |life, next_reuse| CompositionInstruction {
            target_x: 0,
            target_y: 0,
            target_width: 1,
            target_height: 1,
            source_x: 0,
            source_y: 0,
            source_width: 0,
            source_height: 0,
            life,
            persistent: false,
            next_reuse,
        };
        let composition = |instructions| Composition {
            width: 1,
            height: 1,
            loop_count: 1,
            instruction_sets: vec![CompositionInstructionSet {
                flags: 7,
                repeat: 0,
                tick: 1,
                instructions,
            }],
            has_unknown_boxes: false,
        };
        assert_eq!(
            build_timeline(&composition(vec![make(0, 0)]), 0, 0).err(),
            Some(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 0,
                actual: 1
            })
        );
        assert_eq!(
            build_timeline(&composition(vec![make(0, 0)]), 0, 1).unwrap(),
            []
        );
        assert_eq!(
            build_timeline(&composition(vec![make(1, 0), make(1, u32::MAX)]), 2, 1).err(),
            Some(DecodeError::LimitExceeded {
                resource: Resource::Frames,
                limit: 1,
                actual: 2
            })
        );
        assert_eq!(
            build_timeline(&composition(vec![make(1, 2), make(1, 1)]), 2, 3).err(),
            Some(invalid_layer())
        );
        let mut frames = Vec::new();
        let mut time = u64::MAX;
        assert_eq!(
            append_timeline_frame(&mut frames, &mut time, test_unit_instruction(0, 1), 1, 1).err(),
            Some(arithmetic_overflow())
        );
        let mut state = TimelineState {
            frames: Vec::new(),
            assignments: Vec::new(),
            next_layer: 0,
            instruction_index: 0,
            milliseconds: 0,
        };
        assert_eq!(
            apply_timeline_instruction(&mut state, make(1, 0), 0, 0, 0).err(),
            Some(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 0,
                actual: 1
            })
        );
    }

    #[test]
    fn timeline_expands_repetition_reuse_and_timing_deterministically() {
        let instruction = CompositionInstruction {
            target_x: 2,
            target_y: 3,
            target_width: 4,
            target_height: 5,
            life: 25,
            persistent: true,
            next_reuse: 1,
            source_x: 0,
            source_y: 0,
            source_width: 0,
            source_height: 0,
        };
        let composition = Composition {
            width: 8,
            height: 8,
            loop_count: 1,
            instruction_sets: vec![CompositionInstructionSet {
                flags: 7,
                repeat: 1,
                tick: 1,
                instructions: vec![instruction],
            }],
            has_unknown_boxes: false,
        };
        let frames = build_timeline(&composition, 1, 4).unwrap();
        assert_eq!(frames.len(), 2);
        assert_eq!(frames[0].duration_milliseconds(), 25);
        assert_eq!(frames[0].start_milliseconds(), 0);
        assert_eq!(frames[1].start_milliseconds(), 25);
        assert_eq!(frames[0].instructions()[0].layer_index(), 0);
        assert!(frames[0].instructions()[0].persistent());
        assert_eq!(frames[0].instructions()[0].next_reuse(), 1);
        assert_eq!(frames[1].instructions()[0].layer_index(), 0);
        assert_eq!(frames[1].instructions()[0].target_x(), 2);
    }

    #[test]
    fn composed_normalized_frames_match_independent_indexed_supply_and_rational_model() {
        let limits = ResourceLimits::default();
        for mask in 0_u8..16 {
            let composition = Composition {
                width: 2,
                height: 1,
                loop_count: 0,
                has_unknown_boxes: false,
                instruction_sets: vec![CompositionInstructionSet {
                    flags: 7,
                    repeat: 0,
                    tick: 1,
                    instructions: (0..4)
                        .map(|index| CompositionInstruction {
                            target_x: index % 2,
                            target_y: 0,
                            target_width: 1,
                            target_height: 1,
                            source_x: 0,
                            source_y: 0,
                            source_width: 0,
                            source_height: 0,
                            life: index + 1,
                            persistent: mask & (1 << index) != 0,
                            next_reuse: if index == 0 {
                                2
                            } else if index == 2 {
                                1
                            } else {
                                0
                            },
                        })
                        .collect(),
                }],
            };
            let frames = build_timeline(&composition, 2, 4).unwrap();
            for request in [0, 1, 2, 3, 4, 7, 2, 6, 0] {
                for rgb_first in [false, true] {
                    let make_gray = |sample, alpha, premultiplied| {
                        (
                            0,
                            Some(Ok(OwnedLayer {
                                width: 1,
                                height: 1,
                                color_space: ConvertedColorSpace::Grayscale,
                                colors: vec![vec![sample]],
                                alpha: Some((vec![alpha], premultiplied)),
                            })),
                        )
                    };
                    let rgb = (
                        1,
                        Some(Ok(OwnedLayer {
                            width: 1,
                            height: 1,
                            color_space: ConvertedColorSpace::Srgb,
                            colors: vec![vec![60_000], vec![3], vec![32_768]],
                            alpha: None,
                        })),
                    );
                    let mut bank = vec![
                        make_gray(12_345, 32_768, false),
                        (
                            usize::MAX,
                            Some(Err(DecodeError::FrameIndexOutOfRange {
                                index: 99,
                                frames: 1,
                            })),
                        ),
                        (0, None),
                        make_gray(8_000, 16_384, true),
                        make_gray(60_000, u16::MAX, false),
                    ];
                    bank.insert(if rgb_first { 0 } else { 3 }, rgb);
                    let image = render_normalized_frame(
                        2,
                        1,
                        &frames,
                        0,
                        request,
                        bank,
                        limits.maximum_decoded_bytes(),
                        &limits,
                    )
                    .unwrap();
                    let current = request % 4;
                    let chosen: Vec<usize> = (0..=current)
                        .filter(|&index| index == current || mask & (1 << index) != 0)
                        .collect();
                    let rgb = chosen.contains(&1);
                    let channels = if rgb { 3 } else { 1 };
                    let mut colors = vec![vec![0_u16; 2]; channels];
                    let mut alpha = vec![0_u16; 2];
                    let mut gray_occurrence = 0;
                    let maximum = u128::from(u16::MAX);
                    let nearest = |n: u128, d: u128| -> u16 {
                        if d == 0 {
                            0
                        } else {
                            (n / d + u128::from(n % d * 2 >= d)) as u16
                        }
                    };
                    for index in chosen {
                        let pixel = index % 2;
                        let (samples, a, premultiplied) = if index == 1 {
                            ([60_000_u128, 3, 32_768], maximum, false)
                        } else {
                            let (sample, a, flag) = [
                                (12_345, 32_768, false),
                                (8_000, 16_384, true),
                                (60_000, 65_535, false),
                            ][gray_occurrence];
                            gray_occurrence += 1;
                            ([sample; 3], a, flag)
                        };
                        let d = u128::from(alpha[pixel]);
                        let denominator = a * maximum + d * (maximum - a);
                        for channel in 0..channels {
                            let source = if premultiplied {
                                samples[channel] * maximum * maximum
                            } else {
                                samples[channel] * a * maximum
                            };
                            colors[channel][pixel] = nearest(
                                source + u128::from(colors[channel][pixel]) * d * (maximum - a),
                                denominator,
                            );
                        }
                        alpha[pixel] = nearest(denominator, maximum);
                    }
                    assert_eq!(
                        (
                            image.width(),
                            image.height(),
                            image.precision(),
                            image.channels().len()
                        ),
                        (2, 1, 16, channels + 1)
                    );
                    assert_eq!(
                        image.color_space(),
                        if rgb {
                            ConvertedColorSpace::Srgb
                        } else {
                            ConvertedColorSpace::Grayscale
                        }
                    );
                    for (channel, samples) in colors.iter().enumerate() {
                        assert_eq!(image.channel(channel as u16).unwrap().samples(), samples);
                        assert_eq!(
                            image.channel(channel as u16).unwrap().channel_type(),
                            if rgb {
                                [
                                    ConvertedChannelType::Red,
                                    ConvertedChannelType::Green,
                                    ConvertedChannelType::Blue,
                                ][channel]
                            } else {
                                ConvertedChannelType::Gray
                            }
                        );
                    }
                    assert_eq!(image.channel(channels as u16).unwrap().samples(), alpha);
                    assert_eq!(
                        image.channel(channels as u16).unwrap().channel_type(),
                        ConvertedChannelType::Alpha {
                            premultiplied: false,
                            association: ChannelAssociation::WholeImage,
                        }
                    );
                }
            }
        }
    }

    #[test]
    fn composed_normalized_frames_preserve_selection_supply_and_render_error_precedence() {
        let limits = ResourceLimits::default()
            .with_maximum_work_units(0)
            .unwrap();
        let frame = |index, reference, persistent| JpxFrameInfo {
            index,
            start_milliseconds: index as u64,
            duration_milliseconds: 1,
            persistent,
            instructions: vec![test_unit_instruction(reference, 1)],
        };
        let frames = [frame(0, 7, true), frame(1, 9, false)];
        let first_error = DecodeError::FrameIndexOutOfRange {
            index: 123,
            frames: 2,
        };
        let second_error = DecodeError::LayerIndexOutOfRange {
            index: 456,
            layers: 3,
        };
        let invalid = || {
            (
                7,
                Some(Ok(OwnedLayer {
                    width: 1,
                    height: 1,
                    color_space: ConvertedColorSpace::Grayscale,
                    colors: vec![vec![]],
                    alpha: None,
                })),
            )
        };
        for reversed in [false, true] {
            let mut bank = vec![(9, Some(Err(second_error))), (7, Some(Err(first_error)))];
            if reversed {
                bank.reverse();
            }
            assert_eq!(
                render_normalized_frame(1, 1, &frames, 1, 1, bank, 0, &limits).err(),
                Some(first_error)
            );
        }
        assert_eq!(
            render_normalized_frame(
                1,
                1,
                &frames,
                1,
                1,
                vec![(9, Some(Err(second_error))), invalid()],
                0,
                &limits
            )
            .err(),
            Some(second_error)
        );
        assert_eq!(
            render_normalized_frame(1, 1, &frames, 1, 1, vec![invalid()], 0, &limits).err(),
            Some(invalid_layer())
        );
        assert_eq!(
            render_normalized_frame(
                1,
                1,
                &frames,
                1,
                2,
                vec![(7, Some(Err(first_error)))],
                0,
                &limits
            )
            .err(),
            Some(DecodeError::FrameIndexOutOfRange {
                index: 2,
                frames: 2
            })
        );
        assert_eq!(
            render_normalized_frame(
                1,
                1,
                &[],
                0,
                0,
                vec![(7, Some(Err(first_error)))],
                0,
                &limits
            )
            .err(),
            Some(DecodeError::FrameIndexOutOfRange {
                index: 0,
                frames: 0
            })
        );
        let repeated = [JpxFrameInfo {
            index: 0,
            start_milliseconds: 0,
            duration_milliseconds: 1,
            persistent: false,
            instructions: vec![test_unit_instruction(7, 1), test_unit_instruction(7, 1)],
        }];
        assert_eq!(
            render_normalized_frame(
                1,
                1,
                &repeated,
                0,
                0,
                vec![
                    (7, None),
                    invalid(),
                    (7, Some(Err(second_error))),
                    (7, Some(Err(first_error)))
                ],
                0,
                &limits
            )
            .err(),
            Some(second_error)
        );
        let valid = || {
            (
                7,
                Some(Ok(OwnedLayer {
                    width: 1,
                    height: 1,
                    color_space: ConvertedColorSpace::Grayscale,
                    colors: vec![vec![7]],
                    alpha: None,
                })),
            )
        };
        assert_eq!(
            render_normalized_frame(1, 1, &frames[..1], 0, 0, vec![valid()], 7, &limits).err(),
            Some(DecodeError::LimitExceeded {
                resource: Resource::DecodedBytes,
                limit: 7,
                actual: 8
            })
        );
        assert_eq!(
            render_normalized_frame(1, 1, &frames[..1], 0, 0, vec![valid()], 8, &limits).err(),
            Some(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 0,
                actual: 3
            })
        );
        assert_eq!(
            render_normalized_frame(
                1,
                1,
                &frames[..1],
                0,
                0,
                vec![invalid()],
                8,
                &ResourceLimits::default()
            )
            .err(),
            Some(invalid_layer())
        );
    }

    #[test]
    fn normalized_frame_selection_matches_ordered_sequence_model() {
        for mask in 0_u8..16 {
            let frames: Vec<_> = (0..4)
                .map(|index| JpxFrameInfo {
                    index: 99 - index,
                    start_milliseconds: index as u64 * 11,
                    duration_milliseconds: 11,
                    persistent: mask & (1 << index) != 0,
                    instructions: (0..index)
                        .map(|local| {
                            let mut instruction = test_unit_instruction((index + local) % 3, 1);
                            instruction.target_x = (index * 10 + local) as u32;
                            instruction.persistent = local % 2 == 0;
                            instruction.next_reuse = local as u32;
                            instruction
                        })
                        .collect(),
                })
                .collect();
            for loops in [0, 1, 3] {
                for requested in (0..14).chain([usize::MAX]) {
                    let selected = select_frame_instructions(&frames, loops, requested);
                    if loops != 0 && requested >= 4 * usize::from(loops) {
                        assert_eq!(
                            selected.err(),
                            Some(DecodeError::FrameIndexOutOfRange {
                                index: requested,
                                frames: 4 * usize::from(loops),
                            })
                        );
                        continue;
                    }
                    let current = requested % 4;
                    let selected = selected.unwrap();
                    let expected: Vec<_> = (0..=current)
                        .filter(|&index| index == current || mask & (1 << index) != 0)
                        .flat_map(|index| {
                            (0..index).map(move |local| {
                                (
                                    (index * 10 + local) as u32,
                                    (index + local) % 3,
                                    local % 2 == 0,
                                    local as u32,
                                )
                            })
                        })
                        .collect();
                    assert_eq!(
                        selected
                            .iter()
                            .map(|instruction| (
                                instruction.target_x,
                                instruction.layer_index,
                                instruction.persistent,
                                instruction.next_reuse
                            ))
                            .collect::<Vec<_>>(),
                        expected
                    );
                }
            }
        }
        for requested in [0, 1, usize::MAX] {
            assert_eq!(
                select_frame_instructions(&[], 0, requested).err(),
                Some(DecodeError::FrameIndexOutOfRange {
                    index: requested,
                    frames: 0
                })
            );
        }
    }

    #[test]
    fn normalized_multiframe_reuse_persistence_and_reset_match_rational_images() {
        let mut instructions = Vec::new();
        for (index, (life, persistent, next_reuse)) in
            [(10, true, 2), (20, false, 0), (30, true, 1), (40, false, 0)]
                .into_iter()
                .enumerate()
        {
            instructions.push(CompositionInstruction {
                target_x: u32::from(index == 3),
                target_y: 0,
                target_width: 1,
                target_height: 1,
                life,
                persistent,
                next_reuse,
                source_x: 0,
                source_y: 0,
                source_width: 0,
                source_height: 0,
            });
        }
        let composition = Composition {
            width: 2,
            height: 1,
            loop_count: 0,
            has_unknown_boxes: false,
            instruction_sets: vec![CompositionInstructionSet {
                flags: 7,
                repeat: 0,
                tick: 1,
                instructions,
            }],
        };
        let frames = build_timeline(&composition, 2, 4).unwrap();
        assert_eq!(
            frames
                .iter()
                .map(|frame| (
                    frame.index,
                    frame.start_milliseconds,
                    frame.duration_milliseconds,
                    frame.persistent,
                    frame.instructions[0].layer_index
                ))
                .collect::<Vec<_>>(),
            [
                (0, 0, 10, true, 0),
                (1, 10, 20, false, 1),
                (2, 30, 30, true, 0),
                (3, 60, 40, false, 0)
            ]
        );
        let limits = ResourceLimits::default();
        for requested in [0, 1, 2, 3, 4, 7, 6, 2, 0, usize::MAX] {
            let selected =
                select_frame_instructions(&frames, composition.loop_count, requested).unwrap();
            let expected_indices: &[usize] = match requested % 4 {
                0 => &[0],
                1 => &[0, 1],
                2 => &[0, 2],
                _ => &[0, 2, 3],
            };
            assert_eq!(
                selected
                    .iter()
                    .map(|instruction| (instruction.layer_index, instruction.target_x))
                    .collect::<Vec<_>>(),
                expected_indices
                    .iter()
                    .map(|&index| (usize::from(index == 1), u32::from(index == 3)))
                    .collect::<Vec<_>>()
            );
            let layers: Vec<_> = selected
                .into_iter()
                .map(|instruction| {
                    let layer = if instruction.layer_index == 0 {
                        OwnedLayer {
                            width: 1,
                            height: 1,
                            color_space: ConvertedColorSpace::Grayscale,
                            colors: vec![vec![12_345]],
                            alpha: Some((vec![32_768], false)),
                        }
                    } else {
                        OwnedLayer {
                            width: 1,
                            height: 1,
                            color_space: ConvertedColorSpace::Srgb,
                            colors: vec![vec![u16::MAX], vec![0], vec![1]],
                            alpha: None,
                        }
                    };
                    (layer, instruction)
                })
                .collect();
            let image =
                render_decoded_layers(2, 1, &layers, limits.maximum_decoded_bytes(), &limits)
                    .unwrap();
            let color_count = if requested % 4 == 1 { 3 } else { 1 };
            assert_eq!(
                (
                    image.width(),
                    image.height(),
                    image.precision(),
                    image.channels().len()
                ),
                (2, 1, 16, color_count + 1)
            );
            assert_eq!(
                image.color_space(),
                if color_count == 3 {
                    ConvertedColorSpace::Srgb
                } else {
                    ConvertedColorSpace::Grayscale
                }
            );
            let mut expected_colors = vec![vec![0_u16; 2]; color_count];
            let mut expected_alpha = vec![0_u16; 2];
            let maximum = u128::from(u16::MAX);
            let nearest = |n: u128, d: u128| -> u16 {
                if d == 0 {
                    0
                } else {
                    (n / d + u128::from(n % d * 2 >= d)) as u16
                }
            };
            for &index in expected_indices {
                let pixel = usize::from(index == 3);
                let source_alpha = if index == 1 { maximum } else { 32_768 };
                let destination_alpha = u128::from(expected_alpha[pixel]);
                let denominator =
                    source_alpha * maximum + destination_alpha * (maximum - source_alpha);
                for (channel, samples) in expected_colors.iter_mut().enumerate() {
                    let source = if index == 1 {
                        [maximum, 0, 1][channel]
                    } else {
                        12_345
                    };
                    samples[pixel] = nearest(
                        source * source_alpha * maximum
                            + u128::from(samples[pixel])
                                * destination_alpha
                                * (maximum - source_alpha),
                        denominator,
                    );
                }
                expected_alpha[pixel] = nearest(denominator, maximum);
            }
            for (channel, samples) in expected_colors.iter().enumerate() {
                assert_eq!(image.channel(channel as u16).unwrap().samples(), samples);
            }
            assert_eq!(
                image.channel(color_count as u16).unwrap().samples(),
                expected_alpha
            );
            assert_eq!(
                image.channel(color_count as u16).unwrap().channel_type(),
                ConvertedChannelType::Alpha {
                    premultiplied: false,
                    association: ChannelAssociation::WholeImage,
                }
            );
        }
        assert_eq!(
            select_frame_instructions(&frames, 2, 8).err(),
            Some(DecodeError::FrameIndexOutOfRange {
                index: 8,
                frames: 8
            })
        );
    }

    #[test]
    fn normalized_layer_sequence_matches_independent_rational_stack() {
        let maximum = u128::from(u16::MAX);
        let nearest = |n: u128, d: u128| -> u16 {
            if d == 0 {
                0
            } else {
                (n / d + u128::from(n % d * 2 >= d)) as u16
            }
        };
        for order in [[0, 1, 2], [2, 1, 0], [1, 0, 2], [0, 2, 1]] {
            for premultiplied in [false, true] {
                let mut layers = Vec::new();
                let mut expected = [vec![0_u16; 2], vec![0_u16; 2], vec![0_u16; 2]];
                let mut expected_alpha = vec![0_u16; 2];
                for index in order {
                    let alpha = [[32_768, 0], [12_345, u16::MAX], [54_321, 1]][index];
                    let straight = [[60_000, 7], [1, 30_000], [45_000, 60_000]][index];
                    let gray = index != 1;
                    let plane_count = if gray { 1 } else { 3 };
                    let colors: Vec<Vec<u16>> = (0..plane_count)
                        .map(|channel| {
                            (0..2)
                                .map(|pixel| {
                                    let sample = straight[pixel] / (channel + 1) as u16;
                                    if premultiplied {
                                        nearest(
                                            u128::from(sample) * u128::from(alpha[pixel]),
                                            maximum,
                                        )
                                    } else {
                                        sample
                                    }
                                })
                                .collect()
                        })
                        .collect();
                    for pixel in 0..2 {
                        let a = u128::from(alpha[pixel]);
                        let d = u128::from(expected_alpha[pixel]);
                        let denominator = a * maximum + d * (maximum - a);
                        for channel in 0..3 {
                            let s = u128::from(colors[if gray { 0 } else { channel }][pixel]);
                            let old = u128::from(expected[channel][pixel]);
                            expected[channel][pixel] = nearest(
                                if premultiplied {
                                    s * maximum * maximum
                                } else {
                                    s * a * maximum
                                } + old * d * (maximum - a),
                                denominator,
                            );
                        }
                        expected_alpha[pixel] = nearest(denominator, maximum);
                    }
                    layers.push((
                        OwnedLayer {
                            width: 2,
                            height: 1,
                            color_space: if gray {
                                ConvertedColorSpace::Grayscale
                            } else {
                                ConvertedColorSpace::Srgb
                            },
                            colors,
                            alpha: Some((alpha.to_vec(), premultiplied)),
                        },
                        test_unit_instruction(index, 2),
                    ));
                }
                let limits = ResourceLimits::default();
                let image =
                    render_decoded_layers(2, 1, &layers, limits.maximum_decoded_bytes(), &limits)
                        .unwrap();
                assert_eq!(
                    (
                        image.width(),
                        image.height(),
                        image.precision(),
                        image.color_space()
                    ),
                    (2, 1, 16, ConvertedColorSpace::Srgb)
                );
                assert_eq!(image.channels().len(), 4);
                for (channel, expected_samples) in expected.iter().enumerate() {
                    assert_eq!(
                        image.channel(channel as u16).unwrap().samples(),
                        expected_samples
                    );
                    assert_eq!(
                        image.channel(channel as u16).unwrap().channel_type(),
                        [
                            ConvertedChannelType::Red,
                            ConvertedChannelType::Green,
                            ConvertedChannelType::Blue
                        ][channel]
                    );
                }
                assert_eq!(image.channel(3).unwrap().samples(), expected_alpha);
                assert_eq!(
                    image.channel(3).unwrap().channel_type(),
                    ConvertedChannelType::Alpha {
                        premultiplied: false,
                        association: ChannelAssociation::WholeImage,
                    }
                );
            }
        }
    }

    fn test_unit_instruction(layer_index: usize, width: u32) -> JpxInstructionInfo {
        JpxInstructionInfo {
            layer_index,
            target_x: 0,
            target_y: 0,
            target_width: width,
            target_height: 1,
            source_x: 0,
            source_y: 0,
            source_width: 0,
            source_height: 0,
            persistent: true,
            next_reuse: 0,
        }
    }

    #[test]
    fn normalized_layer_sequence_preserves_resource_and_first_error_precedence() {
        let gray = |samples: Vec<u16>| OwnedLayer {
            width: 1,
            height: 1,
            color_space: ConvertedColorSpace::Grayscale,
            colors: vec![samples],
            alpha: None,
        };
        let limits = ResourceLimits::default();
        let layers = [
            (gray(vec![7]), test_unit_instruction(0, 1)),
            (gray(vec![9]), test_unit_instruction(1, 1)),
        ];
        for (cap, actual) in [(0, 8), (7, 8), (8, 12), (11, 12)] {
            assert_eq!(
                render_decoded_layers(1, 1, &layers, cap, &limits).err(),
                Some(DecodeError::LimitExceeded {
                    resource: Resource::DecodedBytes,
                    limit: cap,
                    actual
                })
            );
        }
        for (cap, actual) in [(0, 3), (2, 3), (3, 5), (4, 5)] {
            let tight = limits.with_maximum_work_units(cap).unwrap();
            assert_eq!(
                render_decoded_layers(1, 1, &layers, 12, &tight).err(),
                Some(DecodeError::LimitExceeded {
                    resource: Resource::WorkUnits,
                    limit: cap,
                    actual
                })
            );
        }
        let image = render_decoded_layers(
            1,
            1,
            &layers,
            12,
            &limits.with_maximum_work_units(5).unwrap(),
        )
        .unwrap();
        assert_eq!(image.channel(0).unwrap().samples(), [9]);
        let invalid = [
            (gray(vec![]), test_unit_instruction(0, 1)),
            (gray(vec![9]), test_unit_instruction(1, 1)),
        ];
        assert_eq!(
            render_decoded_layers(1, 1, &invalid, 7, &limits).err(),
            Some(DecodeError::LimitExceeded {
                resource: Resource::DecodedBytes,
                limit: 7,
                actual: 8
            })
        );
        assert_eq!(
            render_decoded_layers(1, 1, &invalid, 8, &limits).err(),
            Some(invalid_layer())
        );
        let mut invalid_target = test_unit_instruction(0, 0);
        invalid_target.source_width = 0;
        let invalid_first = [
            (gray(vec![7]), invalid_target),
            (gray(vec![]), test_unit_instruction(1, 1)),
        ];
        assert_eq!(
            render_decoded_layers(1, 1, &invalid_first, 12, &limits).err(),
            Some(invalid_layer())
        );
        assert_eq!(
            render_decoded_layers(0, 0, &[], 0, &limits).err(),
            Some(invalid_layer())
        );
        let huge = [(
            OwnedLayer {
                width: u32::MAX,
                height: u32::MAX,
                color_space: ConvertedColorSpace::Srgb,
                colors: vec![vec![], vec![], vec![]],
                alpha: None,
            },
            test_unit_instruction(0, 1),
        )];
        assert_eq!(
            render_decoded_layers(1, 1, &huge, u64::MAX, &limits).err(),
            Some(arithmetic_overflow())
        );
    }

    #[test]
    fn normalized_layer_sequence_selects_space_globally_and_preserves_empty_canvas_metadata() {
        let mut hidden = test_unit_instruction(1, 1);
        hidden.target_x = 10;
        let layers = [
            (
                OwnedLayer {
                    width: 1,
                    height: 1,
                    color_space: ConvertedColorSpace::Grayscale,
                    colors: vec![vec![12_345]],
                    alpha: None,
                },
                test_unit_instruction(0, 1),
            ),
            (
                OwnedLayer {
                    width: 1,
                    height: 1,
                    color_space: ConvertedColorSpace::Srgb,
                    colors: vec![vec![], vec![], vec![]],
                    alpha: None,
                },
                hidden,
            ),
        ];
        let limits = ResourceLimits::default();
        let image = render_decoded_layers(1, 1, &layers, 20, &limits).unwrap();
        assert_eq!(image.color_space(), ConvertedColorSpace::Srgb);
        for channel in 0..3 {
            assert_eq!(image.channel(channel).unwrap().samples(), [12_345]);
        }
        assert_eq!(image.channel(3).unwrap().samples(), [u16::MAX]);
        let image = render_decoded_layers(0, 0, &layers, 12, &limits).unwrap();
        assert_eq!(
            (
                image.width(),
                image.height(),
                image.precision(),
                image.channels().len()
            ),
            (0, 0, 16, 4)
        );
        assert!(
            image
                .channels()
                .iter()
                .all(|channel| channel.samples().is_empty())
        );
    }

    #[test]
    fn scaled_registration_and_mixed_color_spaces_are_bounded() {
        let gray = OwnedLayer {
            width: 1,
            height: 1,
            color_space: ConvertedColorSpace::Grayscale,
            colors: vec![vec![12_345]],
            alpha: None,
        };
        let registered = register_layer(
            &gray,
            &jp2::CodestreamRegistration {
                codestream_index: 0,
                horizontal_subsampling: 2,
                vertical_subsampling: 1,
                horizontal_offset: 0,
                vertical_offset: 0,
            },
            1,
            1,
        )
        .unwrap();
        assert_eq!(registered.width, 2);
        assert_eq!(registered.colors[0], [12_345, 12_345]);
        let red = OwnedLayer {
            width: 1,
            height: 1,
            color_space: ConvertedColorSpace::Srgb,
            colors: vec![vec![u16::MAX], vec![0], vec![0]],
            alpha: None,
        };
        let placement = |layer_index| JpxInstructionInfo {
            layer_index,
            target_x: 0,
            target_y: 0,
            target_width: 1,
            target_height: 1,
            source_x: 0,
            source_y: 0,
            source_width: 0,
            source_height: 0,
            persistent: true,
            next_reuse: 0,
        };
        let rendered = render_decoded_layers(
            1,
            1,
            &[(gray, placement(0)), (red, placement(1))],
            ResourceLimits::default().maximum_decoded_bytes(),
            &ResourceLimits::default(),
        )
        .unwrap();
        assert_eq!(rendered.color_space(), ConvertedColorSpace::Srgb);
        assert_eq!(rendered.channel(0).unwrap().samples(), &[u16::MAX]);
    }
}
