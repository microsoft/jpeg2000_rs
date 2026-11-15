use super::*;

fn dimension_recovery_codestream() -> Vec<u8> {
    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0xcf, 0xb4, 0x04, 0x09]);
    let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
    bytes[cod + 9] = 0;
    bytes
}

#[test]
fn pdf_dimensions_recover_only_declared_sizes_and_preserve_strict_defaults() {
    let bytes = dimension_recovery_codestream();
    let options = DecodeOptions::default();
    let expected = decode_codestream(&bytes, &options).unwrap();
    for width in [1, 2] {
        let container = jp2_for_codestream(&bytes, width, 1);
        let inspected = crate::inspect_jp2_recover_dimensions(&container, &options).unwrap();
        assert_eq!(inspected.report.header_width, width);
        assert_eq!(inspected.report.ignored_container_dimensions, width != 1);
        assert_eq!((inspected.report.width, inspected.report.height), (1, 1));
        let recovered = crate::decode_jp2_recover_dimensions(&container, &options).unwrap();
        assert_eq!(recovered.report, inspected.report);
        assert_eq!(recovered.image, expected);
        assert_eq!(
            recovered.image.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![1])
        );
        let centered =
            crate::decode_jp2_reconstructed_recover_dimensions(&container, &options).unwrap();
        assert_eq!(centered.report, inspected.report);
        assert_eq!(centered.image.component(0).unwrap().samples(), &[-127]);
        assert_eq!(centered.image.typed(options.limits()).unwrap(), expected);
        if width == 2 {
            assert!(matches!(
                decode_jp2(&container, &options),
                Err(DecodeError::MalformedInput {
                    kind: MalformedKind::ContainerCodestreamMismatch,
                    ..
                })
            ));
        }
    }
}

#[test]
fn pdf_dimensions_preserve_component_and_uniform_or_variable_precision_checks() {
    let bytes = dimension_recovery_codestream();
    let options = DecodeOptions::default();
    for (count, depth) in [(2_u16, 7_u8), (1, 6), (1, 0x87)] {
        let mut container = jp2_for_codestream(&bytes, 2, 1);
        let ihdr = container
            .windows(4)
            .position(|part| part == b"ihdr")
            .unwrap()
            + 4;
        container[ihdr + 8..ihdr + 10].copy_from_slice(&count.to_be_bytes());
        container[ihdr + 10] = depth;
        assert!(matches!(
            crate::decode_jp2_recover_dimensions(&container, &options),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::ContainerCodestreamMismatch,
                ..
            })
        ));
    }
    let mut two = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0, 0]);
    two[4..6].copy_from_slice(&44_u16.to_be_bytes());
    two[40..42].copy_from_slice(&2_u16.to_be_bytes());
    two.splice(45..45, [11, 1, 1]);
    let cod = two.windows(2).position(|pair| pair == [255, 82]).unwrap();
    two[cod + 9] = 0;
    let sot = two.windows(2).position(|pair| pair == [255, 144]).unwrap();
    two.splice(sot..sot, segment(0xff5d, &[1, 0x40, 0x60]));
    let expected = decode_codestream(&two, &options).unwrap();
    assert_eq!(expected.components().len(), 2);
    for depths in [[7_u8, 11], [7, 10], [7, 0x8b]] {
        let mut container = jp2_reconstruction_with_metadata(&two, &box32(*b"bpcc", &depths));
        let ihdr = container
            .windows(4)
            .position(|part| part == b"ihdr")
            .unwrap()
            + 4;
        container[ihdr + 4..ihdr + 8].copy_from_slice(&2_u32.to_be_bytes());
        container[ihdr + 8..ihdr + 10].copy_from_slice(&2_u16.to_be_bytes());
        container[ihdr + 10] = 255;
        if depths == [7, 11] {
            assert_eq!(
                crate::decode_jp2_recover_dimensions(&container, &options)
                    .unwrap()
                    .image,
                expected
            );
            for override_depths in [None, Some([7_u8, 11]), Some([7, 10])] {
                let mut associated = container.clone();
                associated.splice(12..32, box32(*b"ftyp", b"jpx \0\0\0\0jp2 jpx "));
                let mut header = box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]);
                if let Some(depths) = override_depths {
                    header.extend(box32(*b"bpcc", &depths));
                }
                let stream = associated
                    .windows(4)
                    .position(|part| part == b"jp2c")
                    .unwrap()
                    - 4;
                associated.splice(stream..stream, box32(*b"jpch", &header));
                let result = crate::decode_jp2_recover_dimensions(&associated, &options);
                if override_depths == Some([7, 10]) {
                    assert!(matches!(
                        result,
                        Err(DecodeError::MalformedInput {
                            kind: MalformedKind::ContainerCodestreamMismatch,
                            ..
                        })
                    ));
                } else {
                    assert_eq!(result.unwrap().image, expected);
                }
            }
        } else {
            assert!(matches!(
                crate::decode_jp2_recover_dimensions(&container, &options),
                Err(DecodeError::MalformedInput {
                    kind: MalformedKind::ContainerCodestreamMismatch,
                    ..
                })
            ));
        }
    }
}

#[test]
fn pdf_dimensions_keep_real_nonzero_origin_and_never_promote_inspection_to_pixels() {
    let options = DecodeOptions::default();
    let bytes = two_tile_codestream();
    let container = jp2_for_codestream(&bytes, 99, 1);
    let recovered = crate::decode_jp2_recover_dimensions(&container, &options).unwrap();
    assert_eq!(
        (
            recovered.image.width(),
            recovered.image.height(),
            recovered.image.x_origin()
        ),
        (5, 1, 1)
    );
    assert_eq!(
        (
            recovered.report.width,
            recovered.report.height,
            recovered.report.x_origin
        ),
        (5, 1, 1)
    );
    assert_eq!(recovered.report.header_width, 99);
    assert_eq!(
        recovered.image,
        decode_codestream(&bytes, &options).unwrap()
    );

    let mut damaged = dimension_recovery_codestream();
    let sod = damaged
        .windows(2)
        .position(|pair| pair == [255, 147])
        .unwrap();
    damaged[sod + 2] = 0xff;
    let container = jp2_for_codestream(&damaged, 2, 1);
    assert!(crate::inspect_jp2_recover_dimensions(&container, &options).is_ok());
    let expected = decode_codestream(&damaged, &options).unwrap_err();
    assert_eq!(
        crate::decode_jp2_recover_dimensions(&container, &options).err(),
        Some(expected)
    );
}

#[test]
fn pdf_dimensions_keep_limits_metadata_processing_and_refusal_restoration() {
    let options = DecodeOptions::default();
    let bytes = dimension_recovery_codestream();
    let container = jp2_for_codestream(&bytes, 2, 1);
    let expected = crate::decode_jp2_recover_dimensions(&container, &options).unwrap();
    for limits in [
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
    ] {
        assert!(matches!(
            crate::decode_jp2_recover_dimensions(&container, &DecodeOptions::new(limits)),
            Err(DecodeError::LimitExceeded { .. })
        ));
    }
    let mut oversized = container.clone();
    let ihdr = oversized
        .windows(4)
        .position(|part| part == b"ihdr")
        .unwrap()
        + 4;
    oversized[ihdr + 4..ihdr + 8]
        .copy_from_slice(&(ResourceLimits::HARDENED.maximum_width() + 1).to_be_bytes());
    assert!(matches!(
        crate::decode_jp2_recover_dimensions(&oversized, &options),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Width,
            ..
        })
    ));
    let mut completed = false;
    for after in 0..256 {
        match crate::allocation::with_refusal(after, || {
            crate::decode_jp2_recover_dimensions(&container, &options)
        }) {
            Err(DecodeError::AllocationFailed) => assert_eq!(
                crate::decode_jp2_recover_dimensions(&container, &options).unwrap(),
                expected
            ),
            Ok(actual) => {
                assert_eq!(actual, expected);
                completed = true;
                break;
            }
            Err(error) => panic!("unexpected dimension recovery refusal at {after}: {error:?}"),
        }
    }
    assert!(completed);
    let mut mapped = jp2_reconstruction_with_metadata(&bytes, &box32(*b"cmap", &[0, 0, 0, 0]));
    let ihdr = mapped.windows(4).position(|part| part == b"ihdr").unwrap() + 4;
    mapped[ihdr + 4..ihdr + 8].copy_from_slice(&2_u32.to_be_bytes());
    assert!(crate::decode_jp2_recover_dimensions(&mapped, &options).is_ok());
    assert_eq!(
        crate::decode_jp2_reconstructed_recover_dimensions(&mapped, &options).err(),
        Some(DecodeError::UnsupportedFeature {
            feature: "JP2 output transforms on reconstruction samples",
        })
    );
    assert!(decode_jp2(&container, &options).is_err());
}

#[test]
fn jp2_reconstructed_output_retains_fractional_headroom_and_coded_geometry() {
    let options = DecodeOptions::default();
    for (packet, numerator) in [
        (&[0xcf, 0xb4, 0x04, 0x09][..], -765_i64),
        (&[0xc0, 0x21, 0x03][..], 9),
    ] {
        let mut bytes = prepared_codestream(1, 1, 0, &[0x42, 0x44, 0], packet);
        let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
        bytes[cod + 9] = 0;
        let container = jp2_for_codestream(&bytes, 1, 1);
        let image = crate::decode_jp2_reconstructed(&container, &options).unwrap();
        let component = image.component(0).unwrap();
        assert_eq!(component.fraction_bits(), 16);
        assert_eq!(component.samples(), &[numerator * (1 << 14)]);
        assert_eq!(
            image,
            crate::decode_codestream_reconstructed(&bytes, &options).unwrap()
        );
        assert_eq!(
            image.typed(options.limits()),
            decode_jp2(&container, &options)
        );
    }

    let bytes = two_tile_codestream();
    let info = codestream::parse(&bytes, options.limits()).unwrap();
    let container = jp2_for_codestream(&bytes, info.image_size.width, info.image_size.height);
    let image = crate::decode_jp2_reconstructed(&container, &options).unwrap();
    assert_eq!(
        (
            image.width(),
            image.height(),
            image.x_origin(),
            image.y_origin()
        ),
        (5, 1, 1, 0)
    );
    assert_eq!(
        image,
        crate::decode_codestream_reconstructed(&bytes, &options).unwrap()
    );
    assert_eq!(
        image.typed(options.limits()),
        decode_jp2(&container, &options)
    );
}

fn jp2_reconstruction_with_metadata(bytes: &[u8], metadata: &[u8]) -> Vec<u8> {
    let mut container = jp2_for_codestream(bytes, 1, 1);
    let start = container
        .windows(4)
        .position(|part| part == b"jp2h")
        .unwrap()
        - 4;
    let length = u32::from_be_bytes(container[start..start + 4].try_into().unwrap());
    let end = start + length as usize;
    container.splice(end..end, metadata.iter().copied());
    container[start..start + 4].copy_from_slice(&(length + metadata.len() as u32).to_be_bytes());
    container
}

#[test]
fn jp2_reconstructed_output_rejects_typed_mappings_without_masking_decode_errors() {
    let options = DecodeOptions::default();
    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0]);
    let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
    bytes[cod + 9] = 0;
    let mapped = jp2_reconstruction_with_metadata(&bytes, &box32(*b"cmap", &[0, 0, 0, 0]));
    let start = mapped.windows(4).position(|part| part == b"jp2h").unwrap() - 4;
    let length = u32::from_be_bytes(mapped[start..start + 4].try_into().unwrap()) as usize;
    let mut associated = jp2_for_codestream(&bytes, 1, 1);
    associated.splice(12..32, box32(*b"ftyp", b"jpx \0\0\0\0jp2 jpx "));
    let codestream = associated
        .windows(4)
        .position(|part| part == b"jp2c")
        .unwrap()
        - 4;
    associated.splice(
        codestream..codestream,
        box32(*b"jpch", &mapped[start + 8..start + length]),
    );
    for container in [
        jp2_reconstruction_with_metadata(&bytes, &box32(*b"cmap", &[0, 0, 0, 0])),
        jp2_reconstruction_with_metadata(&bytes, &box32(*b"cdef", &[0, 1, 0, 0, 0, 0, 0, 1])),
        jp2_with_palette(&bytes, 256, true),
        associated,
    ] {
        assert!(decode_jp2(&container, &options).is_ok());
        assert_eq!(
            crate::decode_jp2_reconstructed(&container, &options),
            Err(DecodeError::UnsupportedFeature {
                feature: "JP2 output transforms on reconstruction samples",
            })
        );
        let limited = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(0).unwrap());
        let expected = decode_jp2(&container, &limited).unwrap_err();
        assert!(matches!(expected, DecodeError::LimitExceeded { .. }));
        assert_eq!(
            crate::decode_jp2_reconstructed(&container, &limited),
            Err(expected)
        );
        let mut damaged = container;
        let sod = damaged
            .windows(2)
            .position(|pair| pair == [255, 147])
            .unwrap();
        damaged[sod + 2] = 0xff;
        let expected = decode_jp2(&damaged, &options).unwrap_err();
        assert_eq!(
            crate::decode_jp2_reconstructed(&damaged, &options),
            Err(expected)
        );
    }
}

#[test]
fn jp2_reconstructed_output_keeps_header_profile_and_nlt_validation() {
    let options = DecodeOptions::default();
    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0]);
    let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
    bytes[cod + 9] = 0;
    let good = jp2_for_codestream(&bytes, 1, 1);
    for end in 0..good.len() {
        let expected = decode_jp2(&good[..end], &options).unwrap_err();
        assert_eq!(
            crate::decode_jp2_reconstructed(&good[..end], &options),
            Err(expected)
        );
    }
    let mut precision = good.clone();
    let ihdr = precision
        .windows(4)
        .position(|part| part == b"ihdr")
        .unwrap()
        + 4;
    precision[ihdr + 10] = 6;
    let mut components = good.clone();
    components[ihdr + 8..ihdr + 10].copy_from_slice(&2_u16.to_be_bytes());
    for bad in [jp2_for_codestream(&bytes, 2, 1), precision, components] {
        let expected = decode_jp2(&bad, &options).unwrap_err();
        assert_eq!(
            crate::decode_jp2_reconstructed(&bad, &options),
            Err(expected)
        );
    }
    let start = good.windows(4).position(|part| part == b"jp2h").unwrap() - 4;
    let length = u32::from_be_bytes(good[start..start + 4].try_into().unwrap()) as usize;
    let mut associated = good.clone();
    associated.splice(12..32, box32(*b"ftyp", b"jpx \0\0\0\0jp2 jpx "));
    let stream = associated
        .windows(4)
        .position(|part| part == b"jp2c")
        .unwrap()
        - 4;
    associated.splice(
        stream..stream,
        box32(*b"jpch", &good[start + 8..start + length]),
    );
    assert_eq!(
        crate::decode_jp2_reconstructed(&associated, &options),
        crate::decode_codestream_reconstructed(&bytes, &options)
    );
    let jpch = associated
        .windows(4)
        .position(|part| part == b"jpch")
        .unwrap()
        + 4;
    let local_ihdr = associated[jpch..]
        .windows(4)
        .position(|part| part == b"ihdr")
        .unwrap()
        + jpch;
    associated[local_ihdr..local_ihdr + 4].copy_from_slice(b"skip");
    assert!(decode_jp2(&associated, &options).is_ok());
    assert_eq!(
        crate::decode_jp2_reconstructed(&associated, &options),
        crate::decode_codestream_reconstructed(&bytes, &options)
    );
    let sot = bytes
        .windows(2)
        .position(|pair| pair == [255, 144])
        .unwrap();
    bytes.splice(sot..sot, segment(0xff76, &[255, 255, 7, 0]));
    let container = jp2_for_codestream(&bytes, 1, 1);
    assert!(decode_jp2(&container, &options).is_ok());
    assert_eq!(
        crate::decode_jp2_reconstructed(&container, &options),
        Err(DecodeError::UnsupportedFeature {
            feature: "nonlinear transforms on reconstruction samples",
        })
    );
}

#[test]
fn jp2_reconstructed_output_propagates_refused_storage_and_limits_then_recovers() {
    let options = DecodeOptions::default();
    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0xcf, 0xb4, 0x04, 0x09]);
    let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
    bytes[cod + 9] = 0;
    let container = jp2_for_codestream(&bytes, 1, 1);
    let expected = crate::decode_jp2_reconstructed(&container, &options).unwrap();
    let mut completed = false;
    for after in 0..256 {
        let result = crate::allocation::with_refusal(after, || {
            crate::decode_jp2_reconstructed(&container, &options)
        });
        match result {
            Err(DecodeError::AllocationFailed) => assert_eq!(
                crate::decode_jp2_reconstructed(&container, &options).unwrap(),
                expected
            ),
            Ok(image) => {
                assert_eq!(image, expected);
                completed = true;
                break;
            }
            Err(error) => panic!("unexpected managed refusal result at {after}: {error:?}"),
        }
    }
    assert!(completed);
    for limits in [
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
    ] {
        let limited = DecodeOptions::new(limits);
        let error = decode_jp2(&container, &limited).unwrap_err();
        assert!(matches!(error, DecodeError::LimitExceeded { .. }));
        assert_eq!(
            crate::decode_jp2_reconstructed(&container, &limited),
            Err(error)
        );
    }
    assert_eq!(
        crate::decode_jp2_reconstructed(&container, &options).unwrap(),
        expected
    );
}

#[test]
fn reconstructed_output_roundtrips_independent_packets_and_retains_coded_geometry() {
    let options = DecodeOptions::default();
    for (sample, packet) in [
        (1_i64, &[0xcf, 0xb4, 0x04, 0x09][..]),
        (129, &[0xc0, 0x21, 0x03][..]),
        (200, &[0xcf, 0xb4, 0x08, 0x04, 0x4f][..]),
    ] {
        let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], packet);
        let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
        bytes[cod + 9] = 0;
        for signed in [false, true] {
            bytes[42] = if signed { 0x87 } else { 7 };
            let image = crate::decode_codestream_reconstructed(&bytes, &options).unwrap();
            let component = image.component(0).unwrap();
            assert_eq!(component.fraction_bits(), 0);
            assert_eq!(component.samples(), &[sample - 128]);
            assert_eq!(component.info().signed, signed);
            assert_eq!(
                image.typed(options.limits()),
                decode_codestream(&bytes, &options)
            );
        }
    }

    let mut registered = prepared_codestream(7, 5, 1, &[0x40, 0x40], &[0]);
    let cod = registered
        .windows(2)
        .position(|pair| pair == [255, 82])
        .unwrap();
    registered[cod + 9] = 0;
    registered[16..20].copy_from_slice(&1_u32.to_be_bytes());
    registered[20..24].copy_from_slice(&1_u32.to_be_bytes());
    registered[43] = 2;
    registered[44] = 3;
    let sot = registered.windows(2).position(|p| p == [255, 144]).unwrap();
    registered.splice(sot..sot, segment(0xff63, &[0x40, 0, 0x80, 0]));
    for (bytes, geometry, dimensions, sampling) in [
        (two_tile_codestream(), (5, 1, 1, 0), (5, 1), (1, 1, 0, 0)),
        (registered, (6, 4, 1, 1), (3, 1), (2, 3, 0x4000, 0x8000)),
    ] {
        let image = crate::decode_codestream_reconstructed(&bytes, &options).unwrap();
        assert_eq!(
            (
                image.width(),
                image.height(),
                image.x_origin(),
                image.y_origin()
            ),
            geometry
        );
        let component = image.component(0).unwrap();
        let info = component.info();
        assert_eq!(
            (
                info.x_subsampling,
                info.y_subsampling,
                info.x_registration,
                info.y_registration
            ),
            sampling
        );
        assert_eq!((component.width(), component.height()), dimensions);
        assert_eq!(
            component.samples(),
            vec![0; (dimensions.0 * dimensions.1) as usize]
        );
        assert_eq!(
            image.typed(options.limits()),
            decode_codestream(&bytes, &options)
        );
    }
}

#[test]
fn reconstructed_output_retains_fractional_overshoot_before_typed_rounding_and_clipping() {
    let options = DecodeOptions::default();
    // Independent OpenJPEG entropy bytes for centered -127 and +1. With no
    // DWT levels and step 3/2, midpoint reconstruction is -765/4 and +9/4.
    for (packet, numerator, typed) in [
        (&[0xcf, 0xb4, 0x04, 0x09][..], -765_i64, 0_u64),
        (&[0xc0, 0x21, 0x03][..], 9, 130),
    ] {
        let mut bytes = prepared_codestream(1, 1, 0, &[0x42, 0x44, 0], packet);
        let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
        bytes[cod + 9] = 0;
        let image = crate::decode_codestream_reconstructed(&bytes, &options).unwrap();
        let component = image.component(0).unwrap();
        assert_eq!(component.fraction_bits(), 16);
        assert_eq!(component.samples(), &[numerator * (1 << 14)]);
        let converted = image.typed(options.limits()).unwrap();
        assert_eq!(
            converted.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![typed])
        );
        assert_eq!(Ok(converted), decode_codestream(&bytes, &options));
        if numerator < 0 {
            // Average with centered zero before final conversion: 259/8,
            // rather than the early-clipped typed average of 64.
            let late_numerator = i128::from(component.samples()[0]) + (256_i128 << 16);
            assert_eq!(late_numerator * 8, 259 * (2_i128 << 16));
            assert_ne!(
                late_numerator / (2_i128 << 16),
                i128::from((typed + 128) / 2)
            );
        }
    }
    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0]);
    let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
    bytes[cod + 9] = 0;
    let bytes = add_single_component_mct(bytes, 1, 300);
    let image = crate::decode_codestream_reconstructed(&bytes, &options).unwrap();
    assert_eq!(image.component(0).unwrap().samples(), &[300]);
    assert_eq!(
        image.typed(options.limits()),
        decode_codestream(&bytes, &options)
    );
    assert_eq!(
        image
            .typed(options.limits())
            .unwrap()
            .component(0)
            .unwrap()
            .samples(),
        &TypedSamples::Unsigned(vec![255])
    );
}

#[test]
fn reconstructed_recovery_preserves_fractional_overshoot_before_typed_conversion() {
    let options = DecodeOptions::default();
    for (packet, numerator) in [
        (&[0xcf, 0xb4, 0x04, 0x09][..], -765_i64),
        (&[0xc0, 0x21, 0x03][..], 9),
    ] {
        let mut original = prepared_codestream(1, 1, 0, &[0x42, 0x44, 0], packet);
        let cod = original
            .windows(2)
            .position(|pair| pair == [255, 82])
            .unwrap();
        original[cod + 9] = 0;
        let sot = original
            .windows(2)
            .position(|pair| pair == [255, 144])
            .unwrap();
        assert!(original.ends_with(&[0xff, 0xd9]));
        let mut bytes = original[..original.len() - 2].to_vec();
        bytes[sot + 6..sot + 10].fill(0);
        let recovered =
            crate::decode_codestream_reconstructed_recover_missing_eoc(&bytes, &options).unwrap();
        let component = recovered.image.component(0).unwrap();
        assert_eq!(component.fraction_bits(), 16);
        assert_eq!(component.samples(), &[numerator * (1 << 14)]);
        assert_eq!(
            recovered.image,
            crate::decode_codestream_reconstructed(&original, &options).unwrap()
        );
        assert_eq!(
            recovered.image.typed(options.limits()),
            decode_codestream(&original, &options)
        );
        assert!(recovered.report.appended_eoc);
        assert_eq!(recovered.report.original_bytes, bytes.len() as u64);
        assert_eq!(recovered.report.effective_bytes, original.len() as u64);
    }
}

#[test]
fn reconstructed_output_rejects_main_and_tile_typed_domain_nlt_without_masking_decode_errors() {
    let options = DecodeOptions::default();
    for tile in [false, true] {
        for kind in [0_u8, 3] {
            let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0xcf, 0xb4, 0x04, 0x09]);
            let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
            bytes[cod + 9] = 0;
            bytes[42] = 0x87;
            let sot = bytes
                .windows(2)
                .position(|pair| pair == [255, 144])
                .unwrap();
            let nlt = segment(0xff76, &[255, 255, 0x87, kind]);
            if tile {
                let length = u32::from_be_bytes(bytes[sot + 6..sot + 10].try_into().unwrap());
                bytes[sot + 6..sot + 10]
                    .copy_from_slice(&(length + nlt.len() as u32).to_be_bytes());
                bytes.splice(sot + 12..sot + 12, nlt);
            } else {
                bytes.splice(sot..sot, nlt);
            }
            assert_eq!(
                decode_codestream(&bytes, &options)
                    .unwrap()
                    .component(0)
                    .unwrap()
                    .samples(),
                &TypedSamples::Signed(vec![if kind == 0 { -127 } else { -2 }])
            );
            assert_eq!(
                crate::decode_codestream_reconstructed(&bytes, &options),
                Err(DecodeError::UnsupportedFeature {
                    feature: "nonlinear transforms on reconstruction samples"
                })
            );
            let limited =
                DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(0).unwrap());
            let expected = decode_codestream(&bytes, &limited).unwrap_err();
            assert!(matches!(
                expected,
                DecodeError::LimitExceeded {
                    resource: Resource::Packets,
                    ..
                }
            ));
            assert_eq!(
                crate::decode_codestream_reconstructed(&bytes, &limited),
                Err(expected)
            );
            let sod = bytes
                .windows(2)
                .position(|pair| pair == [255, 147])
                .unwrap();
            bytes[sod + 2] = 0xff;
            let expected = decode_codestream(&bytes, &options).unwrap_err();
            assert_eq!(
                crate::decode_codestream_reconstructed(&bytes, &options),
                Err(expected)
            );
        }
    }
}

#[test]
fn reconstructed_output_keeps_strict_errors_limits_and_success_after_failure() {
    let bytes = two_tile_codestream();
    let options = DecodeOptions::default();
    let expected = crate::decode_codestream_reconstructed(&bytes, &options).unwrap();
    for end in 0..bytes.len() {
        let error = decode_codestream(&bytes[..end], &options).unwrap_err();
        assert_eq!(
            crate::decode_codestream_reconstructed(&bytes[..end], &options),
            Err(error)
        );
    }
    for limits in [
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
    ] {
        let limited = DecodeOptions::new(limits);
        let error = decode_codestream(&bytes, &limited).unwrap_err();
        assert!(matches!(error, DecodeError::LimitExceeded { .. }));
        assert_eq!(
            crate::decode_codestream_reconstructed(&bytes, &limited),
            Err(error)
        );
        assert_eq!(
            crate::decode_codestream_reconstructed(&bytes, &options).unwrap(),
            expected
        );
    }
    let container = jp2_for_codestream(&bytes, 5, 1);
    let error = decode_codestream(&container, &options).unwrap_err();
    assert_eq!(
        crate::decode_codestream_reconstructed(&container, &options),
        Err(error)
    );
}

#[test]
fn actual_raw_typed_result_derives_full_and_reduced_signed_unsigned_planes_from_bytes() {
    let options = DecodeOptions::default();
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let mut cases = 0;
    for width in [1_u32, 2, 5, 9] {
        for height in [1_u32, 3, 7] {
            for signed in [false, true] {
                let mut bytes = prepared_codestream(width, height, 1, &qcd, &[0, 0, 0]);
                bytes[42] = if signed { 0x87 } else { 7 };
                let full = decode_codestream(&bytes, &options).unwrap();
                assert_eq!((full.width(), full.height()), (width, height));
                assert_eq!((full.x_origin(), full.y_origin()), (0, 0));
                for levels in 0..=2 {
                    let request = DecodeSelection::full_image().with_discard_levels(levels);
                    let image = decode_codestream_selected(&bytes, &options, &request).unwrap();
                    let scale = 1_u32 << levels;
                    let expected_width = width.div_ceil(scale);
                    let expected_height = height.div_ceil(scale);
                    assert_eq!(
                        (image.width(), image.height()),
                        (expected_width, expected_height)
                    );
                    assert_eq!(image.components().len(), 1);
                    let component = image.component(0).unwrap();
                    assert_eq!(component.info().precision, 8);
                    assert_eq!(component.info().signed, signed);
                    let count = usize::try_from(expected_width * expected_height).unwrap();
                    let expected = if signed {
                        TypedSamples::Signed(vec![0; count])
                    } else {
                        TypedSamples::Unsigned(vec![128; count])
                    };
                    assert_eq!(component.samples(), &expected);
                    cases += 1;
                }
                let expected = if signed {
                    TypedSamples::Signed(vec![0; (width * height) as usize])
                } else {
                    TypedSamples::Unsigned(vec![128; (width * height) as usize])
                };
                assert_eq!(full.component(0).unwrap().samples(), &expected);
            }
        }
    }
    assert_eq!(cases, 72);
}

#[test]
fn actual_raw_typed_result_preserves_parser_selection_and_backend_budget_first_errors() {
    let bytes = two_tile_codestream();
    let invalid = DecodeSelection::tile(u16::MAX);
    for (limits, expected) in [
        (
            ResourceLimits::HARDENED
                .with_maximum_input_bytes(0)
                .unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::InputBytes,
                limit: 0,
                actual: bytes.len() as u64,
            },
        ),
        (
            ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 0,
                actual: 1,
            },
        ),
    ] {
        let options = DecodeOptions::new(limits);
        assert_eq!(decode_codestream(&bytes, &options), Err(expected));
        assert_eq!(
            decode_codestream_selected(&bytes, &options, &invalid),
            Err(expected)
        );
    }
    let options = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(0).unwrap());
    assert_eq!(
        decode_codestream(&bytes, &options),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: 0,
            actual: 1
        }),
    );
    assert_eq!(
        decode_codestream_selected(&bytes, &options, &invalid),
        Err(DecodeError::InvalidSelection {
            reason: SelectionError::TileOutOfRange
        }),
    );
    for (request, reason) in [
        (
            DecodeSelection::tiles(Vec::new()),
            SelectionError::EmptyTileSet,
        ),
        (
            DecodeSelection::tiles(vec![0, 0]),
            SelectionError::DuplicateTile,
        ),
        (
            DecodeSelection::full_image().with_discard_levels(u8::MAX),
            SelectionError::ReductionTooLarge,
        ),
    ] {
        assert_eq!(
            decode_codestream_selected(&bytes, &DecodeOptions::default(), &request),
            Err(DecodeError::InvalidSelection { reason }),
        );
    }
    for end in 0..bytes.len() {
        let full = decode_codestream(&bytes[..end], &DecodeOptions::default());
        assert!(full.is_err(), "truncated source at {end}");
        assert_eq!(
            decode_codestream_selected(&bytes[..end], &DecodeOptions::default(), &invalid),
            full
        );
    }
}

#[test]
fn actual_raw_typed_result_joins_real_packed_packets_mct_and_nonlinear_regions() {
    let mut basic = prepared_codestream(1, 1, 1, &[0, 0x40], &[0]);
    let cod = basic
        .windows(2)
        .position(|pair| pair == [0xff, 0x52])
        .unwrap();
    basic[cod + 9] = 0;
    let transformed = add_second_component_mct_stage(add_single_component_mct(basic, 2, 3), -4, 5);
    for packed in [None, Some(false), Some(true)] {
        let bytes = match packed {
            None => transformed.clone(),
            Some(ppm) => pack_packet_header(transformed.clone(), ppm, &[0]),
        };
        for selected in [false, true] {
            let image = if selected {
                decode_codestream_selected(
                    &bytes,
                    &DecodeOptions::default(),
                    &DecodeSelection::full_image(),
                )
            } else {
                decode_codestream(&bytes, &DecodeOptions::default())
            }
            .unwrap();
            assert_eq!(
                image.component(0).unwrap().samples(),
                &TypedSamples::Unsigned(vec![136])
            );
        }
    }
    let mut nonlinear = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0xcf, 0xb4, 0x04, 0x09]);
    let cod = nonlinear
        .windows(2)
        .position(|pair| pair == [0xff, 0x52])
        .unwrap();
    nonlinear[cod + 9] = 0;
    nonlinear[42] = 0x87;
    let plain = decode_codestream(&nonlinear, &DecodeOptions::default()).unwrap();
    assert_eq!(
        plain.component(0).unwrap().samples(),
        &TypedSamples::Signed(vec![-127])
    );
    let sot = nonlinear
        .windows(2)
        .position(|pair| pair == [0xff, 0x90])
        .unwrap();
    nonlinear.splice(sot..sot, segment(0xff76, &[0xff, 0xff, 0x87, 3]));
    let expected = TypedSamples::Signed(vec![-2]);
    assert_eq!(
        decode_codestream(&nonlinear, &DecodeOptions::default())
            .unwrap()
            .component(0)
            .unwrap()
            .samples(),
        &expected
    );
    assert_eq!(
        decode_codestream_selected(
            &nonlinear,
            &DecodeOptions::default(),
            &DecodeSelection::full_image()
        )
        .unwrap()
        .component(0)
        .unwrap()
        .samples(),
        &expected,
    );
}

#[test]
fn actual_raw_typed_result_keeps_independently_encoded_nonzero_samples_and_selected_geometry() {
    for (sample, packet) in [
        (1, &[0xcf, 0xb4, 0x04, 0x09][..]),
        (129, &[0xc0, 0x21, 0x03][..]),
        (200, &[0xcf, 0xb4, 0x08, 0x04, 0x4f][..]),
    ] {
        let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], packet);
        let cod = bytes
            .windows(2)
            .position(|pair| pair == [0xff, 0x52])
            .unwrap();
        bytes[cod + 9] = 0;
        let full = decode_codestream(&bytes, &DecodeOptions::default()).unwrap();
        let selected = decode_codestream_selected(
            &bytes,
            &DecodeOptions::default(),
            &DecodeSelection::tile(0),
        )
        .unwrap();
        assert_eq!(full, selected);
        assert_eq!(
            full.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![sample])
        );
    }
    let bytes = two_tile_codestream();
    let request = DecodeSelection::full_image().with_region(crate::ImageRegion::new(2, 0, 3, 1));
    let selected = decode_codestream_selected(&bytes, &DecodeOptions::default(), &request).unwrap();
    assert_eq!((selected.width(), selected.height()), (3, 1));
    assert_eq!(
        selected.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(vec![128; 3])
    );
}
