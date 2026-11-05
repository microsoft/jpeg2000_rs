use super::*;

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
    let transformed = add_second_component_mct_stage(add_single_component_mct(basic, 2, 3), 3, 5);
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
                &TypedSamples::Unsigned(vec![141])
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
