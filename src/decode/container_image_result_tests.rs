use super::*;
use crate::decode::api::decode_jph_selected;
use crate::image::{ChannelAssociation, ChannelType};

fn ht_source(refinement: bool, signed: bool) -> Vec<u8> {
    let (quantization, packet): (&[u8], &[u8]) = if refinement {
        (&[0, 0x18], &[0xf1, 0x80, 0x00, 0x63, 0x00])
    } else {
        (&[0, 0x10], &[0xe4, 0xfe, 0x00, 0x63, 0x00])
    };
    let mut bytes = prepared_codestream(1, 1, 1, quantization, packet);
    bytes[6..8].copy_from_slice(&0x4000_u16.to_be_bytes());
    bytes[42] = if signed { 0x87 } else { 7 };
    let cod = bytes
        .windows(2)
        .position(|pair| pair == [0xff, 0x52])
        .unwrap();
    bytes.splice(cod..cod, segment(0xff50, &[0, 2, 0, 0, 0, 8]));
    let cod = bytes
        .windows(2)
        .position(|pair| pair == [0xff, 0x52])
        .unwrap();
    bytes[cod + 9] = 0;
    bytes[cod + 12] = 0x40;
    bytes
}

fn branded(mut bytes: Vec<u8>, brand: &[u8; 4]) -> Vec<u8> {
    bytes[20..24].copy_from_slice(brand);
    bytes[28..32].copy_from_slice(brand);
    bytes
}

#[test]
fn actual_raw_container_image_derives_signed_unsigned_full_and_reduced_planes() {
    let options = DecodeOptions::default();
    let quantization = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let mut cases = 0;
    for width in [1_u32, 2, 5, 9] {
        for height in [1_u32, 3, 7] {
            for signed in [false, true] {
                let mut stream = prepared_codestream(width, height, 1, &quantization, &[0, 0, 0]);
                stream[42] = if signed { 0x87 } else { 7 };
                let mut bytes = jp2_for_codestream(&stream, width, height);
                let ihdr = bytes.windows(4).position(|word| word == b"ihdr").unwrap();
                bytes[ihdr + 14] = stream[42];
                let full = decode_jp2(&bytes, &options).unwrap();
                assert_eq!(
                    (
                        full.width(),
                        full.height(),
                        full.x_origin(),
                        full.y_origin()
                    ),
                    (width, height, 0, 0)
                );
                for levels in 0..=2 {
                    let request = DecodeSelection::full_image().with_discard_levels(levels);
                    let image = decode_jp2_selected(&bytes, &options, &request).unwrap();
                    let scale = 1_u32 << levels;
                    let geometry = (width.div_ceil(scale), height.div_ceil(scale));
                    assert_eq!((image.width(), image.height()), geometry);
                    assert_eq!((image.x_origin(), image.y_origin()), (0, 0));
                    assert_eq!(image.components().len(), 1);
                    let component = image.component(0).unwrap();
                    assert_eq!((component.width(), component.height()), geometry);
                    assert_eq!(
                        (component.info().precision, component.info().signed),
                        (8, signed)
                    );
                    assert_eq!(
                        (
                            component.info().x_subsampling,
                            component.info().y_subsampling
                        ),
                        (1, 1)
                    );
                    assert!(component.channel_definitions().is_empty());
                    let count = usize::try_from(geometry.0 * geometry.1).unwrap();
                    let expected = if signed {
                        TypedSamples::Signed(vec![0; count])
                    } else {
                        TypedSamples::Unsigned(vec![128; count])
                    };
                    assert_eq!(component.samples(), &expected);
                    if levels == 0 {
                        assert_eq!(image, full);
                    }
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 72);
}

#[test]
fn actual_raw_container_image_preserves_requested_tiles_regions_origins_and_selected_limits() {
    let bytes = jp2_for_codestream(&two_tile_codestream(), 5, 1);
    let options = DecodeOptions::default();
    let full = decode_jp2(&bytes, &options).unwrap();
    assert_eq!(
        (
            full.width(),
            full.height(),
            full.x_origin(),
            full.y_origin()
        ),
        (5, 1, 1, 0)
    );
    for (request, width, origin) in [
        (DecodeSelection::tile(0), 2, 1),
        (DecodeSelection::tile(1), 3, 3),
        (DecodeSelection::tiles(vec![1, 0]), 5, 1),
        (
            DecodeSelection::full_image().with_region(crate::ImageRegion::new(2, 0, 3, 1)),
            3,
            2,
        ),
    ] {
        let image = decode_jp2_selected(&bytes, &options, &request).unwrap();
        assert_eq!(
            (
                image.width(),
                image.height(),
                image.x_origin(),
                image.y_origin()
            ),
            (width, 1, origin, 0)
        );
        assert_eq!(
            image.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![128; width as usize])
        );
    }
    let limited = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(1).unwrap());
    assert_eq!(
        decode_jp2(&bytes, &limited),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: 1,
            actual: 2
        })
    );
    let selected = decode_jp2_selected(&bytes, &limited, &DecodeSelection::tile(1)).unwrap();
    assert_eq!((selected.width(), selected.x_origin()), (3, 3));
    assert_eq!(
        selected.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(vec![128; 3])
    );
}

#[test]
fn actual_raw_container_image_applies_complete_palette_mapping_and_channel_definitions() {
    let mut stream = prepared_codestream(1, 1, 1, &[0, 0x40], &[0]);
    let cod = stream
        .windows(2)
        .position(|pair| pair == [0xff, 0x52])
        .unwrap();
    stream[cod + 9] = 0;
    let bytes = jp2_with_palette(&stream, 256, true);
    for image in [
        decode_jp2(&bytes, &DecodeOptions::default()).unwrap(),
        decode_jp2_selected(
            &bytes,
            &DecodeOptions::default(),
            &DecodeSelection::full_image(),
        )
        .unwrap(),
    ] {
        assert_eq!(
            (
                image.width(),
                image.height(),
                image.x_origin(),
                image.y_origin()
            ),
            (1, 1, 0, 0)
        );
        assert_eq!(image.components().len(), 3);
        for (index, precision, signed, samples, channel, association) in [
            (
                0,
                8,
                false,
                TypedSamples::Unsigned(vec![42]),
                ChannelType::Color,
                ChannelAssociation::Color(1),
            ),
            (
                1,
                5,
                true,
                TypedSamples::Signed(vec![-3]),
                ChannelType::Opacity,
                ChannelAssociation::Color(1),
            ),
            (
                2,
                8,
                false,
                TypedSamples::Unsigned(vec![128]),
                ChannelType::Unspecified,
                ChannelAssociation::Unassociated,
            ),
        ] {
            let component = image.component(index).unwrap();
            assert_eq!(
                (component.info().precision, component.info().signed),
                (precision, signed)
            );
            assert_eq!(component.samples(), &samples);
            assert_eq!(component.channel_definitions().len(), 1);
            let definition = &component.channel_definitions()[0];
            assert_eq!(
                (definition.channel_type(), definition.association()),
                (channel, association)
            );
        }
    }
    let options = DecodeOptions::new(
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(16)
            .unwrap(),
    );
    let expected = Err(DecodeError::LimitExceeded {
        resource: Resource::DecodedBytes,
        limit: 16,
        actual: 24,
    });
    assert_eq!(decode_jp2(&bytes, &options), expected);
    assert_eq!(
        decode_jp2_selected(&bytes, &options, &DecodeSelection::full_image()),
        expected
    );
}

#[test]
fn actual_raw_container_image_jph_keeps_cleanup_refinement_signedness_and_public_selection() {
    let options = DecodeOptions::default();
    for refinement in [false, true] {
        for signed in [false, true] {
            let stream = ht_source(refinement, signed);
            let mut bytes = branded(jp2_for_codestream(&stream, 1, 1), b"jph ");
            let ihdr = bytes.windows(4).position(|word| word == b"ihdr").unwrap();
            bytes[ihdr + 14] = stream[42];
            let full = decode_jph(&bytes, &options).unwrap();
            let selected =
                decode_jph_selected(&bytes, &options, &DecodeSelection::full_image()).unwrap();
            assert_eq!(selected, full);
            assert_eq!(
                (
                    full.width(),
                    full.height(),
                    full.x_origin(),
                    full.y_origin()
                ),
                (1, 1, 0, 0)
            );
            assert_eq!(full.components().len(), 1);
            let component = full.component(0).unwrap();
            assert_eq!(
                (component.info().precision, component.info().signed),
                (8, signed)
            );
            let value = if refinement { -3 } else { 1 };
            let expected = if signed {
                TypedSamples::Signed(vec![value])
            } else {
                TypedSamples::Unsigned(vec![u64::try_from(128 + value).unwrap()])
            };
            assert_eq!(component.samples(), &expected);
            assert!(component.channel_definitions().is_empty());
            assert_eq!(
                decode_jph_selected(&bytes, &options, &DecodeSelection::tile(1)),
                Err(DecodeError::InvalidSelection {
                    reason: SelectionError::TileOutOfRange
                })
            );
        }
    }
}

#[test]
fn actual_raw_container_image_preserves_raw_parse_selection_and_packet_first_errors() {
    let bytes = jp2_for_codestream(&two_tile_codestream(), 5, 1);
    let invalid = DecodeSelection::tile(u16::MAX);
    let options = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(0).unwrap());
    assert_eq!(
        decode_jp2(&bytes, &options),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: 0,
            actual: 1
        })
    );
    assert_eq!(
        decode_jp2_selected(&bytes, &options, &invalid),
        Err(DecodeError::InvalidSelection {
            reason: SelectionError::TileOutOfRange
        })
    );
    let options = DecodeOptions::new(
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
    );
    let expected = Err(DecodeError::LimitExceeded {
        resource: Resource::InputBytes,
        limit: 0,
        actual: bytes.len() as u64,
    });
    assert_eq!(decode_jp2(&bytes, &options), expected);
    assert_eq!(decode_jp2_selected(&bytes, &options, &invalid), expected);
    let options = DecodeOptions::default();
    for end in 0..bytes.len() {
        let full = decode_jp2(&bytes[..end], &options);
        assert!(full.is_err(), "truncated container at {end}");
        assert_eq!(decode_jp2_selected(&bytes[..end], &options, &invalid), full);
    }
    let bytes = branded(jp2_for_codestream(&ht_source(false, false), 1, 1), b"jph ");
    for end in 0..bytes.len() {
        let full = decode_jph(&bytes[..end], &options);
        assert!(full.is_err(), "truncated JPH container at {end}");
        assert_eq!(decode_jph_selected(&bytes[..end], &options, &invalid), full);
    }
}

#[test]
fn actual_raw_container_image_checks_inspection_before_brand_count_and_backend() {
    let options = DecodeOptions::default();
    let invalid = DecodeSelection::tile(u16::MAX);
    let stream = two_tile_codestream();
    let wrong_brand = branded(jp2_for_codestream(&stream, 5, 1), b"jpxb");
    let mut two_streams = wrong_brand.clone();
    two_streams.extend(box32(*b"jp2c", &stream));
    let profile = Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    for bytes in [&wrong_brand, &two_streams] {
        assert_eq!(decode_jp2(bytes, &options), profile);
        assert_eq!(decode_jp2_selected(bytes, &options, &invalid), profile);
    }
    let mut invalid_count = jp2_for_codestream(&stream, 5, 1);
    let second_offset = invalid_count.len() as u64;
    invalid_count.extend(box32(*b"jp2c", &stream));
    let invalid_boxes = Err(DecodeError::malformed(
        second_offset,
        MalformedKind::InvalidBoxContents,
    ));
    assert_eq!(decode_jp2(&invalid_count, &options), invalid_boxes);
    assert_eq!(
        decode_jp2_selected(&invalid_count, &options, &invalid),
        invalid_boxes
    );
    let mut bad_later = wrong_brand;
    bad_later.extend(box32(*b"jp2c", &[0]));
    let truncated = Err(DecodeError::malformed(0, MalformedKind::Truncated));
    assert_eq!(decode_jp2(&bad_later, &options), truncated);
    assert_eq!(
        decode_jp2_selected(&bad_later, &options, &invalid),
        truncated
    );
    let mismatched = jp2_for_codestream(&stream, 6, 1);
    let stream_offset = mismatched
        .windows(4)
        .position(|word| word == b"jp2c")
        .unwrap() as u64
        - 4;
    let mismatch = Err(DecodeError::malformed(
        stream_offset,
        MalformedKind::ContainerCodestreamMismatch,
    ));
    assert_eq!(decode_jp2(&mismatched, &options), mismatch);
    assert_eq!(
        decode_jp2_selected(&mismatched, &options, &invalid),
        mismatch
    );
    let jph = branded(jp2_for_codestream(&ht_source(false, false), 1, 1), b"jph ");
    assert_eq!(decode_jp2(&jph, &options), profile);
    assert_eq!(decode_jp2_selected(&jph, &options, &invalid), profile);
    let part1_jph = branded(jp2_for_codestream(&stream, 5, 1), b"jph ");
    let stream_profile = Err(DecodeError::malformed(
        stream_offset,
        MalformedKind::InvalidProfile,
    ));
    assert_eq!(decode_jph(&part1_jph, &options), stream_profile);
    assert_eq!(
        decode_jph_selected(&part1_jph, &options, &invalid),
        stream_profile
    );
}
