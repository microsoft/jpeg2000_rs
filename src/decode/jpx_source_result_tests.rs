use super::*;
use crate::{ChannelAssociation, ChannelDefinition, ChannelType};

fn source(packet: &[u8]) -> Vec<u8> {
    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], packet);
    let cod = bytes
        .windows(2)
        .position(|pair| pair == [0xff, 0x52])
        .unwrap();
    bytes[cod + 9] = 0;
    bytes
}

fn associated_source(codestream: &[u8], boxes: &[u8]) -> Vec<u8> {
    let mut bytes = jpx_for_codestreams(&[], 1, 1);
    let mut reader = jp2::BoxReader::new(&bytes, &ResourceLimits::default()).unwrap();
    reader.next_box_ref().unwrap().unwrap();
    reader.next_box_ref().unwrap().unwrap();
    let header = reader.next_box_ref().unwrap().unwrap();
    assert!(header.header.box_type().equals(jp2::BoxType::JP2_HEADER));
    let mut payload = header.payload.to_vec();
    payload.extend_from_slice(boxes);
    bytes.extend(box32(*b"jpch", &payload));
    bytes.extend(box32(*b"jp2c", codestream));
    bytes
}

#[test]
fn actual_jpx_source_result_decodes_selected_real_bytes_and_retains_actual_header_reference() {
    let one = source(&[0xcf, 0xb4, 0x04, 0x09]);
    let two_hundred = source(&[0xcf, 0xb4, 0x08, 0x04, 0x4f]);
    let options = DecodeOptions::default();
    let bytes = jpx_for_codestreams(&[one.clone(), two_hundred.clone()], 1, 1);
    let mut file = jp2::parse(&bytes, options.limits()).unwrap();
    file.header.color.precedence = u8::MAX;
    file.header.color.approximation = 7;
    file.header.nested_box_count = u32::MAX;
    file.header.palette_entries = u16::MAX;
    file.header.component_mapping_entries = u16::MAX;
    file.header.capture_resolution = Some(jp2::Resolution {
        vertical_numerator: 3,
        vertical_denominator: 2,
        horizontal_numerator: 5,
        horizontal_denominator: 4,
        vertical_exponent: -1,
        horizontal_exponent: 1,
    });
    for (index, expected) in [(0, 1), (1, 200)] {
        let (image, header) = decode_jpx_file(&file, index, &options).unwrap();
        assert_eq!(
            (
                image.width(),
                image.height(),
                image.x_origin(),
                image.y_origin()
            ),
            (1, 1, 0, 0)
        );
        assert_eq!(image.components().len(), 1);
        assert_eq!(
            image.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![expected])
        );
        assert!(std::ptr::eq(header.unwrap(), file.header()));
        assert_eq!(header.unwrap(), file.header());
    }

    let bytes = jpx_for_compositing_layers(&[one, two_hundred], 1, 1, false);
    let mut file = jp2::parse(&bytes, options.limits()).unwrap();
    file.header.image.width = 2;
    file.header.color.method = jp2::ColorMethod::AnyIcc { profile_bytes: 123 };
    for (index, expected) in [(0, 1), (1, 200)] {
        let (image, header) = decode_jpx_file(&file, index, &options).unwrap();
        let association = file.codestream(index).unwrap().codestream_header().unwrap();
        assert!(std::ptr::eq(
            header.unwrap(),
            association.parsed_header().unwrap()
        ));
        assert!(!std::ptr::eq(header.unwrap(), file.header()));
        assert_eq!(header.unwrap().image.width, 1);
        assert_eq!(
            header.unwrap().color.method(),
            jp2::ColorMethod::Enumerated { color_space: 17 }
        );
        assert_eq!(
            image.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![expected])
        );
    }
}

#[test]
fn actual_jpx_source_result_keeps_profile_lookup_and_inherited_association_priority() {
    let codestream = source(&[0xcf, 0xb4, 0x04, 0x09]);
    let bytes = jp2_for_codestream(&codestream, 1, 1);
    let file = jp2::parse(&bytes, &ResourceLimits::default()).unwrap();
    let options = DecodeOptions::new(
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
    );
    assert_eq!(
        decode_jpx_file(&file, usize::MAX, &options),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidProfile
        }),
    );
    let bytes = jpx_for_codestreams(&[codestream], 1, 1);
    let file = jp2::parse(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(
        decode_jpx_file(&file, usize::MAX, &options),
        Err(DecodeError::CodestreamIndexOutOfRange {
            index: usize::MAX,
            codestreams: 1
        }),
    );

    let mut bytes = jpx_for_codestreams(&[], 1, 1);
    bytes.extend(box32(*b"jpch", &[]));
    bytes.extend(box32(*b"jp2c", &[0xff]));
    let file = jp2::parse(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(
        file.codestream(0)
            .unwrap()
            .codestream_header()
            .unwrap()
            .parsed_header()
            .unwrap()
            .image,
        file.header().image,
    );
    assert_eq!(
        decode_jpx_file(&file, 0, &options),
        Err(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: 0,
            actual: 1,
        }),
    );
}

#[test]
fn actual_jpx_source_result_preserves_parser_header_and_backend_budget_priority() {
    let codestream = source(&[0xcf, 0xb4, 0x04, 0x09]);
    let bytes = jpx_for_codestreams(std::slice::from_ref(&codestream), 2, 1);
    let file = jp2::parse(&bytes, &ResourceLimits::default()).unwrap();
    let offset = file.codestream(0).unwrap().box_header().offset();
    let options = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(0).unwrap());
    assert_eq!(
        decode_jpx_file(&file, 0, &options),
        Err(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::ContainerCodestreamMismatch
        }),
    );
    let input_limited = DecodeOptions::new(
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
    );
    assert_eq!(
        decode_jpx_file(&file, 0, &input_limited),
        Err(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: 0,
            actual: codestream.len() as u64
        }),
    );
    let bytes = jpx_for_codestreams(std::slice::from_ref(&codestream), 1, 1);
    let mut file = jp2::parse(&bytes, &ResourceLimits::default()).unwrap();
    file.header.image.bit_depth = jp2::ComponentBitDepth::Uniform {
        bits: 7,
        signed: false,
    };
    assert_eq!(
        decode_jpx_file(&file, 0, &options),
        Err(DecodeError::MalformedInput {
            offset: file.codestream(0).unwrap().box_header().offset(),
            kind: MalformedKind::ContainerCodestreamMismatch,
        }),
    );
    file.header.image.bit_depth = jp2::ComponentBitDepth::Variable;
    assert_eq!(
        decode_jpx_file(&file, 0, &options),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: 0,
            actual: 1
        }),
    );
    for end in 0..codestream.len() {
        let prefix = codestream[..end].to_vec();
        let bytes = jpx_for_codestreams(std::slice::from_ref(&prefix), 1, 1);
        let file = jp2::parse(&bytes, &ResourceLimits::default()).unwrap();
        let expected = crate::codestream::parse(&prefix, options.limits()).unwrap_err();
        assert_eq!(
            decode_jpx_file(&file, 0, &options),
            Err(expected),
            "prefix {end}"
        );
    }
}

#[test]
fn actual_jpx_source_result_applies_real_associated_mapping_palette_definitions_and_limits() {
    let codestream = source(&[0xcf, 0xb4, 0x04, 0x09]);
    let bytes = jpx_for_codestreams(std::slice::from_ref(&codestream), 1, 1);
    let mut file = jp2::parse(&bytes, &ResourceLimits::default()).unwrap();
    file.header.component_mappings = vec![
        jp2::ComponentMapping {
            component: 0,
            mapping_type: jp2::MappingType::Direct,
        },
        jp2::ComponentMapping {
            component: 0,
            mapping_type: jp2::MappingType::Direct,
        },
    ];
    let definition = ChannelDefinition::new(ChannelType::Opacity, ChannelAssociation::WholeImage);
    file.header.channel_definition_records = vec![jp2::ChannelDefinitionRecord {
        channel: 1,
        definition,
    }];
    let options = DecodeOptions::default();
    let (image, header) = decode_jpx_file(&file, 0, &options).unwrap();
    assert!(std::ptr::eq(header.unwrap(), file.header()));
    assert_eq!(image.components().len(), 2);
    for component in image.components() {
        assert_eq!(component.samples(), &TypedSamples::Unsigned(vec![1]));
    }
    assert!(image.component(0).unwrap().channel_definitions().is_empty());
    assert_eq!(
        image.component(1).unwrap().channel_definitions(),
        &[definition]
    );
    let limits = ResourceLimits::HARDENED;
    let tight = DecodeOptions::new(limits.with_geometry_limits_for_test(
        1,
        limits.maximum_width(),
        limits.maximum_height(),
        limits.maximum_pixels(),
        limits.maximum_tiles(),
    ));
    assert_eq!(
        decode_jpx_file(&file, 0, &tight),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Components,
            limit: 1,
            actual: 2
        }),
    );

    let mut boxes = box32(*b"pclr", &[0, 2, 1, 7, 7, 200]);
    boxes.extend(box32(*b"cmap", &[0, 0, 1, 0]));
    boxes.extend(box32(*b"cdef", &[0, 1, 0, 0, 0, 0, 0, 1]));
    let bytes = associated_source(&codestream, &boxes);
    let file = jp2::parse(&bytes, options.limits()).unwrap();
    let (image, header) = decode_jpx_file(&file, 0, &options).unwrap();
    assert_eq!(
        image.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(vec![200])
    );
    assert_eq!(image.component(0).unwrap().info().precision, 8);
    assert_eq!(
        image.component(0).unwrap().channel_definitions(),
        &[ChannelDefinition::new(
            ChannelType::Color,
            ChannelAssociation::Color(1)
        )],
    );
    assert!(std::ptr::eq(
        header.unwrap(),
        file.codestream(0)
            .unwrap()
            .codestream_header()
            .unwrap()
            .parsed_header()
            .unwrap(),
    ));
    let bytes = associated_source(&source(&[0xcf, 0xb4, 0x08, 0x04, 0x4f]), &boxes);
    let file = jp2::parse(&bytes, options.limits()).unwrap();
    assert_eq!(
        decode_jpx_file(&file, 0, &options),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ContainerCodestreamMismatch
        }),
    );
}

#[test]
fn actual_raw_jpx_public_selects_real_nonzero_codestreams_and_complete_typed_planes() {
    let streams = [
        source(&[0xcf, 0xb4, 0x04, 0x09]),
        source(&[0xc0, 0x21, 0x03]),
        source(&[0xcf, 0xb4, 0x08, 0x04, 0x4f]),
    ];
    let bytes = jpx_for_codestreams(&streams, 1, 1);
    let options = DecodeOptions::default();
    for (index, value) in [(0, 1), (1, 129), (2, 200)] {
        let image = decode_jpx_codestream(&bytes, index, &options).unwrap();
        assert_eq!(
            decode_jpx_codestream_selected(&bytes, index, &options, &DecodeSelection::full_image())
                .unwrap(),
            image
        );
        assert_eq!(
            (
                image.width(),
                image.height(),
                image.x_origin(),
                image.y_origin()
            ),
            (1, 1, 0, 0)
        );
        assert_eq!(image.components().len(), 1);
        let component = image.component(0).unwrap();
        assert_eq!(
            (component.info().precision, component.info().signed),
            (8, false)
        );
        assert!(component.channel_definitions().is_empty());
        assert_eq!(component.samples(), &TypedSamples::Unsigned(vec![value]));
        let color = decode_jpx_codestream_color(&bytes, index, &options).unwrap();
        assert_eq!(
            decode_jpx_codestream_color_selected(
                &bytes,
                index,
                &options,
                &DecodeSelection::full_image()
            )
            .unwrap(),
            color
        );
        assert_eq!(
            (color.width(), color.height(), color.precision()),
            (1, 1, 16)
        );
        assert_eq!(
            color.color_space(),
            crate::color::ConvertedColorSpace::Grayscale
        );
        assert_eq!(color.channels().len(), 1);
        assert_eq!(
            color.channel(0).unwrap().channel_type(),
            crate::color::ConvertedChannelType::Gray
        );
        assert_eq!(
            color.channel(0).unwrap().samples(),
            &[u16::try_from(value).unwrap() * 257]
        );
    }
}

#[test]
fn actual_raw_jpx_public_preserves_tile_region_reduction_and_selected_source_limits() {
    let bytes = jpx_for_codestreams(&[two_tile_codestream()], 5, 1);
    let options = DecodeOptions::default();
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
        let image = decode_jpx_codestream_selected(&bytes, 0, &options, &request).unwrap();
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
        let color = decode_jpx_codestream_color_selected(&bytes, 0, &options, &request).unwrap();
        assert_eq!((color.width(), color.height()), (width, 1));
        assert_eq!(
            color.channel(0).unwrap().samples(),
            vec![32_896; width as usize]
        );
    }
    let limits = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(1).unwrap());
    assert_eq!(
        decode_jpx_codestream(&bytes, 0, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: 1,
            actual: 2
        })
    );
    let selected =
        decode_jpx_codestream_selected(&bytes, 0, &limits, &DecodeSelection::tile(1)).unwrap();
    assert_eq!((selected.width(), selected.x_origin()), (3, 3));
    for signed in [false, true] {
        let mut stream = prepared_codestream(
            5,
            3,
            1,
            &[0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50],
            &[0, 0, 0],
        );
        stream[42] = if signed { 0x87 } else { 7 };
        let mut bytes = jpx_for_codestreams(&[stream.clone()], 5, 3);
        let ihdr = bytes.windows(4).position(|word| word == b"ihdr").unwrap();
        bytes[ihdr + 14] = stream[42];
        let request = DecodeSelection::full_image().with_discard_levels(1);
        let image = decode_jpx_codestream_selected(&bytes, 0, &options, &request).unwrap();
        assert_eq!((image.width(), image.height()), (3, 2));
        assert_eq!(
            (
                image.component(0).unwrap().info().precision,
                image.component(0).unwrap().info().signed
            ),
            (8, signed)
        );
        let expected = if signed {
            TypedSamples::Signed(vec![0; 6])
        } else {
            TypedSamples::Unsigned(vec![128; 6])
        };
        assert_eq!(image.component(0).unwrap().samples(), &expected);
        let color = decode_jpx_codestream_color_selected(&bytes, 0, &options, &request).unwrap();
        assert_eq!((color.width(), color.height()), (3, 2));
        assert_eq!(color.channel(0).unwrap().samples(), &[32_896; 6]);
    }
}

#[test]
fn actual_raw_jpx_public_selected_producer_retains_actual_fallback_and_associated_header_references()
 {
    let streams = [
        source(&[0xcf, 0xb4, 0x04, 0x09]),
        source(&[0xcf, 0xb4, 0x08, 0x04, 0x4f]),
    ];
    let options = DecodeOptions::default();
    let request = DecodeSelection::full_image();
    let bytes = jpx_for_codestreams(&streams, 1, 1);
    let mut file = jp2::parse(&bytes, options.limits()).unwrap();
    file.header.color.precedence = u8::MAX;
    file.header.color.approximation = 7;
    file.header.nested_box_count = u32::MAX;
    file.header.palette_entries = u16::MAX;
    for (index, value) in [(0, 1), (1, 200)] {
        let (image, header) =
            crate::decode::output::decode_jpx_file_selected(&file, index, &options, &request)
                .unwrap();
        assert!(std::ptr::eq(header.unwrap(), file.header()));
        assert_eq!(header.unwrap(), file.header());
        assert_eq!(
            image.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![value])
        );
    }
    let bytes = jpx_for_compositing_layers(&streams, 1, 1, false);
    let mut file = jp2::parse(&bytes, options.limits()).unwrap();
    file.header.image.width = 2;
    file.header.color.method = jp2::ColorMethod::AnyIcc { profile_bytes: 123 };
    for (index, value) in [(0, 1), (1, 200)] {
        let (image, header) =
            crate::decode::output::decode_jpx_file_selected(&file, index, &options, &request)
                .unwrap();
        let associated = file
            .codestream(index)
            .unwrap()
            .codestream_header()
            .unwrap()
            .parsed_header()
            .unwrap();
        assert!(std::ptr::eq(header.unwrap(), associated));
        assert!(!std::ptr::eq(header.unwrap(), file.header()));
        assert_eq!(header.unwrap().image.width, 1);
        assert_eq!(
            header.unwrap().color.method(),
            jp2::ColorMethod::Enumerated { color_space: 17 }
        );
        assert_eq!(
            image.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![value])
        );
    }
}

#[test]
fn actual_raw_jpx_public_derives_associated_palette_rgb_and_complete_alpha_output() {
    let stream = source(&[0]);
    let options = DecodeOptions::default();
    for kind in 0..3 {
        let mut palette = 256_u16.to_be_bytes().to_vec();
        palette.extend_from_slice(&[2, 7, 0x84]);
        for entry in 0..256 {
            palette.extend_from_slice(if entry == 128 { &[42, 0x1d] } else { &[0, 0] });
        }
        let mut boxes = box32(*b"pclr", &palette);
        boxes.extend(box32(*b"cmap", &[0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]));
        let mut definitions = 3_u16.to_be_bytes().to_vec();
        for index in 0..3_u16 {
            let (channel, association) = if kind == 2 {
                (0_u16, index + 1)
            } else if index == 0 {
                (0, 1)
            } else if index == 1 {
                (kind + 1, 1)
            } else {
                (u16::MAX, u16::MAX)
            };
            definitions.extend_from_slice(&index.to_be_bytes());
            definitions.extend_from_slice(&channel.to_be_bytes());
            definitions.extend_from_slice(&association.to_be_bytes());
        }
        boxes.extend(box32(*b"cdef", &definitions));
        let mut bytes = associated_source(&stream, &boxes);
        if kind == 2 {
            let colr = bytes.windows(4).rposition(|word| word == b"colr").unwrap();
            bytes[colr + 7..colr + 11].copy_from_slice(&16_u32.to_be_bytes());
        }
        let typed = decode_jpx_codestream(&bytes, 0, &options).unwrap();
        assert_eq!(
            decode_jpx_codestream_selected(&bytes, 0, &options, &DecodeSelection::full_image())
                .unwrap(),
            typed
        );
        assert_eq!(typed.components().len(), 3);
        assert_eq!(
            typed.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![42])
        );
        assert_eq!(
            typed.component(1).unwrap().samples(),
            &TypedSamples::Signed(vec![-3])
        );
        assert_eq!(
            typed.component(2).unwrap().samples(),
            &TypedSamples::Unsigned(vec![128])
        );
        let color = decode_jpx_codestream_color(&bytes, 0, &options).unwrap();
        assert_eq!(
            decode_jpx_codestream_color_selected(
                &bytes,
                0,
                &options,
                &DecodeSelection::full_image()
            )
            .unwrap(),
            color
        );
        assert_eq!(
            (color.width(), color.height(), color.precision()),
            (1, 1, 16)
        );
        assert_eq!(color.channels().len(), if kind == 2 { 3 } else { 2 });
        assert_eq!(color.channel(0).unwrap().samples(), &[10_794]);
        assert_eq!(color.channel(1).unwrap().samples(), &[27_482]);
        if kind == 2 {
            assert_eq!(color.color_space(), crate::color::ConvertedColorSpace::Srgb);
            for (index, expected) in [
                (0, crate::color::ConvertedChannelType::Red),
                (1, crate::color::ConvertedChannelType::Green),
                (2, crate::color::ConvertedChannelType::Blue),
            ] {
                assert_eq!(color.channel(index).unwrap().channel_type(), expected);
            }
            assert_eq!(color.channel(2).unwrap().samples(), &[32_896]);
        } else {
            assert_eq!(
                color.color_space(),
                crate::color::ConvertedColorSpace::Grayscale
            );
            assert_eq!(
                color.channel(0).unwrap().channel_type(),
                crate::color::ConvertedChannelType::Gray
            );
            assert_eq!(
                color.channel(1).unwrap().channel_type(),
                crate::color::ConvertedChannelType::Alpha {
                    premultiplied: kind == 1,
                    association: ChannelAssociation::Color(1)
                }
            );
        }
    }
}

#[test]
fn actual_raw_jpx_public_inspects_only_the_chosen_payload_after_raw_profile_and_index_admission() {
    let options = DecodeOptions::default();
    let invalid = DecodeSelection::tile(u16::MAX);
    let good = source(&[0xcf, 0xb4, 0x04, 0x09]);
    let bytes = jpx_for_codestreams(&[good.clone(), vec![0xff]], 1, 1);
    let first = decode_jpx_codestream(&bytes, 0, &options).unwrap();
    assert_eq!(
        first.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(vec![1])
    );
    assert_eq!(
        decode_jpx_codestream_selected(&bytes, 0, &options, &DecodeSelection::full_image())
            .unwrap(),
        first
    );
    assert_eq!(
        decode_jpx_codestream_color(&bytes, 0, &options)
            .unwrap()
            .channel(0)
            .unwrap()
            .samples(),
        &[257]
    );
    assert_eq!(
        decode_jpx_codestream_color_selected(&bytes, 0, &options, &DecodeSelection::full_image())
            .unwrap()
            .channel(0)
            .unwrap()
            .samples(),
        &[257]
    );
    let truncated = DecodeError::malformed(0, MalformedKind::Truncated);
    assert_eq!(decode_jpx_codestream(&bytes, 1, &options), Err(truncated));
    assert_eq!(
        decode_jpx_codestream_selected(&bytes, 1, &options, &invalid),
        Err(truncated)
    );
    assert_eq!(
        decode_jpx_codestream_color(&bytes, 1, &options),
        Err(truncated)
    );
    assert_eq!(
        decode_jpx_codestream_color_selected(&bytes, 1, &options, &invalid),
        Err(truncated)
    );
    let index = DecodeError::CodestreamIndexOutOfRange {
        index: usize::MAX,
        codestreams: 2,
    };
    assert_eq!(
        decode_jpx_codestream(&bytes, usize::MAX, &options),
        Err(index)
    );
    assert_eq!(
        decode_jpx_codestream_selected(&bytes, usize::MAX, &options, &invalid),
        Err(index)
    );
    assert_eq!(
        decode_jpx_codestream_color_selected(&bytes, usize::MAX, &options, &invalid),
        Err(index)
    );
    let jp2 = jp2_for_codestream(&good, 1, 1);
    let profile = DecodeError::malformed(0, MalformedKind::InvalidProfile);
    assert_eq!(
        decode_jpx_codestream(&jp2, usize::MAX, &options),
        Err(profile)
    );
    assert_eq!(
        decode_jpx_codestream_selected(&jp2, usize::MAX, &options, &invalid),
        Err(profile)
    );
    assert_eq!(
        decode_jpx_codestream_color_selected(&jp2, usize::MAX, &options, &invalid),
        Err(profile)
    );
    let limited = DecodeOptions::new(
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
    );
    let input = DecodeError::LimitExceeded {
        resource: Resource::InputBytes,
        limit: 0,
        actual: jp2.len() as u64,
    };
    assert_eq!(
        decode_jpx_codestream(&jp2, usize::MAX, &limited),
        Err(input)
    );
    assert_eq!(
        decode_jpx_codestream_color_selected(&jp2, usize::MAX, &limited, &invalid),
        Err(input)
    );
}

#[test]
fn actual_raw_jpx_public_keeps_layout_header_selection_packet_and_palette_first_errors() {
    let stream = source(&[0]);
    let bytes = jpx_for_codestreams(&[stream], 2, 1);
    let options = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(0).unwrap());
    let file = jp2::parse(&bytes, options.limits()).unwrap();
    let mismatch = DecodeError::malformed(
        file.codestream(0).unwrap().box_header().offset(),
        MalformedKind::ContainerCodestreamMismatch,
    );
    let invalid = DecodeSelection::tile(u16::MAX);
    assert_eq!(decode_jpx_codestream(&bytes, 0, &options), Err(mismatch));
    assert_eq!(
        decode_jpx_codestream_selected(&bytes, 0, &options, &invalid),
        Err(mismatch)
    );
    assert_eq!(
        decode_jpx_codestream_color(&bytes, 0, &options),
        Err(mismatch)
    );
    assert_eq!(
        decode_jpx_codestream_color_selected(&bytes, 0, &options, &invalid),
        Err(DecodeError::InvalidSelection {
            reason: SelectionError::TileOutOfRange
        })
    );
    let bytes = jpx_for_codestreams(&[source(&[0])], 1, 1);
    let packet = DecodeError::LimitExceeded {
        resource: Resource::Packets,
        limit: 0,
        actual: 1,
    };
    assert_eq!(decode_jpx_codestream(&bytes, 0, &options), Err(packet));
    assert_eq!(
        decode_jpx_codestream_selected(&bytes, 0, &options, &DecodeSelection::full_image()),
        Err(packet)
    );
    assert_eq!(
        decode_jpx_codestream_selected(&bytes, 0, &options, &invalid),
        Err(DecodeError::InvalidSelection {
            reason: SelectionError::TileOutOfRange
        })
    );
    let defaults = DecodeOptions::default();
    for end in 0..bytes.len() {
        let full = decode_jpx_codestream(&bytes[..end], 0, &defaults);
        assert!(full.is_err(), "truncated raw JPX at {end}");
        assert_eq!(
            decode_jpx_codestream_selected(&bytes[..end], 0, &defaults, &invalid),
            full
        );
    }
}
