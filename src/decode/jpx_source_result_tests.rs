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
    let file = jp2::parse(&bytes, options.limits()).unwrap();
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
