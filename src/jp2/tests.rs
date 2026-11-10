use super::*;

type RawBoxReaderSnapshot = (usize, u64, u64, bool, ResourceLimits);

fn raw_box_reader_snapshot(reader: &BoxReader<'_>) -> RawBoxReaderSnapshot {
    (
        reader.position,
        reader.metadata_bytes,
        reader.work_units,
        reader.failed,
        reader.limits,
    )
}

#[test]
fn actual_raw_box_reader_retains_fixed_extended_to_end_headers_payload_borrows_and_charges() {
    let limits = ResourceLimits::default();
    let mut bytes = box32(*b"xml ", &[1, 2, 3]);
    bytes.extend_from_slice(&1_u32.to_be_bytes());
    bytes.extend_from_slice(b"jp2c");
    bytes.extend_from_slice(&18_u64.to_be_bytes());
    bytes.extend_from_slice(&[4, 5]);
    bytes.extend_from_slice(&0_u32.to_be_bytes());
    bytes.extend_from_slice(b"free");
    bytes.extend_from_slice(&[6, 7, 8, 9]);
    let mut reader = BoxReader::new(&bytes, &limits).unwrap();
    for (offset, header_length, total_length, kind, payload) in [
        (0, 8, 11, *b"xml ", &bytes[8..11]),
        (11, 16, 18, *b"jp2c", &bytes[27..29]),
        (29, 8, 12, *b"free", &bytes[37..41]),
    ] {
        let value = reader.next_box_ref().unwrap().unwrap();
        assert_eq!(value.header.box_type().bytes(), kind);
        assert_eq!(value.header.offset(), offset);
        assert_eq!(value.header.header_length(), header_length);
        assert_eq!(value.header.total_length(), total_length);
        assert_eq!(
            value.header.payload_offset().unwrap(),
            offset + header_length
        );
        assert_eq!(
            value.header.payload_length().unwrap(),
            total_length - header_length
        );
        assert_eq!(value.payload, payload);
        assert!(std::ptr::eq(value.payload, payload));
        assert!(std::ptr::eq(reader.input, bytes.as_slice()));
        assert_eq!(reader.limits, limits);
    }
    assert_eq!(raw_box_reader_snapshot(&reader), (41, 23, 3, false, limits));
    let complete = raw_box_reader_snapshot(&reader);
    for _ in 0..3 {
        assert!(reader.next_box_ref().is_none());
        assert_eq!(raw_box_reader_snapshot(&reader), complete);
    }
}

#[test]
fn actual_raw_box_reader_preserves_literal_length_truncation_overflow_and_sticky_error_order() {
    let limits = ResourceLimits::default();
    let check = |bytes: &[u8], kind| {
        let mut reader = BoxReader::new(bytes, &limits).unwrap();
        assert_eq!(
            reader.next_box_ref().unwrap().err(),
            Some(DecodeError::MalformedInput { offset: 0, kind })
        );
        assert_eq!(raw_box_reader_snapshot(&reader), (0, 0, 1, true, limits));
        let failed = raw_box_reader_snapshot(&reader);
        assert!(reader.next_box_ref().is_none());
        assert_eq!(raw_box_reader_snapshot(&reader), failed);
    };
    for length in 1..8 {
        check(&vec![0xaa; length], MalformedKind::Truncated);
    }
    for length in 2_u32..8 {
        let mut bytes = length.to_be_bytes().to_vec();
        bytes.extend_from_slice(b"free");
        check(&bytes, MalformedKind::InvalidBoxLength);
    }
    for length in 8..16 {
        let mut bytes = vec![0; length];
        bytes[..4].copy_from_slice(&1_u32.to_be_bytes());
        bytes[4..8].copy_from_slice(b"free");
        check(&bytes, MalformedKind::Truncated);
    }
    for total in 0_u64..16 {
        let mut bytes = 1_u32.to_be_bytes().to_vec();
        bytes.extend_from_slice(b"free");
        bytes.extend_from_slice(&total.to_be_bytes());
        check(&bytes, MalformedKind::InvalidBoxLength);
    }
    let mut bytes = 12_u32.to_be_bytes().to_vec();
    bytes.extend_from_slice(b"free");
    check(&bytes, MalformedKind::Truncated);
    let mut bytes = box32(*b"free", &[]);
    bytes.extend_from_slice(&1_u32.to_be_bytes());
    bytes.extend_from_slice(b"free");
    bytes.extend_from_slice(&u64::MAX.to_be_bytes());
    let mut reader = BoxReader::new(&bytes, &limits).unwrap();
    reader.next_box_ref().unwrap().unwrap();
    let kind = if usize::BITS == 64 {
        MalformedKind::ArithmeticOverflow
    } else {
        MalformedKind::InvalidBoxLength
    };
    assert_eq!(
        reader.next_box_ref().unwrap().err(),
        Some(DecodeError::MalformedInput { offset: 8, kind })
    );
    assert_eq!(raw_box_reader_snapshot(&reader), (8, 8, 2, true, limits));
}

#[test]
fn actual_raw_box_reader_preserves_every_resource_and_arbitrary_counter_error_frame() {
    let bytes = box32(*b"free", &[]);
    let base = ResourceLimits::default();
    for (limits, expected, metadata) in [
        (
            base.with_maximum_work_units(0).unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 0,
                actual: 1,
            },
            0,
        ),
        (
            base.with_maximum_metadata_bytes(7).unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::MetadataBytes,
                limit: 7,
                actual: 8,
            },
            8,
        ),
    ] {
        let mut reader = BoxReader::new(&bytes, &limits).unwrap();
        assert_eq!(reader.next_box_ref().unwrap().err(), Some(expected));
        assert_eq!(
            raw_box_reader_snapshot(&reader),
            (0, metadata, 1, true, limits)
        );
    }
    for (position, metadata_bytes, work_units, failed) in [
        (0, 0, u64::MAX, false),
        (0, u64::MAX, 0, false),
        (usize::MAX, 0, 0, false),
        (usize::MAX, u64::MAX, u64::MAX, true),
    ] {
        let mut reader = BoxReader {
            input: &bytes,
            limits: base,
            position,
            metadata_bytes,
            work_units,
            failed,
        };
        if failed {
            let before = raw_box_reader_snapshot(&reader);
            assert!(reader.next_box_ref().is_none());
            assert_eq!(raw_box_reader_snapshot(&reader), before);
        } else {
            assert_eq!(
                reader.next_box_ref().unwrap().err(),
                Some(DecodeError::MalformedInput {
                    offset: position as u64,
                    kind: MalformedKind::ArithmeticOverflow
                })
            );
            assert_eq!(
                raw_box_reader_snapshot(&reader),
                (
                    position,
                    metadata_bytes,
                    work_units.saturating_add(1),
                    true,
                    base
                )
            );
        }
        assert!(std::ptr::eq(reader.input, bytes.as_slice()));
    }
    let bytes = box32(*b"jp2c", &[]);
    let limits = base.with_maximum_metadata_bytes(0).unwrap();
    let mut reader = BoxReader {
        input: &bytes,
        limits,
        position: 0,
        metadata_bytes: u64::MAX,
        work_units: 0,
        failed: false,
    };
    assert!(reader.next_box_ref().unwrap().is_ok());
    assert_eq!(
        raw_box_reader_snapshot(&reader),
        (8, u64::MAX, 1, false, limits)
    );
}

#[test]
fn actual_raw_box_reader_shared_initialization_and_copy_type_constructor_match_literal_inputs() {
    let limits = ResourceLimits::default();
    for bytes in [
        [0; 4],
        [u8::MAX; 4],
        *b"jp2c",
        *b"xml ",
        [0x80, 1, 0xfe, 0x7f],
    ] {
        let kind = super::box_reader::box_type_from_bytes(bytes);
        assert_eq!(kind.0, u32::from_be_bytes(bytes));
        assert_eq!(kind.bytes(), bytes);
        assert_eq!(kind, BoxType::new(bytes));
        assert_eq!(
            super::box_reader::read_u32(bytes),
            u32::from_be_bytes(bytes)
        );
    }
    let bytes = box32(*b"free", &[1, 2, 3, 4]);
    let reader = super::box_reader::box_reader_from_input(&bytes, &limits).unwrap();
    assert_eq!(raw_box_reader_snapshot(&reader), (0, 0, 0, false, limits));
    assert!(std::ptr::eq(reader.input, bytes.as_slice()));
    let limited = limits.with_maximum_input_bytes(0).unwrap();
    for result in [
        BoxReader::new(&bytes, &limited),
        super::box_reader::box_reader_from_input(&bytes, &limited),
    ] {
        assert_eq!(
            result.err(),
            Some(DecodeError::LimitExceeded {
                resource: Resource::InputBytes,
                limit: 0,
                actual: 12,
            })
        );
    }
    let mut empty = BoxReader::new(&[], &limits).unwrap();
    assert!(empty.next_box_ref().is_none());
    assert_eq!(raw_box_reader_snapshot(&empty), (0, 0, 0, false, limits));
    assert_eq!(
        required_box(&mut empty, 91).err(),
        Some(DecodeError::MalformedInput {
            offset: 91,
            kind: MalformedKind::MissingRequiredStructure,
        })
    );
    assert_eq!(raw_box_reader_snapshot(&empty), (0, 0, 0, false, limits));
    assert_eq!(byte_at_checked(&[1, 2, 3], 1, 1, 91), Ok(3));
    assert_eq!(
        byte_at_checked(&[], usize::MAX, 1, 91),
        Err(DecodeError::MalformedInput {
            offset: 91,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    assert_eq!(
        byte_at_checked(&[], 0, 0, 91),
        Err(DecodeError::MalformedInput {
            offset: 91,
            kind: MalformedKind::InvalidBoxLength
        })
    );
    assert_eq!(add_offset(17, 25), Ok(42));
    assert_eq!(
        add_offset(u64::MAX, 1),
        Err(DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    let malformed = DecodeError::MalformedInput {
        offset: 25,
        kind: MalformedKind::Truncated,
    };
    assert_eq!(
        rebase_error(malformed, 17),
        DecodeError::MalformedInput {
            offset: 42,
            kind: MalformedKind::Truncated
        }
    );
    assert_eq!(
        rebase_error(malformed, u64::MAX),
        DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::ArithmeticOverflow
        }
    );
    let limit_error = DecodeError::LimitExceeded {
        resource: Resource::MetadataBytes,
        limit: 1,
        actual: 2,
    };
    assert_eq!(rebase_error(limit_error, u64::MAX), limit_error);
    assert_eq!(
        read_box_type_at(b"!jp2c", 1, 91),
        Ok(BoxType::CONTIGUOUS_CODESTREAM)
    );
    assert_eq!(
        read_box_type_at(&[], usize::MAX - 1, 91),
        Err(DecodeError::MalformedInput {
            offset: 91,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    assert_eq!(
        read_box_type_at(b"abc", 0, 91),
        Err(DecodeError::MalformedInput {
            offset: 91,
            kind: MalformedKind::InvalidBoxLength
        })
    );
    let bad_header = BoxHeader {
        box_type: BoxType::JP2_HEADER,
        offset: u64::MAX,
        header_length: 16,
        total_length: 8,
    };
    assert_eq!(
        bad_header.payload_offset(),
        Err(DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    assert_eq!(
        bad_header.payload_length(),
        Err(DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::InvalidBoxLength
        })
    );
}

fn box32(box_type: [u8; 4], payload: &[u8]) -> Vec<u8> {
    let length = u32::try_from(8 + payload.len()).unwrap();
    let mut bytes = length.to_be_bytes().to_vec();
    bytes.extend_from_slice(&box_type);
    bytes.extend_from_slice(payload);
    bytes
}

fn raw_file_type_box(payload: &[u8], offset: u64) -> BoxRef<'_> {
    BoxRef {
        header: BoxHeader {
            box_type: BoxType::FILE_TYPE,
            offset,
            header_length: 8,
            total_length: payload.len() as u64 + 8,
        },
        payload,
    }
}

fn raw_file_type_payload(primary: [u8; 4], minor: u32, brands: &[[u8; 4]]) -> Vec<u8> {
    let mut payload = primary.to_vec();
    payload.extend_from_slice(&minor.to_be_bytes());
    for brand in brands {
        payload.extend_from_slice(brand);
    }
    payload
}

#[test]
fn actual_raw_file_type_preserves_primary_minor_and_every_ordered_compatible_brand() {
    let limits = ResourceLimits::default();
    for minor in [0, 0x1234_5678, u32::MAX] {
        let payload = raw_file_type_payload(*b"jp2 ", minor, &[*b"jp2 ", *b"jpx ", *b"jph "]);
        let value =
            super::container::parse_file_type(raw_file_type_box(&payload, 19), &limits).unwrap();
        assert_eq!(value.brand, BoxType::JP2_BRAND);
        assert_eq!(value.minor_version, minor);
        assert_eq!(
            value.compatible_brands(),
            &[BoxType::JP2_BRAND, BoxType::JPX_BRAND, BoxType::JPH_BRAND]
        );
        assert!(value.is_jpx_compatible());
        assert!(value.is_jph_compatible());
    }
}

#[test]
fn actual_raw_file_type_keeps_length_then_count_then_ordered_duplicate_error_priority() {
    let limits = ResourceLimits::default();
    for length in (0..8).chain(9..12) {
        let payload = vec![0; length];
        assert_eq!(
            super::container::parse_file_type(raw_file_type_box(&payload, 19), &limits).err(),
            Some(DecodeError::MalformedInput {
                offset: 27,
                kind: MalformedKind::InvalidBoxLength
            })
        );
    }
    for brands in [vec![*b"jp2 ", *b"jp2 "], vec![*b"jpx ", *b"jp2 ", *b"jpx "]] {
        let payload = raw_file_type_payload(*b"jp2 ", 0, &brands);
        let limited = limits.with_maximum_compatible_brands(1).unwrap();
        assert_eq!(
            super::container::parse_file_type(raw_file_type_box(&payload, 19), &limited).err(),
            Some(DecodeError::LimitExceeded {
                resource: Resource::CompatibleBrands,
                limit: 1,
                actual: brands.len() as u64
            })
        );
        assert_eq!(
            super::container::parse_file_type(raw_file_type_box(&payload, 19), &limits).err(),
            Some(DecodeError::MalformedInput {
                offset: 27,
                kind: MalformedKind::InvalidBoxContents
            })
        );
    }
}

#[test]
fn actual_raw_file_type_retains_exact_jp2_jpx_jph_profile_admission_and_error_offsets() {
    let limits = ResourceLimits::default();
    let cases = [
        (*b"jp2 ", 0, vec![*b"jp2 "], None),
        (
            *b"jp2 ",
            0,
            vec![*b"jpx "],
            Some(MalformedKind::InvalidFileType),
        ),
        (*b"jph ", 0, vec![*b"jph "], None),
        (
            *b"jph ",
            1,
            vec![*b"jph "],
            Some(MalformedKind::InvalidProfile),
        ),
        (*b"jph ", 0, vec![], Some(MalformedKind::InvalidProfile)),
        (
            *b"jpx ",
            0,
            vec![*b"jph "],
            Some(MalformedKind::InvalidProfile),
        ),
        (
            *b"jp2 ",
            0,
            vec![*b"jph ", *b"jpx "],
            Some(MalformedKind::InvalidFileType),
        ),
        (*b"test", u32::MAX, vec![], None),
    ];
    for (primary, minor, brands, error) in cases {
        let payload = raw_file_type_payload(primary, minor, &brands);
        let file_type =
            super::container::parse_file_type(raw_file_type_box(&payload, 19), &limits).unwrap();
        assert_eq!(
            super::container::validate_file_type_profile(&file_type, 91).err(),
            error.map(|kind| DecodeError::MalformedInput { offset: 91, kind })
        );
    }
}

#[test]
fn actual_raw_file_type_checks_header_offset_first_and_preserves_unread_header_fields() {
    let limits = ResourceLimits::default();
    let reference = raw_file_type_box(&[], u64::MAX);
    assert_eq!(
        super::container::parse_file_type(reference, &limits).err(),
        Some(DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    let payload = raw_file_type_payload(*b"jp2 ", 17, &[]);
    let mut reference = raw_file_type_box(&payload, 19);
    reference.header.total_length = 0;
    reference.header.box_type = BoxType::COLOR_SPECIFICATION;
    let no_brands = limits.with_maximum_compatible_brands(0).unwrap();
    let value = super::container::parse_file_type(reference, &no_brands).unwrap();
    assert_eq!(
        (value.brand, value.minor_version, value.compatible_brands()),
        (BoxType::JP2_BRAND, 17, &[][..])
    );
    assert_eq!(reference.header.total_length(), 0);
    assert!(std::ptr::eq(reference.payload, payload.as_slice()));
}

#[test]
fn actual_container_prologue_keeps_input_work_metadata_and_signature_error_priority() {
    let limits = ResourceLimits::default();
    let bad = box32(*b"free", &[1, 2, 3, 4]);
    for (limits, expected) in [
        (
            limits.with_maximum_input_bytes(0).unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::InputBytes,
                limit: 0,
                actual: 12,
            },
        ),
        (
            limits.with_maximum_work_units(0).unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 0,
                actual: 1,
            },
        ),
        (
            limits.with_maximum_metadata_bytes(7).unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::MetadataBytes,
                limit: 7,
                actual: 12,
            },
        ),
        (
            limits,
            DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidSignature,
            },
        ),
    ] {
        assert_eq!(parse(&bad, &limits).err(), Some(expected));
    }
    let signature = box32(*b"jP  ", &SIGNATURE_MAGIC);
    assert_eq!(
        parse(&signature, &limits).err(),
        Some(DecodeError::MalformedInput {
            offset: 1,
            kind: MalformedKind::MissingRequiredStructure
        })
    );
}

#[test]
fn actual_container_prologue_keeps_box_order_length_brand_limit_and_duplicate_error_priority() {
    let limits = ResourceLimits::default();
    let signature = box32(*b"jP  ", &SIGNATURE_MAGIC);
    let mut wrong = signature.clone();
    wrong.extend(box32(*b"colr", &[]));
    assert_eq!(
        parse(&wrong, &limits).err(),
        Some(DecodeError::MalformedInput {
            offset: 12,
            kind: MalformedKind::InvalidBoxOrder
        })
    );
    let mut short = signature.clone();
    short.extend(box32(*b"ftyp", b"abc"));
    assert_eq!(
        parse(&short, &limits).err(),
        Some(DecodeError::MalformedInput {
            offset: 20,
            kind: MalformedKind::InvalidBoxLength
        })
    );
    let mut duplicates = signature;
    duplicates.extend(box32(
        *b"ftyp",
        &raw_file_type_payload(*b"jp2 ", 0, &[*b"jp2 ", *b"jp2 "]),
    ));
    let one_brand = limits.with_maximum_compatible_brands(1).unwrap();
    assert_eq!(
        parse(&duplicates, &one_brand).err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::CompatibleBrands,
            limit: 1,
            actual: 2
        })
    );
    assert_eq!(
        parse(&duplicates, &limits).err(),
        Some(DecodeError::MalformedInput {
            offset: 20,
            kind: MalformedKind::InvalidBoxContents
        })
    );
}

#[test]
fn actual_container_prologue_preserves_profile_priority_and_complete_returned_file_type() {
    let limits = ResourceLimits::default();
    let mut conflict = box32(*b"jP  ", &SIGNATURE_MAGIC);
    conflict.extend(box32(
        *b"ftyp",
        &raw_file_type_payload(*b"jp2 ", 0, &[*b"jpx "]),
    ));
    assert_eq!(
        parse(&conflict, &limits).err(),
        Some(DecodeError::MalformedInput {
            offset: 12,
            kind: MalformedKind::InvalidFileType
        })
    );
    let mut unknown = box32(*b"jP  ", &SIGNATURE_MAGIC);
    unknown.extend(box32(*b"ftyp", &raw_file_type_payload(*b"test", 0, &[])));
    assert_eq!(
        parse(&unknown, &limits).err(),
        Some(DecodeError::UnsupportedProfile {
            feature: "unrecognized JPEG 2000 file brand"
        })
    );
    let mut valid = box32(*b"jP  ", &SIGNATURE_MAGIC);
    valid.extend(box32(
        *b"ftyp",
        &raw_file_type_payload(*b"jp2 ", 17, &[*b"jp2 "]),
    ));
    assert_eq!(
        parse(&valid, &limits).err(),
        Some(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::MissingRequiredStructure
        })
    );
    valid.extend(box32(*b"jp2h", &image_header_box(1, 1)));
    valid.extend(box32(*b"jp2c", &valid_codestream(1, 1)));
    let parsed = parse(&valid, &limits).unwrap();
    assert_eq!(parsed.file_type.brand, BoxType::JP2_BRAND);
    assert_eq!(parsed.file_type.minor_version, 17);
    assert_eq!(parsed.file_type.compatible_brands(), &[BoxType::JP2_BRAND]);
}

fn marker_segment(marker: u16, payload: &[u8]) -> Vec<u8> {
    let mut bytes = marker.to_be_bytes().to_vec();
    bytes.extend_from_slice(&u16::try_from(payload.len() + 2).unwrap().to_be_bytes());
    bytes.extend_from_slice(payload);
    bytes
}

fn raw_image_header_payload(
    width: u32,
    height: u32,
    components: u16,
    depth: u8,
    flags: [u8; 2],
) -> Vec<u8> {
    let mut payload = height.to_be_bytes().to_vec();
    payload.extend_from_slice(&width.to_be_bytes());
    payload.extend_from_slice(&components.to_be_bytes());
    payload.extend_from_slice(&[depth, 7, flags[0], flags[1]]);
    payload
}

fn raw_image_header_box(payload: &[u8], offset: u64) -> BoxRef<'_> {
    BoxRef {
        header: BoxHeader {
            box_type: BoxType::IMAGE_HEADER,
            offset,
            header_length: 8,
            total_length: payload.len() as u64 + 8,
        },
        payload,
    }
}

#[test]
fn actual_raw_image_header_retains_every_copy_field_and_all_flags() {
    let limits = ResourceLimits::default();
    for (depth, expected) in [
        (
            7,
            ComponentBitDepth::Uniform {
                bits: 8,
                signed: false,
            },
        ),
        (
            0x87,
            ComponentBitDepth::Uniform {
                bits: 8,
                signed: true,
            },
        ),
        (0xff, ComponentBitDepth::Variable),
    ] {
        for color in [0, 1] {
            for property in [0, 1] {
                let payload = raw_image_header_payload(3, 2, 4, depth, [color, property]);
                let header = super::headers::parse_image_header(
                    raw_image_header_box(&payload, 19),
                    &limits,
                    100,
                )
                .unwrap();
                assert_eq!(
                    header,
                    ImageHeader {
                        width: 3,
                        height: 2,
                        components: 4,
                        bit_depth: expected,
                        unknown_color_space: color == 1,
                        intellectual_property: property == 1
                    }
                );
            }
        }
    }
}

#[test]
fn actual_raw_image_header_bit_depth_covers_every_byte_without_narrowed_admission() {
    for value in 0..=u8::MAX {
        let bits = u16::from(value % 128) + 1;
        let expected = if value == 255 {
            Ok(ComponentBitDepth::Variable)
        } else if bits <= 38 {
            Ok(ComponentBitDepth::Uniform {
                bits: u8::try_from(bits).unwrap(),
                signed: value >= 128,
            })
        } else {
            Err(DecodeError::MalformedInput {
                offset: 73,
                kind: MalformedKind::InvalidBoxContents,
            })
        };
        assert_eq!(parse_bit_depth(value, 73), expected);
    }
}

#[test]
fn actual_raw_image_header_preserves_limit_order_and_lazy_relative_offset_errors() {
    let payload = raw_image_header_payload(3, 4, 3, 38, [2, 2]);
    let base = ResourceLimits::default();
    for (limits, expected) in [
        (
            base.with_geometry_limits_for_test(1, 2, 2, 1, 1),
            DecodeError::LimitExceeded {
                resource: Resource::Width,
                limit: 2,
                actual: 3,
            },
        ),
        (
            base.with_geometry_limits_for_test(1, 4, 2, 1, 1),
            DecodeError::LimitExceeded {
                resource: Resource::Height,
                limit: 2,
                actual: 4,
            },
        ),
        (
            base.with_geometry_limits_for_test(1, 4, 5, 1, 1),
            DecodeError::LimitExceeded {
                resource: Resource::Components,
                limit: 1,
                actual: 3,
            },
        ),
        (
            base.with_geometry_limits_for_test(4, 4, 5, 1, 1),
            DecodeError::LimitExceeded {
                resource: Resource::Pixels,
                limit: 1,
                actual: 12,
            },
        ),
        (
            base,
            DecodeError::MalformedInput {
                offset: u64::MAX,
                kind: MalformedKind::InvalidBoxContents,
            },
        ),
    ] {
        assert_eq!(
            super::headers::parse_image_header(
                raw_image_header_box(&payload, 19),
                &limits,
                u64::MAX
            )
            .err(),
            Some(expected)
        );
    }
    let valid = raw_image_header_payload(1, 1, 1, 7, [0, 0]);
    assert!(
        super::headers::parse_image_header(raw_image_header_box(&valid, 19), &base, u64::MAX)
            .is_ok()
    );
    for payload in [&[][..], &valid[..13]] {
        assert_eq!(
            super::headers::parse_image_header(raw_image_header_box(payload, 19), &base, u64::MAX)
                .err(),
            Some(DecodeError::MalformedInput {
                offset: u64::MAX,
                kind: MalformedKind::ArithmeticOverflow
            })
        );
    }
    for index in [12, 13] {
        let mut invalid = valid.clone();
        invalid[index] = 2;
        assert_eq!(
            super::headers::parse_image_header(raw_image_header_box(&invalid, 19), &base, 100)
                .err(),
            Some(DecodeError::MalformedInput {
                offset: 119,
                kind: MalformedKind::InvalidBoxContents
            })
        );
        assert_eq!(
            super::headers::parse_image_header(raw_image_header_box(&invalid, 19), &base, u64::MAX)
                .err(),
            Some(DecodeError::MalformedInput {
                offset: u64::MAX,
                kind: MalformedKind::ArithmeticOverflow
            })
        );
    }
}

#[test]
fn actual_raw_image_header_bpcc_retains_length_and_first_precision_error_priority() {
    let image = ImageHeader {
        width: 1,
        height: 1,
        components: 2,
        bit_depth: ComponentBitDepth::Variable,
        unknown_color_space: false,
        intellectual_property: false,
    };
    for (payload, base, expected) in [
        (&[0, 0x87][..], 100, Ok(())),
        (
            &[0][..],
            100,
            Err(DecodeError::MalformedInput {
                offset: 119,
                kind: MalformedKind::InvalidBoxLength,
            }),
        ),
        (
            &[0xff, 38][..],
            100,
            Err(DecodeError::MalformedInput {
                offset: 119,
                kind: MalformedKind::InvalidBoxContents,
            }),
        ),
        (
            &[38, 0xff][..],
            100,
            Err(DecodeError::MalformedInput {
                offset: 100,
                kind: MalformedKind::InvalidBoxContents,
            }),
        ),
        (
            &[38, 0xff][..],
            u64::MAX,
            Err(DecodeError::MalformedInput {
                offset: u64::MAX,
                kind: MalformedKind::InvalidBoxContents,
            }),
        ),
        (
            &[0xff, 38][..],
            u64::MAX,
            Err(DecodeError::MalformedInput {
                offset: u64::MAX,
                kind: MalformedKind::ArithmeticOverflow,
            }),
        ),
    ] {
        assert_eq!(
            super::headers::validate_bpcc(raw_image_header_box(payload, 19), image, base),
            expected
        );
    }
    let empty = ImageHeader {
        components: 0,
        ..image
    };
    assert_eq!(
        super::headers::validate_bpcc(raw_image_header_box(&[], 19), empty, u64::MAX),
        Ok(())
    );
}

#[test]
fn actual_raw_inspection_retains_original_file_and_complete_source_derived_info_fields() {
    let stream = valid_codestream(64, 32);
    let bytes = boxed_file(b"jp2 \0\0\0\0jp2 ", &stream);
    let inspected = parse_and_inspect(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(inspected.file.box_count, 4);
    assert_eq!(
        (inspected.file.metadata_boxes, inspected.file.metadata_depth),
        (0, 0)
    );
    let offset = inspected.file.codestreams[0]
        .header
        .payload_offset()
        .unwrap() as usize;
    assert!(std::ptr::eq(
        inspected.file.codestreams[0].data,
        &bytes[offset..]
    ));
    assert_eq!(inspected.codestreams.len(), 1);
    let info = &inspected.codestreams[0];
    assert_eq!(
        (
            info.image_size.width,
            info.image_size.height,
            info.image_size.components
        ),
        (64, 32, 1)
    );
    assert_eq!(
        (
            info.image_size.x_origin,
            info.image_size.y_origin,
            info.image_size.tile_x_origin,
            info.image_size.tile_y_origin
        ),
        (0, 0, 0, 0)
    );
    assert_eq!(
        (
            info.image_size.tile_width,
            info.image_size.tile_height,
            info.image_size.tiles_across,
            info.image_size.tiles_down
        ),
        (64, 32, 1, 1)
    );
    assert_eq!(
        (
            info.image_size.uniform_bit_depth,
            info.image_size.uniform_signed
        ),
        (Some(8), Some(false))
    );
    assert_eq!(
        (
            info.coding_style.layers,
            info.coding_style.decomposition_levels,
            info.coding_style.code_block_width,
            info.coding_style.code_block_height
        ),
        (1, 0, 16, 16)
    );
    assert_eq!(
        info.coding_style.transform,
        codestream::WaveletTransform::Reversible5x3
    );
    assert_eq!(
        info.component_coding_styles.style(0).unwrap(),
        info.coding_style
    );
    assert_eq!(
        info.component_quantizations.quantization(0).unwrap(),
        info.quantization
    );
    assert_eq!(
        (
            info.quantization.style,
            info.quantization.guard_bits,
            info.quantization.step_count
        ),
        (codestream::QuantizationStyle::None, 0, 1)
    );
    assert_eq!(info.roi_shifts.shift(0).unwrap(), 0);
    assert!(info.progression_changes.is_empty());
    assert!(info.multiple_component_transform.is_none());
    assert!(!info.profile.is_part15());
    assert_eq!(
        (
            info.main_header_segments,
            info.tile_parts,
            info.consumed_bytes
        ),
        (3, 1, stream.len() as u64)
    );
}

#[test]
fn actual_raw_inspection_keeps_complete_container_errors_before_relative_codestream_errors() {
    let mut bytes = boxed_file(b"jp2 \0\0\0\0jp2 ", &[0]);
    let offset = bytes.len() as u64;
    bytes.push(0);
    assert_eq!(
        parse_and_inspect(&bytes, &ResourceLimits::default()).err(),
        Some(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::InvalidBoxLength,
        })
    );
    bytes.pop();
    assert_eq!(
        parse_and_inspect(&bytes, &ResourceLimits::default()).err(),
        Some(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::Truncated,
        })
    );
}

#[test]
fn actual_raw_inspection_keeps_profile_before_geometry_and_first_stream_before_later_errors() {
    for (brand, stream) in [
        (&b"jph \0\0\0\0jph "[..], valid_codestream(63, 32)),
        (&b"jp2 \0\0\0\0jp2 "[..], valid_ht_codestream(63, 32, 0x40)),
    ] {
        let bytes = boxed_file(brand, &stream);
        let offset = parse(&bytes, &ResourceLimits::default())
            .unwrap()
            .codestreams[0]
            .header
            .offset();
        assert_eq!(
            parse_and_inspect(&bytes, &ResourceLimits::default()).err(),
            Some(DecodeError::MalformedInput {
                offset,
                kind: MalformedKind::InvalidProfile,
            })
        );
    }
    let bytes = jpx_with_codestreams(
        b"jpx \0\0\0\0jpx ",
        &[valid_codestream(63, 32), vec![0]],
        &[],
    );
    let offset = parse(&bytes, &ResourceLimits::default())
        .unwrap()
        .codestreams[0]
        .header
        .offset();
    assert_eq!(
        parse_and_inspect(&bytes, &ResourceLimits::default()).err(),
        Some(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::ContainerCodestreamMismatch,
        })
    );
}

#[test]
fn actual_raw_inspection_preserves_first_only_default_and_explicit_associated_header_choices() {
    let streams = [valid_codestream(64, 32), valid_codestream(48, 16)];
    let bytes = jpx_with_codestreams(b"jpx \0\0\0\0jpx ", &streams, &[]);
    let inspected = parse_and_inspect(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(inspected.codestreams.len(), 2);
    assert_eq!(
        (
            inspected.codestreams[1].image_size.width,
            inspected.codestreams[1].image_size.height
        ),
        (48, 16)
    );
    assert!(inspected.file.codestreams[1].codestream_header.is_none());
    let headers = [Vec::new(), image_header_box(48, 16)];
    let bytes = jpx_with_codestreams(b"jpx \0\0\0\0jpx ", &streams, &headers);
    let inspected = parse_and_inspect(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(inspected.codestreams.len(), 2);
    assert_eq!(
        inspected.file.codestreams[1]
            .codestream_header
            .as_ref()
            .unwrap()
            .parsed
            .as_ref()
            .unwrap()
            .image
            .width,
        48
    );
    let headers = [Vec::new(), image_header_box(47, 16)];
    let bytes = jpx_with_codestreams(b"jpx \0\0\0\0jpx ", &streams, &headers);
    let offset = parse(&bytes, &ResourceLimits::default())
        .unwrap()
        .codestreams[1]
        .header
        .offset();
    assert_eq!(
        parse_and_inspect(&bytes, &ResourceLimits::default()).err(),
        Some(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::ContainerCodestreamMismatch,
        })
    );
}

#[test]
fn actual_raw_jph_inspection_checks_wrapper_profile_after_actual_inspection_and_all_prefixes() {
    let bytes = boxed_file(b"jp2 \0\0\0\0jp2 ", &valid_codestream(64, 32));
    for length in 0..bytes.len() {
        assert!(parse_and_inspect(&bytes[..length], &ResourceLimits::default()).is_err());
    }
    assert_eq!(
        inspect_jph(&bytes, &ResourceLimits::default()).err(),
        Some(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidProfile,
        })
    );
    let bytes = boxed_file(b"jp2 \0\0\0\0jp2 ", &[0]);
    assert_eq!(
        inspect_jph(&bytes, &ResourceLimits::default()).err(),
        Some(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::Truncated,
        })
    );
}

#[test]
fn actual_raw_jph_inspection_retains_capability_admission_independent_of_block_coding_mode() {
    for style in [0x40, 0] {
        let mut stream = valid_ht_codestream(64, 32, style);
        if style == 0 {
            let index = stream
                .windows(6)
                .position(|bytes| bytes == [0, 2, 0, 0, 0, 8])
                .unwrap();
            stream[index + 4..index + 6].copy_from_slice(&0x8008_u16.to_be_bytes());
        }
        let bytes = boxed_file(b"jph \0\0\0\0jph ", &stream);
        let inspected = inspect_jph(&bytes, &ResourceLimits::default()).unwrap();
        let info = &inspected.codestreams[0];
        assert!(info.profile.is_part15());
        assert_eq!(info.profile.uses_high_throughput(), style != 0);
        assert_eq!(info.consumed_bytes, stream.len() as u64);
        assert_eq!(inspected.file.file_type.brand, BoxType::JPH_BRAND);
    }
}

fn valid_codestream(width: u32, height: u32) -> Vec<u8> {
    let mut siz = Vec::new();
    siz.extend_from_slice(&0_u16.to_be_bytes());
    siz.extend_from_slice(&width.to_be_bytes());
    siz.extend_from_slice(&height.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&width.to_be_bytes());
    siz.extend_from_slice(&height.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&1_u16.to_be_bytes());
    siz.extend_from_slice(&[7, 1, 1]);

    let mut bytes = 0xff4f_u16.to_be_bytes().to_vec();
    bytes.extend(marker_segment(0xff51, &siz));
    bytes.extend(marker_segment(0xff52, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]));
    bytes.extend(marker_segment(0xff5c, &[0, 0]));
    let tile_part_start = bytes.len();
    let mut sot = Vec::new();
    sot.extend_from_slice(&0_u16.to_be_bytes());
    sot.extend_from_slice(&14_u32.to_be_bytes());
    sot.extend_from_slice(&[0, 1]);
    bytes.extend(marker_segment(0xff90, &sot));
    bytes.extend_from_slice(&0xff93_u16.to_be_bytes());
    assert_eq!(bytes.len() - tile_part_start, 14);
    bytes.extend_from_slice(&0xffd9_u16.to_be_bytes());
    bytes
}

#[test]
fn actual_raw_color_header_preserves_enumerated_method_and_all_metadata_bytes() {
    for space in [0_u32, 16, 17, 18, u32::MAX] {
        for precedence in [0, u8::MAX] {
            for approximation in [0, u8::MAX] {
                let mut payload = vec![1, precedence, approximation];
                payload.extend_from_slice(&space.to_be_bytes());
                let color = parse_color_specification(raw_image_header_box(&payload, 19), u64::MAX)
                    .unwrap();
                assert_eq!(
                    color.method(),
                    ColorMethod::Enumerated { color_space: space }
                );
                assert_eq!(
                    (color.precedence, color.approximation),
                    (precedence, approximation)
                );
                assert_eq!(color.icc_profile(), None);
            }
        }
    }
}

#[test]
fn actual_raw_color_header_copies_every_restricted_and_unrestricted_icc_byte() {
    for method in [2, 3] {
        for length in [1, 2, 257] {
            let profile: Vec<u8> = (0..length)
                .map(|index| u8::try_from(index % 256).unwrap())
                .collect();
            let mut payload = vec![method, 173, 219];
            payload.extend_from_slice(&profile);
            let color = parse_color_specification(raw_image_header_box(&payload, 19), 100).unwrap();
            let expected = if method == 2 {
                ColorMethod::RestrictedIcc {
                    profile_bytes: length as u64,
                }
            } else {
                ColorMethod::AnyIcc {
                    profile_bytes: length as u64,
                }
            };
            assert_eq!(color.method(), expected);
            assert_eq!((color.precedence, color.approximation), (173, 219));
            assert_eq!(color.icc_profile(), Some(profile.as_slice()));
            assert_ne!(color.icc_profile().unwrap().as_ptr(), payload[3..].as_ptr());
        }
    }
}

#[test]
fn actual_raw_color_header_preserves_exact_length_method_and_lazy_offset_errors() {
    for payload in [
        &[][..],
        &[1][..],
        &[1, 0][..],
        &[1, 0, 0][..],
        &[2, 0, 0][..],
        &[3, 0, 0][..],
    ] {
        assert_eq!(
            parse_color_specification(raw_image_header_box(payload, 19), 100).err(),
            Some(DecodeError::MalformedInput {
                offset: 119,
                kind: MalformedKind::InvalidBoxLength
            })
        );
        assert_eq!(
            parse_color_specification(raw_image_header_box(payload, 19), u64::MAX).err(),
            Some(DecodeError::MalformedInput {
                offset: u64::MAX,
                kind: MalformedKind::ArithmeticOverflow
            })
        );
    }
    for method in [0, 4, u8::MAX] {
        let payload = [method, 0, 0];
        assert_eq!(
            parse_color_specification(raw_image_header_box(&payload, 19), 100).err(),
            Some(DecodeError::MalformedInput {
                offset: 119,
                kind: MalformedKind::InvalidColorSpecification
            })
        );
    }
    for method in [2, 3] {
        assert!(
            parse_color_specification(raw_image_header_box(&[method, 0, 0, 7], 19), u64::MAX)
                .is_ok()
        );
    }
}

#[test]
fn actual_raw_color_header_owned_profile_is_independent_of_original_source_storage() {
    let mut payload = vec![3, 255, 254, 1, 128, 255, 0, 17];
    let color = parse_color_specification(raw_image_header_box(&payload, 19), 100).unwrap();
    payload.fill(0);
    assert_eq!(color.method(), ColorMethod::AnyIcc { profile_bytes: 5 });
    assert_eq!((color.precedence, color.approximation), (255, 254));
    assert_eq!(color.icc_profile(), Some(&[1, 128, 255, 0, 17][..]));
}

#[test]
fn actual_raw_component_mapping_retains_order_repeats_and_every_record_field() {
    let payload = [0, 0, 0, 0, 0, 2, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0];
    let mappings = parse_component_mapping(
        raw_image_header_box(&payload, 19),
        3,
        2,
        &ResourceLimits::default(),
        u64::MAX,
    )
    .unwrap();
    assert_eq!(
        mappings,
        vec![
            ComponentMapping {
                component: 0,
                mapping_type: MappingType::Direct
            },
            ComponentMapping {
                component: 2,
                mapping_type: MappingType::Palette { column: 1 }
            },
            ComponentMapping {
                component: 1,
                mapping_type: MappingType::Palette { column: 0 }
            },
            ComponentMapping {
                component: 0,
                mapping_type: MappingType::Direct
            }
        ]
    );
}

#[test]
fn actual_raw_component_mapping_covers_every_method_and_column_byte() {
    for kind in 0..=u8::MAX {
        for column in 0..=u8::MAX {
            let payload = [0, 0, kind, column];
            let result = parse_component_mapping(
                raw_image_header_box(&payload, 19),
                1,
                2,
                &ResourceLimits::default(),
                100,
            );
            if (kind == 0 && column == 0) || (kind == 1 && column < 2) {
                assert_eq!(result.unwrap()[0].component, 0);
            } else {
                assert_eq!(
                    result,
                    Err(DecodeError::MalformedInput {
                        offset: 119,
                        kind: MalformedKind::InvalidBoxContents
                    })
                );
            }
        }
    }
}

#[test]
fn actual_raw_component_mapping_keeps_length_conversion_limit_and_lazy_error_priority() {
    let limits = ResourceLimits::default().with_geometry_limits_for_test(0, 1, 1, 1, 1);
    for payload in [&[][..], &[0][..], &[0, 0][..], &[0, 0, 0][..], &[0; 5][..]] {
        assert_eq!(
            parse_component_mapping(raw_image_header_box(payload, 19), 0, 0, &limits, 100),
            Err(DecodeError::MalformedInput {
                offset: 119,
                kind: MalformedKind::InvalidBoxLength
            })
        );
    }
    assert_eq!(
        parse_component_mapping(
            raw_image_header_box(&[0, 1, 255, 255], 19),
            0,
            0,
            &limits,
            u64::MAX
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Components,
            limit: 0,
            actual: 1
        })
    );
    let payload = vec![0; (usize::from(u16::MAX) + 1) * 4];
    assert_eq!(
        parse_component_mapping(raw_image_header_box(&payload, 19), 0, 0, &limits, 100),
        Err(DecodeError::MalformedInput {
            offset: 100,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    assert_eq!(
        parse_component_mapping(
            raw_image_header_box(&[0, 0, 1, 0], 19),
            1,
            0,
            &ResourceLimits::default(),
            u64::MAX
        ),
        Err(DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
}

fn raw_channel_definition_payload(records: &[(u16, u16, u16)]) -> Vec<u8> {
    let mut payload = u16::try_from(records.len()).unwrap().to_be_bytes().to_vec();
    for (channel, kind, association) in records {
        payload.extend_from_slice(&channel.to_be_bytes());
        payload.extend_from_slice(&kind.to_be_bytes());
        payload.extend_from_slice(&association.to_be_bytes());
    }
    payload
}

#[test]
fn actual_raw_channel_definition_retains_order_repeats_types_and_associations() {
    let mut raw = Vec::new();
    let mut expected = Vec::new();
    for (kind, channel_type) in [
        (0, ChannelType::Color),
        (1, ChannelType::Opacity),
        (2, ChannelType::PremultipliedOpacity),
        (u16::MAX, ChannelType::Unspecified),
    ] {
        for (association, value) in [
            (0, ChannelAssociation::WholeImage),
            (1, ChannelAssociation::Color(1)),
            (u16::MAX, ChannelAssociation::Unassociated),
        ] {
            raw.push((2, kind, association));
            expected.push(ChannelDefinitionRecord {
                channel: 2,
                definition: ChannelDefinition::new(channel_type, value),
            });
        }
    }
    raw.push(raw[0]);
    expected.push(expected[0]);
    let payload = raw_channel_definition_payload(&raw);
    assert_eq!(
        parse_channel_definition(raw_image_header_box(&payload, 19), 3, u64::MAX).unwrap(),
        expected
    );
}

#[test]
fn actual_raw_channel_definition_keeps_all_channel_type_and_association_boundaries() {
    for output in [0, 1, u16::MAX] {
        for channel in [0, 1, u16::MAX - 1, u16::MAX] {
            for kind in [0, 1, 2, 3, u16::MAX - 1, u16::MAX] {
                for association in [0, 1, 2, u16::MAX - 1, u16::MAX] {
                    let payload = raw_channel_definition_payload(&[(channel, kind, association)]);
                    let result =
                        parse_channel_definition(raw_image_header_box(&payload, 19), output, 100);
                    let valid = channel < output
                        && matches!(kind, 0 | 1 | 2 | u16::MAX)
                        && (association <= output || association == u16::MAX);
                    if valid {
                        assert_eq!(result.unwrap()[0].channel, channel);
                    } else {
                        assert_eq!(
                            result,
                            Err(DecodeError::MalformedInput {
                                offset: 119,
                                kind: MalformedKind::InvalidBoxContents
                            })
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn actual_raw_channel_definition_keeps_exact_lengths_full_count_and_lazy_offsets() {
    for payload in [
        &[][..],
        &[0][..],
        &[0, 0][..],
        &[0, 1][..],
        &[0, 1, 0, 0][..],
        &[0; 9][..],
    ] {
        assert_eq!(
            parse_channel_definition(raw_image_header_box(payload, 19), 0, 100),
            Err(DecodeError::MalformedInput {
                offset: 119,
                kind: MalformedKind::InvalidBoxLength
            })
        );
        assert_eq!(
            parse_channel_definition(raw_image_header_box(payload, 19), 0, u64::MAX),
            Err(DecodeError::MalformedInput {
                offset: u64::MAX,
                kind: MalformedKind::ArithmeticOverflow
            })
        );
    }
    let mut payload = u16::MAX.to_be_bytes().to_vec();
    payload.resize(2 + usize::from(u16::MAX) * 6, 0);
    let records =
        parse_channel_definition(raw_image_header_box(&payload, 19), 1, u64::MAX).unwrap();
    assert_eq!(records.len(), usize::from(u16::MAX));
    assert!(records.iter().all(|record| record.channel == 0
        && record.definition
            == ChannelDefinition::new(ChannelType::Color, ChannelAssociation::WholeImage)));
}

fn raw_resolution_payload() -> Vec<u8> {
    let mut payload = Vec::new();
    for value in [1_u16, 257, 513, u16::MAX] {
        payload.extend_from_slice(&value.to_be_bytes());
    }
    payload.extend_from_slice(&[0x80, 0x7f]);
    payload
}

#[test]
fn actual_raw_resolution_retains_all_fields_and_every_signed_exponent_byte() {
    for exponent in 0..=u8::MAX {
        let mut payload = raw_resolution_payload();
        payload[8] = exponent;
        payload[9] = u8::MAX - exponent;
        assert_eq!(
            super::metadata::parse_resolution(raw_image_header_box(&payload, 19), u64::MAX)
                .unwrap(),
            Resolution {
                vertical_numerator: 1,
                vertical_denominator: 257,
                horizontal_numerator: 513,
                horizontal_denominator: u16::MAX,
                vertical_exponent: exponent as i8,
                horizontal_exponent: (u8::MAX - exponent) as i8,
            }
        );
    }
}

#[test]
fn actual_raw_resolution_keeps_exact_length_zero_fields_and_lazy_relative_errors() {
    for length in [0, 1, 9, 11] {
        let payload = vec![1; length];
        assert_eq!(
            super::metadata::parse_resolution(raw_image_header_box(&payload, 19), 100),
            Err(DecodeError::MalformedInput {
                offset: 119,
                kind: MalformedKind::InvalidBoxLength
            })
        );
    }
    for position in [0, 2, 4, 6] {
        let mut payload = raw_resolution_payload();
        payload[position..position + 2].fill(0);
        for (base, offset, kind) in [
            (100, 119, MalformedKind::InvalidBoxContents),
            (u64::MAX, u64::MAX, MalformedKind::ArithmeticOverflow),
        ] {
            assert_eq!(
                super::metadata::parse_resolution(raw_image_header_box(&payload, 19), base),
                Err(DecodeError::MalformedInput { offset, kind })
            );
        }
    }
}

#[test]
fn actual_raw_resolution_superbox_retains_both_orders_unknowns_and_duplicate_priority() {
    let capture_payload = raw_resolution_payload();
    let mut display_payload = raw_resolution_payload();
    display_payload[8] = 9;
    let capture =
        super::metadata::parse_resolution(raw_image_header_box(&capture_payload, 19), 100).unwrap();
    let display =
        super::metadata::parse_resolution(raw_image_header_box(&display_payload, 19), 100).unwrap();
    let capture_box = box32(*b"resc", &capture_payload);
    let display_box = box32(*b"resd", &display_payload);
    for boxes in [[&capture_box, &display_box], [&display_box, &capture_box]] {
        let mut payload = box32(*b"free", &[1, 2, 3]);
        payload.extend_from_slice(boxes[0]);
        payload.extend_from_slice(&box32(*b"jp2c", &[7]));
        payload.extend_from_slice(boxes[1]);
        assert_eq!(
            parse_resolution_superbox(&payload, &ResourceLimits::default(), u64::MAX),
            Ok((Some(capture), Some(display)))
        );
    }
    let mut payload = capture_box;
    payload.extend_from_slice(&box32(*b"resc", &[]));
    assert_eq!(
        parse_resolution_superbox(&payload, &ResourceLimits::default(), 100),
        Err(DecodeError::MalformedInput {
            offset: 118,
            kind: MalformedKind::InvalidBoxOrder
        })
    );
    let mut payload = display_box;
    payload.extend_from_slice(&box32(*b"resd", &[]));
    assert_eq!(
        parse_resolution_superbox(&payload, &ResourceLimits::default(), 100),
        Err(DecodeError::MalformedInput {
            offset: 118,
            kind: MalformedKind::InvalidBoxOrder
        })
    );
}

#[test]
fn actual_raw_resolution_superbox_keeps_input_limit_then_progress_before_reader_errors() {
    let capture = box32(*b"resc", &raw_resolution_payload());
    assert_eq!(
        parse_resolution_superbox(
            &capture,
            &ResourceLimits::default()
                .with_maximum_input_bytes(1)
                .unwrap(),
            100
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: 1,
            actual: 18
        })
    );
    assert_eq!(
        parse_resolution_superbox(
            &capture,
            &ResourceLimits::default()
                .with_maximum_metadata_bytes(1)
                .unwrap(),
            100
        ),
        Err(DecodeError::MalformedInput {
            offset: 100,
            kind: MalformedKind::InvalidBoxLength
        })
    );
    let mut payload = capture;
    payload.extend_from_slice(&[0, 0, 0]);
    assert_eq!(
        parse_resolution_superbox(&payload, &ResourceLimits::default(), 100),
        Err(DecodeError::MalformedInput {
            offset: 118,
            kind: MalformedKind::InvalidBoxLength
        })
    );
    payload.truncate(18);
    payload.extend_from_slice(&box32(*b"free", &[]));
    let limits = ResourceLimits::default()
        .with_maximum_work_units(1)
        .unwrap();
    assert_eq!(
        parse_resolution_superbox(&payload, &limits, u64::MAX),
        Err(DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    for payload in [&[][..], box32(*b"free", &[]).as_slice()] {
        assert_eq!(
            parse_resolution_superbox(payload, &ResourceLimits::default(), 100),
            Err(DecodeError::MalformedInput {
                offset: 100,
                kind: MalformedKind::MissingRequiredStructure
            })
        );
    }
}

#[test]
fn actual_raw_metadata_copy_retains_every_byte_and_independent_owned_storage() {
    for length in [0, 1, 257, 4096] {
        let mut input: Vec<u8> = (0..length).map(|index| (index % 256) as u8).collect();
        let expected = input.clone();
        let output = super::metadata::copy_bytes(&input).unwrap();
        if length > 0 {
            assert_ne!(input.as_ptr(), output.as_ptr());
        }
        input.fill(0);
        assert_eq!(output, expected);
    }
}

#[test]
fn actual_raw_palette_value_keeps_every_precision_and_length_admission_boundary() {
    for precision in 0..=u8::MAX {
        for length in 0..=6 {
            for signed in [false, true] {
                let bytes = vec![255; length];
                let result = super::color::parse_palette_value(&bytes, precision, signed, 197);
                if precision == 0 || precision > 38 || length == 0 || length > 5 {
                    assert_eq!(
                        result,
                        Err(DecodeError::MalformedInput {
                            offset: 197,
                            kind: MalformedKind::InvalidBoxContents
                        })
                    );
                } else {
                    let raw = (1_u64 << (length * 8)) - 1;
                    let modulus = 1_u64 << precision;
                    let value = raw % modulus;
                    let expected = if signed && value >= modulus / 2 {
                        i128::from(value) - i128::from(modulus)
                    } else {
                        i128::from(value)
                    };
                    assert_eq!(result, Ok(i64::try_from(expected).unwrap()));
                }
            }
        }
    }
}

#[test]
fn actual_raw_palette_value_retains_every_byte_value_with_native_padding_and_signedness() {
    for precision in 1..=38 {
        for byte in 0..=u8::MAX {
            for signed in [false, true] {
                let modulus = 1_u64 << precision;
                let value = u64::from(byte) % modulus;
                let expected = if signed && value >= modulus / 2 {
                    i128::from(value) - i128::from(modulus)
                } else {
                    i128::from(value)
                };
                assert_eq!(
                    super::color::parse_palette_value(&[byte], precision, signed, u64::MAX),
                    Ok(i64::try_from(expected).unwrap())
                );
            }
        }
    }
}

#[test]
fn actual_raw_palette_value_keeps_big_endian_five_byte_mask_and_sign_boundaries() {
    for bytes in [
        &[0][..],
        &[0x80][..],
        &[0x80, 0x01][..],
        &[0x7f, 0xff, 0x01][..],
        &[0x80, 0x00, 0x00, 0x01][..],
        &[0xff, 0xff, 0xff, 0xff, 0xff][..],
        &[0x20, 0x00, 0x00, 0x00, 0x00][..],
    ] {
        let raw = bytes
            .iter()
            .fold(0_u64, |value, byte| value * 256 + u64::from(*byte));
        for precision in 1..=38 {
            for signed in [false, true] {
                let modulus = 1_u64 << precision;
                let value = raw % modulus;
                let expected = if signed && value >= modulus / 2 {
                    i128::from(value) - i128::from(modulus)
                } else {
                    i128::from(value)
                };
                assert_eq!(
                    super::color::parse_palette_value(bytes, precision, signed, 197),
                    Ok(i64::try_from(expected).unwrap())
                );
            }
        }
    }
}

#[test]
fn actual_raw_palette_rows_retain_the_original_column_and_value_owners() {
    let payload = [
        0, 2, 3, 0, 0x87, 37, 0xff, 0x80, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x7f, 0x20, 0x00,
        0x00, 0x00, 0x00,
    ];
    let palette = parse_palette(raw_image_header_box(&payload, 19), u64::MAX).unwrap();
    assert_eq!(palette.entries, 2);
    assert_eq!(
        palette.columns,
        vec![
            PaletteColumn {
                precision: 1,
                signed: false
            },
            PaletteColumn {
                precision: 8,
                signed: true
            },
            PaletteColumn {
                precision: 38,
                signed: false
            },
        ]
    );
    assert_eq!(
        palette.values,
        vec![1, -128, (1_i64 << 38) - 1, 0, 127, 1_i64 << 37]
    );
}

#[test]
fn actual_raw_palette_result_keeps_every_descriptor_byte_and_complete_owned_fields() {
    for descriptor in 0..=u8::MAX {
        let bits = descriptor % 128 + 1;
        let mut payload = vec![0, 1, 1, descriptor];
        if descriptor != u8::MAX && bits <= 38 {
            payload.resize(4 + usize::from(bits).div_ceil(8), u8::MAX);
        }
        let result = parse_palette(raw_image_header_box(&payload, 19), 100);
        if descriptor == u8::MAX {
            assert_eq!(
                result.err(),
                Some(DecodeError::MalformedInput {
                    offset: 119,
                    kind: MalformedKind::InvalidBoxContents
                })
            );
        } else if bits > 38 {
            assert_eq!(
                result.err(),
                Some(DecodeError::MalformedInput {
                    offset: 100,
                    kind: MalformedKind::InvalidBoxContents
                })
            );
        } else {
            let palette = result.unwrap();
            assert_eq!(palette.entries, 1);
            assert_eq!(
                palette.columns,
                vec![PaletteColumn {
                    precision: bits,
                    signed: descriptor >= 128
                }]
            );
            assert_eq!(
                palette.values,
                vec![if descriptor >= 128 {
                    -1
                } else {
                    (1_i64 << bits) - 1
                }]
            );
        }
    }
}

#[test]
fn actual_raw_palette_result_keeps_dimension_descriptor_then_sample_error_priority() {
    for payload in [&[][..], &[0][..], &[0, 1][..], &[0, 1, 2, 38][..]] {
        assert_eq!(
            parse_palette(raw_image_header_box(payload, 19), 100).err(),
            Some(DecodeError::MalformedInput {
                offset: 119,
                kind: MalformedKind::InvalidBoxLength
            })
        );
    }
    for (payload, offset, kind) in [
        (&[0, 0, 1][..], 119, MalformedKind::InvalidBoxContents),
        (&[0, 1, 0][..], 119, MalformedKind::InvalidBoxContents),
        (
            &[0, 1, 2, 38, 255][..],
            100,
            MalformedKind::InvalidBoxContents,
        ),
        (
            &[0, 1, 2, 255, 38][..],
            119,
            MalformedKind::InvalidBoxContents,
        ),
        (&[0, 1, 1, 37][..], 119, MalformedKind::InvalidBoxLength),
        (
            &[0, 1, 1, 0, 1, 2][..],
            119,
            MalformedKind::InvalidBoxLength,
        ),
    ] {
        assert_eq!(
            parse_palette(raw_image_header_box(payload, 19), 100).err(),
            Some(DecodeError::MalformedInput { offset, kind })
        );
    }
    assert_eq!(
        parse_palette(raw_image_header_box(&[0, 1, 2, 38, 255], 19), u64::MAX).err(),
        Some(DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::InvalidBoxContents
        })
    );
    assert_eq!(
        parse_palette(raw_image_header_box(&[0, 1, 2, 255, 38], 19), u64::MAX).err(),
        Some(DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
}

#[test]
fn actual_raw_palette_result_retains_ordered_mixed_width_rows_and_source_independent_owners() {
    for entries in [1_u16, 2, 257] {
        let mut payload = entries.to_be_bytes().to_vec();
        payload.extend_from_slice(&[4, 0, 7, 0x87, 37]);
        let mut expected = Vec::new();
        for entry in 0..entries {
            let byte = (entry % 256) as u8;
            payload.extend_from_slice(&[byte, byte, byte, 0, 0, 0, 0, byte]);
            expected.extend_from_slice(&[
                i64::from(byte % 2),
                i64::from(byte),
                i64::from(byte as i8),
                i64::from(byte),
            ]);
        }
        let palette = parse_palette(raw_image_header_box(&payload, 19), u64::MAX).unwrap();
        payload.fill(0);
        assert_eq!(palette.entries, entries);
        assert_eq!(
            palette.columns,
            vec![
                PaletteColumn {
                    precision: 1,
                    signed: false
                },
                PaletteColumn {
                    precision: 8,
                    signed: false
                },
                PaletteColumn {
                    precision: 8,
                    signed: true
                },
                PaletteColumn {
                    precision: 38,
                    signed: false
                },
            ]
        );
        assert_eq!(palette.values, expected);
    }
}

#[test]
fn actual_raw_palette_result_admits_the_full_entry_and_column_counts_without_narrowing() {
    let mut payload = u16::MAX.to_be_bytes().to_vec();
    payload.extend_from_slice(&[1, 0]);
    payload.resize(4 + usize::from(u16::MAX), u8::MAX);
    let palette = parse_palette(raw_image_header_box(&payload, 19), u64::MAX).unwrap();
    assert_eq!(palette.entries, u16::MAX);
    assert_eq!(palette.columns.len(), 1);
    assert_eq!(palette.values, vec![1; usize::from(u16::MAX)]);

    let mut payload = vec![0, 1, u8::MAX];
    payload.resize(3 + usize::from(u8::MAX), 0);
    payload.resize(3 + 2 * usize::from(u8::MAX), u8::MAX);
    let palette = parse_palette(raw_image_header_box(&payload, 19), u64::MAX).unwrap();
    assert_eq!(palette.entries, 1);
    assert_eq!(
        palette.columns,
        vec![
            PaletteColumn {
                precision: 1,
                signed: false
            };
            usize::from(u8::MAX)
        ]
    );
    assert_eq!(palette.values, vec![1; usize::from(u8::MAX)]);
}

fn raw_jp2_header_image(depth: u8, components: u16) -> Vec<u8> {
    box32(
        *b"ihdr",
        &raw_image_header_payload(3, 2, components, depth, [1, 1]),
    )
}

fn raw_jp2_header_color() -> Vec<u8> {
    box32(*b"colr", &[1, 3, 4, 0, 0, 0, 16])
}

#[test]
fn actual_raw_jp2_header_retains_every_owned_metadata_field_from_real_raw_producers() {
    let mut payload = raw_jp2_header_image(u8::MAX, 3);
    payload.extend_from_slice(&box32(*b"bpcc", &[7, 0x87, 37]));
    payload.extend_from_slice(&box32(*b"colr", &[3, 173, 219, 1, 128, 255, 0, 17]));
    payload.extend_from_slice(&box32(*b"pclr", &[0, 2, 2, 7, 0x87, 5, 0x80, 7, 0x7f]));
    payload.extend_from_slice(&box32(*b"cmap", &[0, 0, 1, 0, 0, 1, 1, 1]));
    payload.extend_from_slice(&box32(
        *b"cdef",
        &raw_channel_definition_payload(&[(0, 0, 1), (1, 2, 0)]),
    ));
    let mut resolution = box32(*b"resc", &raw_resolution_payload());
    let mut display = raw_resolution_payload();
    display[8] = 9;
    resolution.extend_from_slice(&box32(*b"resd", &display));
    payload.extend_from_slice(&box32(*b"res ", &resolution));
    payload.extend_from_slice(&box32(*b"xml ", &[9, 8, 7]));
    let header =
        super::headers::parse_jp2_header(&payload, &ResourceLimits::default(), 100).unwrap();
    payload.fill(0);
    assert_eq!(
        header.image,
        ImageHeader {
            width: 3,
            height: 2,
            components: 3,
            bit_depth: ComponentBitDepth::Variable,
            unknown_color_space: true,
            intellectual_property: true,
        }
    );
    assert_eq!(
        header.color.method(),
        ColorMethod::AnyIcc { profile_bytes: 5 }
    );
    assert_eq!(
        (header.color.precedence, header.color.approximation),
        (173, 219)
    );
    assert_eq!(header.color.icc_profile(), Some(&[1, 128, 255, 0, 17][..]));
    assert_eq!(
        (
            header.nested_box_count,
            header.palette_entries,
            header.palette_columns
        ),
        (8, 2, 2)
    );
    assert_eq!(
        (header.component_mapping_entries, header.channel_definitions),
        (2, 2)
    );
    let palette = header.palette.unwrap();
    assert_eq!(palette.entries, 2);
    assert_eq!(
        palette.columns,
        vec![
            PaletteColumn {
                precision: 8,
                signed: false
            },
            PaletteColumn {
                precision: 8,
                signed: true
            }
        ]
    );
    assert_eq!(palette.values, vec![5, -128, 7, 127]);
    assert_eq!(
        header.component_mappings,
        vec![
            ComponentMapping {
                component: 0,
                mapping_type: MappingType::Palette { column: 0 }
            },
            ComponentMapping {
                component: 1,
                mapping_type: MappingType::Palette { column: 1 }
            },
        ]
    );
    assert_eq!(
        header.channel_definition_records,
        vec![
            ChannelDefinitionRecord {
                channel: 0,
                definition: ChannelDefinition::new(
                    ChannelType::Color,
                    ChannelAssociation::Color(1)
                )
            },
            ChannelDefinitionRecord {
                channel: 1,
                definition: ChannelDefinition::new(
                    ChannelType::PremultipliedOpacity,
                    ChannelAssociation::WholeImage
                )
            },
        ]
    );
    let capture = Resolution {
        vertical_numerator: 1,
        vertical_denominator: 257,
        horizontal_numerator: 513,
        horizontal_denominator: u16::MAX,
        vertical_exponent: -128,
        horizontal_exponent: 127,
    };
    assert_eq!(header.capture_resolution, Some(capture));
    assert_eq!(
        header.display_resolution,
        Some(Resolution {
            vertical_exponent: 9,
            ..capture
        })
    );
}

#[test]
fn actual_raw_jp2_header_preserves_first_color_but_still_parses_every_later_color() {
    let mut payload = raw_jp2_header_image(7, 1);
    payload.extend_from_slice(&raw_jp2_header_color());
    payload.extend_from_slice(&box32(*b"colr", &[3, 255, 255, 7]));
    let header =
        super::headers::parse_jp2_header(&payload, &ResourceLimits::default(), u64::MAX).unwrap();
    assert_eq!(
        header.color.method(),
        ColorMethod::Enumerated { color_space: 16 }
    );
    assert_eq!(
        (header.color.precedence, header.color.approximation),
        (3, 4)
    );
    assert_eq!(header.color.icc_profile(), None);
    assert_eq!(header.nested_box_count, 3);
    payload.truncate(raw_jp2_header_image(7, 1).len() + raw_jp2_header_color().len());
    let offset = payload.len() as u64 + 100;
    payload.extend_from_slice(&box32(*b"colr", &[0, 0, 0]));
    assert_eq!(
        super::headers::parse_jp2_header(&payload, &ResourceLimits::default(), 100).err(),
        Some(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::InvalidColorSpecification
        })
    );
}

#[test]
fn actual_raw_jp2_header_keeps_initial_required_input_metadata_and_later_progress_priority() {
    let image = raw_jp2_header_image(7, 1);
    assert_eq!(
        super::headers::parse_jp2_header(&[], &ResourceLimits::default(), 100).err(),
        Some(DecodeError::MalformedInput {
            offset: 100,
            kind: MalformedKind::MissingRequiredStructure
        })
    );
    assert_eq!(
        super::headers::parse_jp2_header(
            &image,
            &ResourceLimits::default()
                .with_maximum_input_bytes(1)
                .unwrap(),
            100
        )
        .err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: 1,
            actual: 22
        })
    );
    assert_eq!(
        super::headers::parse_jp2_header(
            &image,
            &ResourceLimits::default()
                .with_maximum_metadata_bytes(1)
                .unwrap(),
            100
        )
        .err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::MetadataBytes,
            limit: 1,
            actual: 22
        })
    );
    let mut payload = image;
    payload.extend_from_slice(&raw_jp2_header_color());
    assert_eq!(
        super::headers::parse_jp2_header(
            &payload,
            &ResourceLimits::default()
                .with_maximum_work_units(1)
                .unwrap(),
            100
        )
        .err(),
        Some(DecodeError::MalformedInput {
            offset: 122,
            kind: MalformedKind::InvalidBoxLength
        })
    );
}

#[test]
fn actual_raw_jp2_header_keeps_duplicate_checks_and_resolution_parse_before_duplicate() {
    let mut prefix = raw_jp2_header_image(u8::MAX, 1);
    prefix.extend_from_slice(&raw_jp2_header_color());
    prefix.extend_from_slice(&box32(*b"bpcc", &[7]));
    let offset = prefix.len() as u64 + 100;
    let mut payload = prefix.clone();
    payload.extend_from_slice(&box32(*b"bpcc", &[]));
    assert_eq!(
        super::headers::parse_jp2_header(&payload, &ResourceLimits::default(), 100).err(),
        Some(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::InvalidBoxOrder
        })
    );
    prefix.extend_from_slice(&box32(
        *b"res ",
        &box32(*b"resc", &raw_resolution_payload()),
    ));
    let second_offset = prefix.len() as u64 + 100;
    let mut payload = prefix.clone();
    payload.extend_from_slice(&box32(*b"res ", &[]));
    assert_eq!(
        super::headers::parse_jp2_header(&payload, &ResourceLimits::default(), 100).err(),
        Some(DecodeError::MalformedInput {
            offset: second_offset + 8,
            kind: MalformedKind::MissingRequiredStructure
        })
    );
    let mut payload = prefix;
    payload.extend_from_slice(&box32(
        *b"res ",
        &box32(*b"resc", &raw_resolution_payload()),
    ));
    assert_eq!(
        super::headers::parse_jp2_header(&payload, &ResourceLimits::default(), 100).err(),
        Some(DecodeError::MalformedInput {
            offset: second_offset,
            kind: MalformedKind::InvalidBoxOrder
        })
    );
}

#[test]
fn actual_raw_jp2_header_keeps_final_bpcc_palette_mapping_and_color_requirements() {
    let mut variable = raw_jp2_header_image(u8::MAX, 1);
    variable.extend_from_slice(&raw_jp2_header_color());
    let mut unexpected_bpcc = raw_jp2_header_image(7, 1);
    unexpected_bpcc.extend_from_slice(&raw_jp2_header_color());
    unexpected_bpcc.extend_from_slice(&box32(*b"bpcc", &[7]));
    let mut palette_without_mapping = raw_jp2_header_image(7, 1);
    palette_without_mapping.extend_from_slice(&raw_jp2_header_color());
    palette_without_mapping.extend_from_slice(&box32(*b"pclr", &[0, 1, 1, 0, 1]));
    for payload in [
        variable,
        unexpected_bpcc,
        palette_without_mapping,
        raw_jp2_header_image(7, 1),
    ] {
        assert_eq!(
            super::headers::parse_jp2_header(&payload, &ResourceLimits::default(), 100).err(),
            Some(DecodeError::MalformedInput {
                offset: 100,
                kind: MalformedKind::MissingRequiredStructure
            })
        );
    }
}

#[test]
fn actual_raw_jp2_header_uses_actual_mapping_count_at_the_channel_definition_site() {
    let mut prefix = raw_jp2_header_image(7, 1);
    prefix.extend_from_slice(&raw_jp2_header_color());
    let mapping = box32(*b"cmap", &[0, 0, 0, 0, 0, 0, 0, 0]);
    let definition = box32(*b"cdef", &raw_channel_definition_payload(&[(1, 0, 1)]));
    let mut payload = prefix.clone();
    payload.extend_from_slice(&mapping);
    payload.extend_from_slice(&definition);
    let header =
        super::headers::parse_jp2_header(&payload, &ResourceLimits::default(), 100).unwrap();
    assert_eq!(header.image.components, 1);
    assert_eq!(header.component_mapping_entries, 2);
    assert_eq!(header.channel_definition_records[0].channel, 1);
    let offset = prefix.len() as u64 + 100;
    let mut payload = prefix;
    payload.extend_from_slice(&definition);
    payload.extend_from_slice(&mapping);
    assert_eq!(
        super::headers::parse_jp2_header(&payload, &ResourceLimits::default(), 100).err(),
        Some(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::InvalidBoxContents
        })
    );
}

fn raw_associated_defaults() -> Jp2Header {
    Jp2Header {
        image: ImageHeader {
            width: 3,
            height: 2,
            components: 3,
            bit_depth: ComponentBitDepth::Uniform {
                bits: 8,
                signed: false,
            },
            unknown_color_space: true,
            intellectual_property: true,
        },
        color: ColorSpecification {
            method: ColorMethod::AnyIcc { profile_bytes: 5 },
            precedence: 173,
            approximation: 219,
            icc_profile: Some(vec![1, 128, 255, 0, 17]),
        },
        nested_box_count: 99,
        palette_entries: 37,
        palette_columns: 19,
        component_mapping_entries: 21,
        channel_definitions: 22,
        palette: Some(Palette {
            entries: 2,
            columns: vec![
                PaletteColumn {
                    precision: 8,
                    signed: false,
                },
                PaletteColumn {
                    precision: 8,
                    signed: true,
                },
            ],
            values: vec![5, -128, 7, 127],
        }),
        component_mappings: vec![
            ComponentMapping {
                component: 0,
                mapping_type: MappingType::Palette { column: 0 },
            },
            ComponentMapping {
                component: 1,
                mapping_type: MappingType::Palette { column: 1 },
            },
        ],
        channel_definition_records: vec![ChannelDefinitionRecord {
            channel: 1,
            definition: ChannelDefinition::new(
                ChannelType::PremultipliedOpacity,
                ChannelAssociation::WholeImage,
            ),
        }],
        capture_resolution: Some(Resolution {
            vertical_numerator: 1,
            vertical_denominator: 257,
            horizontal_numerator: 513,
            horizontal_denominator: u16::MAX,
            vertical_exponent: -128,
            horizontal_exponent: 127,
        }),
        display_resolution: None,
    }
}

#[test]
fn actual_native_association_clone_preserves_arbitrary_header_payload_and_independent_metadata_owners()
 {
    let payload = [0, 128, 255, 17];
    let source = CodestreamHeaderAssociation {
        header: raw_metadata_box(&payload, *b"jpch", u64::MAX).header,
        payload: &payload,
        parsed: Some(raw_associated_defaults()),
    };
    let cloned = super::clone_support::codestream_association_clone(&source);
    assert_eq!(cloned, source);
    assert_eq!(cloned.payload.as_ptr(), source.payload.as_ptr());
    assert_eq!(cloned.payload.len(), source.payload.len());
    assert_eq!(source.clone(), source);
    let (cloned_header, source_header) = (
        cloned.parsed.as_ref().unwrap(),
        source.parsed.as_ref().unwrap(),
    );
    assert_ne!(
        cloned_header.color.icc_profile().unwrap().as_ptr(),
        source_header.color.icc_profile().unwrap().as_ptr()
    );
    assert_ne!(
        cloned_header.palette.as_ref().unwrap().columns.as_ptr(),
        source_header.palette.as_ref().unwrap().columns.as_ptr()
    );
    assert_ne!(
        cloned_header.palette.as_ref().unwrap().values.as_ptr(),
        source_header.palette.as_ref().unwrap().values.as_ptr()
    );
    assert_ne!(
        cloned_header.component_mappings.as_ptr(),
        source_header.component_mappings.as_ptr()
    );
    assert_ne!(
        cloned_header.channel_definition_records.as_ptr(),
        source_header.channel_definition_records.as_ptr()
    );
    drop(source);
    assert_eq!(cloned.payload, payload);
    assert_eq!(cloned_header, &raw_associated_defaults());
}

#[test]
fn actual_native_association_clone_keeps_absent_and_invalid_metadata_without_a_validity_premise() {
    let payload = [1];
    let mut source = CodestreamHeaderAssociation {
        header: raw_metadata_box(&payload, *b"xxxx", 123).header,
        payload: &payload,
        parsed: None,
    };
    assert_eq!(super::clone_support::optional_jp2_header_clone(&None), None);
    assert_eq!(source.clone(), source);
    let mut header = raw_associated_defaults();
    header.image.width = 0;
    header.image.components = 0;
    header.color.icc_profile = Some(Vec::new());
    header.palette = Some(Palette {
        entries: 0,
        columns: vec![PaletteColumn {
            precision: 0,
            signed: true,
        }],
        values: vec![i64::MIN, i64::MAX],
    });
    source.parsed = Some(header);
    let cloned = source.clone();
    assert_eq!(cloned, source);
    assert_eq!(cloned.payload.as_ptr(), payload.as_ptr());
}

#[test]
fn actual_native_metadata_clone_preserves_every_arbitrary_field_and_deep_owner() {
    let source = raw_associated_defaults();
    let cloned = source.clone();
    assert_eq!(cloned, source);
    assert_ne!(
        cloned.color.icc_profile().unwrap().as_ptr(),
        source.color.icc_profile().unwrap().as_ptr()
    );
    let (cloned_palette, source_palette) = (
        cloned.palette.as_ref().unwrap(),
        source.palette.as_ref().unwrap(),
    );
    assert_ne!(
        cloned_palette.columns.as_ptr(),
        source_palette.columns.as_ptr()
    );
    assert_ne!(
        cloned_palette.values.as_ptr(),
        source_palette.values.as_ptr()
    );
    assert_ne!(
        cloned.component_mappings.as_ptr(),
        source.component_mappings.as_ptr()
    );
    assert_ne!(
        cloned.channel_definition_records.as_ptr(),
        source.channel_definition_records.as_ptr()
    );
    assert_eq!(super::clone_support::jp2_header_clone(&source), source);
    assert_eq!(super::clone_support::optional_palette_clone(&None), None);
}

#[test]
fn actual_native_metadata_clone_keeps_invalid_palette_metadata_without_a_validity_premise() {
    let mut source = raw_associated_defaults();
    source.palette = Some(Palette {
        entries: 0,
        columns: vec![PaletteColumn {
            precision: 0,
            signed: true,
        }],
        values: vec![i64::MIN, i64::MAX],
    });
    source.image.components = 0;
    source.image.bit_depth = ComponentBitDepth::Variable;
    let cloned = source.clone();
    assert_eq!(cloned, source);
    assert_eq!(
        super::clone_support::palette_clone(source.palette.as_ref().unwrap()),
        source.palette.unwrap()
    );
}

#[test]
fn actual_raw_associated_header_complete_first_parse_preempts_defaults_and_fallback_errors() {
    let defaults = raw_associated_defaults();
    let mut payload = raw_jp2_header_image(7, 1);
    payload.extend_from_slice(&raw_jp2_header_color());
    let header = super::headers::parse_codestream_header(
        &payload,
        Some(&defaults),
        &ResourceLimits::default(),
        100,
    )
    .unwrap();
    assert_eq!(
        header.color.method(),
        ColorMethod::Enumerated { color_space: 16 }
    );
    assert_eq!(header.palette, None);
    assert_eq!(header.nested_box_count, 2);
    assert_eq!(header.image.components, 1);
    assert!(
        super::headers::parse_codestream_header(&payload, None, &ResourceLimits::default(), 100)
            .is_ok()
    );
    assert_eq!(
        super::headers::parse_codestream_header(&[0], None, &ResourceLimits::default(), 100).err(),
        Some(DecodeError::MalformedInput {
            offset: 100,
            kind: MalformedKind::MissingRequiredStructure
        })
    );
}

#[test]
fn actual_raw_associated_header_inherits_full_defaults_counts_and_independent_owners() {
    let mut defaults = raw_associated_defaults();
    defaults.image.bit_depth = ComponentBitDepth::Variable;
    let mut expected = defaults.clone();
    expected.nested_box_count = 0;
    let header = super::headers::parse_codestream_header(
        &[],
        Some(&defaults),
        &ResourceLimits::default(),
        u64::MAX,
    )
    .unwrap();
    assert_eq!(header, expected);
    assert_eq!(
        (
            header.palette_entries,
            header.palette_columns,
            header.component_mapping_entries,
            header.channel_definitions
        ),
        (37, 19, 21, 22)
    );
    assert_ne!(
        header.color.icc_profile().unwrap().as_ptr(),
        defaults.color.icc_profile().unwrap().as_ptr()
    );
    assert_ne!(
        header.palette.as_ref().unwrap().values.as_ptr(),
        defaults.palette.as_ref().unwrap().values.as_ptr()
    );
}

#[test]
fn actual_raw_associated_header_image_override_clears_only_original_palette_record_owners() {
    let defaults = raw_associated_defaults();
    let payload = box32(*b"ihdr", &raw_image_header_payload(5, 7, 1, 7, [0, 1]));
    let header = super::headers::parse_codestream_header(
        &payload,
        Some(&defaults),
        &ResourceLimits::default(),
        100,
    )
    .unwrap();
    assert_eq!(header.image.width, 5);
    assert_eq!(header.image.height, 7);
    assert_eq!(header.image.components, 1);
    assert_eq!(header.palette, None);
    assert!(header.component_mappings.is_empty());
    assert!(header.channel_definition_records.is_empty());
    assert_eq!(
        (
            header.palette_entries,
            header.palette_columns,
            header.component_mapping_entries,
            header.channel_definitions
        ),
        (0, 0, 0, 0)
    );
    assert_eq!(header.color, defaults.color);
    assert_eq!(header.capture_resolution, defaults.capture_resolution);
    assert_eq!(header.nested_box_count, 1);
}

#[test]
fn actual_raw_associated_header_preserves_bpcc_before_image_and_override_only_final_requirement() {
    let defaults = raw_associated_defaults();
    let image = raw_jp2_header_image(u8::MAX, 3);
    assert_eq!(
        super::headers::parse_codestream_header(
            &image,
            Some(&defaults),
            &ResourceLimits::default(),
            100
        )
        .err(),
        Some(DecodeError::MalformedInput {
            offset: 100,
            kind: MalformedKind::MissingRequiredStructure
        })
    );
    let mut payload = box32(*b"bpcc", &[7, 0x87, 37]);
    payload.extend_from_slice(&image);
    let header = super::headers::parse_codestream_header(
        &payload,
        Some(&defaults),
        &ResourceLimits::default(),
        100,
    )
    .unwrap();
    assert_eq!(header.image.bit_depth, ComponentBitDepth::Variable);
    assert_eq!(header.nested_box_count, 2);
    assert_eq!(header.palette, None);
}

#[test]
fn actual_raw_associated_header_uses_real_first_color_palette_mapping_definition_resolution_overrides()
 {
    let defaults = raw_associated_defaults();
    let mut payload = box32(*b"colr", &[3, 7, 9, 11, 12]);
    payload.extend_from_slice(&raw_jp2_header_color());
    payload.extend_from_slice(&box32(*b"pclr", &[0, 1, 1, 0, 1]));
    payload.extend_from_slice(&box32(*b"cmap", &[0, 0, 1, 0]));
    payload.extend_from_slice(&box32(
        *b"cdef",
        &raw_channel_definition_payload(&[(0, 1, 0)]),
    ));
    payload.extend_from_slice(&box32(
        *b"res ",
        &box32(*b"resc", &raw_resolution_payload()),
    ));
    let header = super::headers::parse_codestream_header(
        &payload,
        Some(&defaults),
        &ResourceLimits::default(),
        100,
    )
    .unwrap();
    assert_eq!(
        header.color.method(),
        ColorMethod::AnyIcc { profile_bytes: 2 }
    );
    assert_eq!(
        (header.color.precedence, header.color.approximation),
        (7, 9)
    );
    assert_eq!(header.color.icc_profile(), Some(&[11, 12][..]));
    assert_eq!(
        (
            header.palette_entries,
            header.palette_columns,
            header.component_mapping_entries,
            header.channel_definitions
        ),
        (1, 1, 1, 1)
    );
    assert_eq!(header.palette.unwrap().values, vec![1]);
    assert_eq!(
        header.component_mappings,
        vec![ComponentMapping {
            component: 0,
            mapping_type: MappingType::Palette { column: 0 }
        }]
    );
    assert_eq!(
        header.channel_definition_records[0].definition,
        ChannelDefinition::new(ChannelType::Opacity, ChannelAssociation::WholeImage)
    );
    assert!(header.capture_resolution.is_some());
    assert_eq!(header.display_resolution, None);
    assert_eq!(header.nested_box_count, 6);
}

#[test]
fn actual_raw_associated_header_keeps_override_order_before_payload_validation() {
    let defaults = raw_associated_defaults();
    let mut prefix = box32(*b"cmap", &[0, 0, 0, 0]);
    let offset = 100 + prefix.len() as u64;
    prefix.extend_from_slice(&box32(*b"pclr", &[]));
    assert_eq!(
        super::headers::parse_codestream_header(
            &prefix,
            Some(&defaults),
            &ResourceLimits::default(),
            100
        )
        .err(),
        Some(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::InvalidBoxOrder
        })
    );
    let mut prefix = box32(*b"res ", &box32(*b"resc", &raw_resolution_payload()));
    let offset = 100 + prefix.len() as u64;
    prefix.extend_from_slice(&box32(*b"res ", &[]));
    assert_eq!(
        super::headers::parse_codestream_header(
            &prefix,
            Some(&defaults),
            &ResourceLimits::default(),
            100
        )
        .err(),
        Some(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::InvalidBoxOrder
        })
    );
}

#[test]
fn actual_raw_associated_header_keeps_unknown_count_and_missing_default_before_second_input_limit()
{
    let defaults = raw_associated_defaults();
    let payload = box32(*b"xml ", &[7]);
    let header = super::headers::parse_codestream_header(
        &payload,
        Some(&defaults),
        &ResourceLimits::default(),
        100,
    )
    .unwrap();
    assert_eq!(header.nested_box_count, 1);
    assert_eq!(header.palette_entries, 37);
    let limits = ResourceLimits::default()
        .with_maximum_input_bytes(1)
        .unwrap();
    assert_eq!(
        super::headers::parse_codestream_header(&payload, None, &limits, 100).err(),
        Some(DecodeError::MalformedInput {
            offset: 100,
            kind: MalformedKind::MissingRequiredStructure
        })
    );
    assert_eq!(
        super::headers::parse_codestream_header(&payload, Some(&defaults), &limits, 100).err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: 1,
            actual: 9
        })
    );
}

fn raw_metadata_box<'a>(payload: &'a [u8], kind: [u8; 4], offset: u64) -> BoxRef<'a> {
    BoxRef {
        header: BoxHeader {
            box_type: BoxType::new(kind),
            offset,
            header_length: 8,
            total_length: payload.len() as u64 + 8,
        },
        payload,
    }
}

#[test]
fn actual_raw_metadata_tree_keeps_non_association_and_empty_association_seed_behavior() {
    let limits = ResourceLimits::default()
        .with_maximum_input_bytes(1)
        .unwrap();
    for kind in [*b"xml ", *b"free", *b"jp2c"] {
        assert_eq!(
            super::metadata::inspect_metadata_box(
                raw_metadata_box(&[0, 1, 2], kind, 99),
                &limits,
                1,
                0
            ),
            Ok((1, 1))
        );
    }
    for (depth, remaining) in [(0, 0), (1, 1), (32, 0)] {
        assert_eq!(
            super::metadata::inspect_metadata_box(
                raw_metadata_box(&[], *b"asoc", 99),
                &limits,
                depth,
                remaining
            ),
            Ok((1, depth))
        );
    }
}

#[test]
fn actual_raw_metadata_tree_derives_complete_nested_count_and_maximum_depth_from_bytes() {
    let mut children = box32(*b"xml ", &[7]);
    children.extend_from_slice(&box32(*b"asoc", &[]));
    let mut payload = box32(*b"xml ", &[]);
    payload.extend_from_slice(&box32(*b"asoc", &children));
    assert_eq!(
        super::metadata::inspect_metadata_box(
            raw_metadata_box(&payload, *b"asoc", 99),
            &ResourceLimits::default(),
            1,
            2
        ),
        Ok((5, 3))
    );
    assert_eq!(
        super::metadata::inspect_metadata_box(
            raw_metadata_box(&payload, *b"asoc", 99),
            &ResourceLimits::default(),
            1,
            1
        ),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    let mut payload = Vec::new();
    for _ in 0..257 {
        payload.extend_from_slice(&box32(*b"xml ", &[]));
    }
    assert_eq!(
        super::metadata::inspect_metadata_box(
            raw_metadata_box(&payload, *b"asoc", 99),
            &ResourceLimits::default(),
            1,
            1
        ),
        Ok((258, 2))
    );
}

#[test]
fn actual_raw_metadata_tree_keeps_exact_depth_before_kind_and_remaining_before_child_depth_priority()
 {
    let limits = ResourceLimits::default();
    for kind in [*b"asoc", *b"xml "] {
        assert_eq!(
            super::metadata::inspect_metadata_box(raw_metadata_box(&[0], kind, 99), &limits, 33, 0),
            Err(DecodeError::LimitExceeded {
                resource: Resource::BoxDepth,
                limit: 32,
                actual: 33
            })
        );
    }
    let payload = box32(*b"xml ", &[]);
    assert_eq!(
        super::metadata::inspect_metadata_box(
            raw_metadata_box(&payload, *b"asoc", 99),
            &limits,
            32,
            1
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::BoxDepth,
            limit: 32,
            actual: 33
        })
    );
    assert_eq!(
        super::metadata::inspect_metadata_box(
            raw_metadata_box(&payload, *b"asoc", 99),
            &limits,
            32,
            0
        ),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
}

#[test]
fn actual_raw_metadata_tree_keeps_reader_relative_errors_before_remaining_depth_errors() {
    let limits = ResourceLimits::default();
    assert_eq!(
        super::metadata::inspect_metadata_box(raw_metadata_box(&[0], *b"asoc", 99), &limits, 1, 0),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::Truncated
        })
    );
    let mut payload = box32(*b"xml ", &[]);
    payload.extend_from_slice(&[0, 0]);
    assert_eq!(
        super::metadata::inspect_metadata_box(
            raw_metadata_box(&payload, *b"asoc", 99),
            &limits,
            1,
            1
        ),
        Err(DecodeError::MalformedInput {
            offset: 8,
            kind: MalformedKind::Truncated
        })
    );
}

#[test]
fn actual_raw_metadata_tree_keeps_nested_input_metadata_and_local_aggregate_work_limits() {
    let payload = box32(*b"xml ", &[]);
    assert_eq!(
        super::metadata::inspect_metadata_box(
            raw_metadata_box(&payload, *b"asoc", 99),
            &ResourceLimits::default()
                .with_maximum_input_bytes(1)
                .unwrap(),
            1,
            0
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: 1,
            actual: 8
        })
    );
    assert_eq!(
        super::metadata::inspect_metadata_box(
            raw_metadata_box(&payload, *b"asoc", 99),
            &ResourceLimits::default()
                .with_maximum_metadata_bytes(1)
                .unwrap(),
            1,
            0
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::MetadataBytes,
            limit: 1,
            actual: 8
        })
    );
    assert_eq!(
        super::metadata::inspect_metadata_box(
            raw_metadata_box(&payload, *b"asoc", 99),
            &ResourceLimits::default()
                .with_maximum_work_units(1)
                .unwrap(),
            1,
            1
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2
        })
    );
    let nested = box32(*b"asoc", &payload);
    assert_eq!(
        super::metadata::inspect_metadata_box(
            raw_metadata_box(&nested, *b"asoc", 99),
            &ResourceLimits::default()
                .with_maximum_work_units(1)
                .unwrap(),
            1,
            2
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2
        })
    );
}

#[test]
fn actual_raw_layer_registration_retains_grids_all_fields_order_and_duplicate_indices() {
    let payload = [
        1, 0, 1, 1, 255, 255, 1, 255, 255, 254, 255, 255, 2, 1, 0, 255,
    ];
    let (horizontal, vertical, values) = super::composition::parse_codestream_registration(
        raw_metadata_box(&payload, *b"creg", 19),
        u64::MAX,
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!((horizontal, vertical), (256, 257));
    assert_eq!(
        values,
        vec![
            CodestreamRegistration {
                codestream_index: u16::MAX,
                horizontal_subsampling: 1,
                vertical_subsampling: 255,
                horizontal_offset: 255,
                vertical_offset: 254
            },
            CodestreamRegistration {
                codestream_index: u16::MAX,
                horizontal_subsampling: 2,
                vertical_subsampling: 1,
                horizontal_offset: 0,
                vertical_offset: 255
            },
        ]
    );
}

#[test]
fn actual_raw_layer_registration_keeps_length_grid_count_and_record_error_priority() {
    let limits = ResourceLimits::default()
        .with_maximum_codestreams(1)
        .unwrap();
    for payload in [&[][..], &[0; 9][..], &[0; 11][..]] {
        assert_eq!(
            super::composition::parse_codestream_registration(
                raw_metadata_box(payload, *b"creg", 19),
                100,
                &limits
            )
            .err(),
            Some(DecodeError::MalformedInput {
                offset: 119,
                kind: MalformedKind::InvalidBoxLength
            })
        );
    }
    let mut payload = vec![0; 16];
    assert_eq!(
        super::composition::parse_codestream_registration(
            raw_metadata_box(&payload, *b"creg", 19),
            100,
            &limits
        )
        .err(),
        Some(DecodeError::MalformedInput {
            offset: 119,
            kind: MalformedKind::InvalidBoxContents
        })
    );
    payload[1] = 1;
    payload[3] = 1;
    assert_eq!(
        super::composition::parse_codestream_registration(
            raw_metadata_box(&payload, *b"creg", 19),
            u64::MAX,
            &limits
        )
        .err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::Codestreams,
            limit: 1,
            actual: 2
        })
    );
    payload.truncate(10);
    assert_eq!(
        super::composition::parse_codestream_registration(
            raw_metadata_box(&payload, *b"creg", 19),
            u64::MAX,
            &limits
        )
        .err(),
        Some(DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
}

#[test]
fn actual_raw_layer_registration_covers_every_subsampling_byte_and_exact_offset_boundary() {
    for factor in 0..=u8::MAX {
        let payload = [0, 2, 0, 2, 0, 7, factor, 1, 1, 1];
        let result = super::composition::parse_codestream_registration(
            raw_metadata_box(&payload, *b"creg", 19),
            100,
            &ResourceLimits::default(),
        );
        if factor == 0 {
            assert_eq!(
                result.err(),
                Some(DecodeError::MalformedInput {
                    offset: 119,
                    kind: MalformedKind::InvalidBoxContents
                })
            );
        } else {
            assert_eq!(result.unwrap().2[0].horizontal_subsampling, factor);
        }
    }
    for position in [8, 9] {
        let mut payload = [0, 2, 0, 2, 0, 7, 1, 1, 1, 1];
        payload[position] = 2;
        assert_eq!(
            super::composition::parse_codestream_registration(
                raw_metadata_box(&payload, *b"creg", 19),
                100,
                &ResourceLimits::default()
            )
            .err(),
            Some(DecodeError::MalformedInput {
                offset: 119,
                kind: MalformedKind::InvalidBoxContents
            })
        );
    }
}

#[test]
fn actual_raw_layer_color_group_retains_order_all_metadata_and_every_owned_icc_byte() {
    let mut payload = raw_jp2_header_color();
    payload.extend_from_slice(&box32(*b"colr", &[2, 173, 219, 0, 255, 128, 17]));
    payload.extend_from_slice(&box32(*b"colr", &[3, 5, 7, 11]));
    let colors = super::composition::parse_color_group(
        raw_metadata_box(&payload, *b"cgrp", 19),
        &ResourceLimits::default(),
        u64::MAX,
    )
    .unwrap();
    payload.fill(0);
    assert_eq!(colors.len(), 3);
    assert_eq!(
        colors[0].method(),
        ColorMethod::Enumerated { color_space: 16 }
    );
    assert_eq!((colors[0].precedence, colors[0].approximation), (3, 4));
    assert_eq!(
        colors[1].method(),
        ColorMethod::RestrictedIcc { profile_bytes: 4 }
    );
    assert_eq!((colors[1].precedence, colors[1].approximation), (173, 219));
    assert_eq!(colors[1].icc_profile(), Some(&[0, 255, 128, 17][..]));
    assert_eq!(colors[2].method(), ColorMethod::AnyIcc { profile_bytes: 1 });
    assert_eq!(colors[2].icc_profile(), Some(&[11][..]));
}

#[test]
fn actual_raw_layer_color_group_keeps_empty_kind_progress_and_parse_before_component_limit_priority()
 {
    let limits = ResourceLimits::default();
    assert_eq!(
        super::composition::parse_color_group(raw_metadata_box(&[], *b"cgrp", 19), &limits, 100)
            .err(),
        Some(DecodeError::MalformedInput {
            offset: 100,
            kind: MalformedKind::MissingRequiredStructure
        })
    );
    assert_eq!(
        super::composition::parse_color_group(raw_metadata_box(&[0], *b"cgrp", 19), &limits, 100)
            .err(),
        Some(DecodeError::MalformedInput {
            offset: 100,
            kind: MalformedKind::InvalidBoxLength
        })
    );
    assert_eq!(
        super::composition::parse_color_group(
            raw_metadata_box(&box32(*b"free", &[]), *b"cgrp", 19),
            &limits,
            100
        )
        .err(),
        Some(DecodeError::MalformedInput {
            offset: 100,
            kind: MalformedKind::InvalidBoxContents
        })
    );
    let limits = limits.with_geometry_limits_for_test(0, 3, 2, 6, 1);
    assert_eq!(
        super::composition::parse_color_group(
            raw_metadata_box(&box32(*b"colr", &[0, 0, 0]), *b"cgrp", 19),
            &limits,
            100
        )
        .err(),
        Some(DecodeError::MalformedInput {
            offset: 100,
            kind: MalformedKind::InvalidColorSpecification
        })
    );
    assert_eq!(
        super::composition::parse_color_group(
            raw_metadata_box(&raw_jp2_header_color(), *b"cgrp", 19),
            &limits,
            100
        )
        .err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::Components,
            limit: 0,
            actual: 1
        })
    );
}

#[test]
fn actual_raw_layer_opacity_keeps_all_methods_lengths_and_eager_offset_error_priority() {
    for method in 0..=u8::MAX {
        for length in 0..=4 {
            let mut payload = vec![1; length];
            if let Some(first) = payload.first_mut() {
                *first = method;
            }
            let result = super::composition::parse_layer_opacity(
                raw_metadata_box(&payload, *b"opct", 19),
                100,
            );
            if length == 1 && method <= 1 {
                assert_eq!(
                    result.unwrap(),
                    if method == 0 {
                        LayerOpacity::Straight
                    } else {
                        LayerOpacity::Premultiplied
                    }
                );
            } else if method == 2 && length >= 3 {
                assert_eq!(
                    result.unwrap(),
                    LayerOpacity::ChromaKey {
                        channels: 1,
                        values: vec![1; length - 2]
                    }
                );
            } else {
                let kind = if length == 0 || method <= 2 {
                    MalformedKind::InvalidBoxLength
                } else {
                    MalformedKind::InvalidBoxContents
                };
                assert_eq!(
                    result.err(),
                    Some(DecodeError::MalformedInput { offset: 119, kind })
                );
            }
            assert_eq!(
                super::composition::parse_layer_opacity(
                    raw_metadata_box(&payload, *b"opct", 19),
                    u64::MAX
                )
                .err(),
                Some(DecodeError::MalformedInput {
                    offset: u64::MAX,
                    kind: MalformedKind::ArithmeticOverflow
                })
            );
        }
    }
}

#[test]
fn actual_raw_layer_opacity_retains_arbitrary_channel_count_and_independent_key_bytes() {
    let mut payload = vec![2, 255, 0, 255, 128, 17];
    let opacity =
        super::composition::parse_layer_opacity(raw_metadata_box(&payload, *b"opct", 19), 100)
            .unwrap();
    payload.fill(0);
    assert_eq!(
        opacity,
        LayerOpacity::ChromaKey {
            channels: 255,
            values: vec![0, 255, 128, 17]
        }
    );
    assert_eq!(
        super::composition::parse_layer_opacity(raw_metadata_box(&[2, 0, 7], *b"opct", 19), 100)
            .err(),
        Some(DecodeError::MalformedInput {
            offset: 119,
            kind: MalformedKind::InvalidBoxContents
        })
    );
}

#[test]
fn actual_raw_layer_header_preserves_empty_defaults_header_and_original_payload_reference() {
    let limits = ResourceLimits::default();
    let payload = [];
    let input = raw_metadata_box(&payload, *b"jplh", 99);
    let layer = parse_compositing_layer(input, &limits).unwrap();
    assert_eq!(layer.header, input.header);
    assert!(std::ptr::eq(layer.payload, input.payload));
    assert_eq!(
        (layer.horizontal_grid_size, layer.vertical_grid_size),
        (1, 1)
    );
    assert!(layer.registrations.is_empty());
    assert!(layer.color_group.is_empty());
    assert!(layer.channel_definition_records.is_empty());
    assert_eq!(layer.opacity, None);
    assert_eq!(layer.nested_metadata_boxes, 0);
    assert_eq!(
        parse_compositing_layer(raw_metadata_box(&[], *b"jplh", u64::MAX), &limits).err(),
        Some(DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
}

#[test]
fn actual_raw_layer_header_derives_all_raw_registration_color_opacity_and_nested_metadata_fields() {
    let registration = [1, 0, 1, 1, 0, 1, 2, 3, 255, 254, 0, 0, 1, 1, 0, 255];
    let mut payload = box32(*b"creg", &registration);
    let mut colors = raw_jp2_header_color();
    colors.extend_from_slice(&box32(*b"colr", &[3, 7, 9, 0, 255, 128]));
    payload.extend_from_slice(&box32(*b"cgrp", &colors));
    payload.extend_from_slice(&box32(*b"opct", &[2, 3, 1, 255, 128, 0]));
    payload.extend_from_slice(&box32(*b"asoc", &box32(*b"xml ", &[7])));
    payload.extend_from_slice(&box32(*b"free", &[]));
    let input = raw_metadata_box(&payload, *b"jplh", 99);
    let layer = parse_compositing_layer(input, &ResourceLimits::default()).unwrap();
    assert_eq!(layer.header, input.header);
    assert!(std::ptr::eq(layer.payload, payload.as_slice()));
    assert_eq!(
        (layer.horizontal_grid_size, layer.vertical_grid_size),
        (256, 257)
    );
    assert_eq!(layer.registrations.len(), 2);
    assert_eq!(
        layer.registrations[0],
        CodestreamRegistration {
            codestream_index: 1,
            horizontal_subsampling: 2,
            vertical_subsampling: 3,
            horizontal_offset: 255,
            vertical_offset: 254,
        }
    );
    assert_eq!(layer.registrations[1].codestream_index, 0);
    assert_eq!(layer.color_group.len(), 2);
    assert_eq!(layer.color_group[1].icc_profile(), Some(&[0, 255, 128][..]));
    assert_eq!(
        (
            layer.color_group[1].precedence,
            layer.color_group[1].approximation
        ),
        (7, 9)
    );
    assert_eq!(
        layer.opacity,
        Some(LayerOpacity::ChromaKey {
            channels: 3,
            values: vec![1, 255, 128, 0]
        })
    );
    assert!(layer.channel_definition_records.is_empty());
    assert_eq!(layer.nested_metadata_boxes, 3);
}

#[test]
fn actual_raw_layer_header_keeps_duplicate_exclusion_and_metadata_reader_error_priority() {
    let registration = box32(*b"creg", &[0, 1, 0, 1, 0, 0, 1, 1, 0, 0]);
    let group = box32(*b"cgrp", &raw_jp2_header_color());
    let definition = box32(*b"cdef", &raw_channel_definition_payload(&[(0, 1, 0)]));
    for (first, second) in [
        (registration, box32(*b"creg", &[])),
        (group, box32(*b"cgrp", &[])),
        (box32(*b"opct", &[0]), box32(*b"cdef", &[])),
        (definition, box32(*b"opct", &[])),
    ] {
        let offset = 107 + first.len() as u64;
        let mut payload = first;
        payload.extend_from_slice(&second);
        assert_eq!(
            parse_compositing_layer(
                raw_metadata_box(&payload, *b"jplh", 99),
                &ResourceLimits::default()
            )
            .err(),
            Some(DecodeError::MalformedInput {
                offset,
                kind: MalformedKind::InvalidBoxOrder
            })
        );
    }
    assert_eq!(
        parse_compositing_layer(
            raw_metadata_box(&[0], *b"jplh", 99),
            &ResourceLimits::default()
        )
        .err(),
        Some(DecodeError::MalformedInput {
            offset: 107,
            kind: MalformedKind::InvalidBoxLength
        })
    );
    let definition = box32(
        *b"cdef",
        &raw_channel_definition_payload(&[(u16::MAX - 1, u16::MAX, u16::MAX)]),
    );
    let layer = parse_compositing_layer(
        raw_metadata_box(&definition, *b"jplh", 99),
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(layer.channel_definition_records[0].channel, u16::MAX - 1);
    assert_eq!(layer.opacity, None);
}

fn raw_instruction_payload(flags: u16, repeat: u16, tick: u32, words: &[u32]) -> Vec<u8> {
    let mut payload = flags.to_be_bytes().to_vec();
    payload.extend_from_slice(&repeat.to_be_bytes());
    payload.extend_from_slice(&tick.to_be_bytes());
    for word in words {
        payload.extend_from_slice(&word.to_be_bytes());
    }
    payload
}

#[test]
fn actual_raw_composition_word_retains_endian_cursor_and_complete_error_frames() {
    let input = [9, 0x80, 0x01, 0xff, 0x7f, 3];
    let mut position = 1;
    assert_eq!(
        super::composition::read_u32_at(&input, &mut position, 197),
        Ok(0x8001_ff7f)
    );
    assert_eq!(position, 5);
    for initial in [3, input.len(), input.len() + 1, usize::MAX] {
        let mut position = initial;
        assert_eq!(
            super::composition::read_u32_at(&input, &mut position, 197),
            Err(DecodeError::MalformedInput {
                offset: 197,
                kind: if initial == usize::MAX {
                    MalformedKind::ArithmeticOverflow
                } else {
                    MalformedKind::InvalidBoxLength
                },
            })
        );
        assert_eq!(position, initial);
    }
}

#[test]
fn actual_raw_composition_dimensions_keep_geometry_width_height_pixel_priority() {
    let limits = ResourceLimits::default().with_geometry_limits_for_test(1, 2, 2, 3, 1);
    for (width, height, error) in [
        (
            0,
            9,
            DecodeError::MalformedInput {
                offset: 197,
                kind: MalformedKind::InvalidImageGeometry,
            },
        ),
        (
            3,
            4,
            DecodeError::LimitExceeded {
                resource: Resource::Width,
                limit: 2,
                actual: 3,
            },
        ),
        (
            2,
            4,
            DecodeError::LimitExceeded {
                resource: Resource::Height,
                limit: 2,
                actual: 4,
            },
        ),
        (
            2,
            2,
            DecodeError::LimitExceeded {
                resource: Resource::Pixels,
                limit: 3,
                actual: 4,
            },
        ),
    ] {
        assert_eq!(
            super::composition::validate_dimensions(width, height, &limits, 197),
            Err(error)
        );
    }
    let limits = limits.with_geometry_limits_for_test(1, u32::MAX, u32::MAX, u64::MAX, 1);
    assert_eq!(
        super::composition::validate_dimensions(u32::MAX, u32::MAX, &limits, u64::MAX),
        Ok(())
    );
}

#[test]
fn actual_raw_composition_instruction_retains_every_optional_field_and_zero_life_defaults() {
    for mask in 0..16 {
        let flags = (mask & 7) | ((mask & 8) << 2);
        let mut words = Vec::new();
        if flags & 1 != 0 {
            words.extend_from_slice(&[3, 5]);
        }
        if flags & 2 != 0 {
            words.extend_from_slice(&[7, 11]);
        }
        if flags & 4 != 0 {
            words.extend_from_slice(&[0x8000_0002, 13]);
        }
        if flags & 32 != 0 {
            words.extend_from_slice(&[17, 19, 23, 29]);
        }
        let payload = raw_instruction_payload(flags, u16::MAX, 31, &words);
        let set = super::composition::parse_instruction_set(
            raw_metadata_box(&payload, *b"inst", 19),
            (101, 103, 255),
            100,
            &ResourceLimits::default(),
        )
        .unwrap();
        assert_eq!((set.flags, set.repeat, set.tick), (flags, u16::MAX, 31));
        if flags == 0 {
            assert!(set.instructions.is_empty());
        } else {
            assert_eq!(
                set.instructions,
                vec![CompositionInstruction {
                    target_x: if flags & 1 != 0 { 3 } else { 0 },
                    target_y: if flags & 1 != 0 { 5 } else { 0 },
                    target_width: if flags & 2 != 0 { 7 } else { 101 },
                    target_height: if flags & 2 != 0 { 11 } else { 103 },
                    life: if flags & 4 != 0 { 62 } else { 0 },
                    persistent: true,
                    next_reuse: if flags & 4 != 0 { 13 } else { 0 },
                    source_x: if flags & 32 != 0 { 17 } else { 0 },
                    source_y: if flags & 32 != 0 { 19 } else { 0 },
                    source_width: if flags & 32 != 0 { 23 } else { 0 },
                    source_height: if flags & 32 != 0 { 29 } else { 0 },
                }]
            );
        }
    }
}

#[test]
fn actual_raw_composition_instruction_covers_every_flag_and_eager_offset_admission() {
    for flags in 0..=u16::MAX {
        let payload = raw_instruction_payload(flags, 7, u32::MAX, &[]);
        let result = super::composition::parse_instruction_set(
            raw_metadata_box(&payload, *b"inst", 19),
            (0, 0, 0),
            100,
            &ResourceLimits::default(),
        );
        if flags & !0x0027 == 0 {
            assert!(result.unwrap().instructions.is_empty());
        } else {
            assert_eq!(
                result.err(),
                Some(DecodeError::MalformedInput {
                    offset: 119,
                    kind: MalformedKind::InvalidBoxContents
                })
            );
        }
    }
    assert_eq!(
        super::composition::parse_instruction_set(
            raw_metadata_box(&[], *b"inst", 19),
            (0, 0, 0),
            u64::MAX,
            &ResourceLimits::default()
        )
        .err(),
        Some(DecodeError::MalformedInput {
            offset: u64::MAX,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
}

#[test]
fn actual_raw_composition_instruction_keeps_count_geometry_and_life_overflow_error_priority() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(1)
        .unwrap();
    let payload = raw_instruction_payload(2, 0, u32::MAX, &[0, 0, 0, 0]);
    assert_eq!(
        super::composition::parse_instruction_set(
            raw_metadata_box(&payload, *b"inst", 19),
            (1, 1, 0),
            100,
            &limits
        )
        .err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2
        })
    );
    for (words, expected) in [
        (
            vec![0, 1, 0x7fff_ffff, 0],
            MalformedKind::InvalidImageGeometry,
        ),
        (
            vec![1, 1, 0x7fff_ffff, 0],
            MalformedKind::ArithmeticOverflow,
        ),
    ] {
        let payload = raw_instruction_payload(6, 0, 3, &words);
        assert_eq!(
            super::composition::parse_instruction_set(
                raw_metadata_box(&payload, *b"inst", 19),
                (1, 1, 0),
                100,
                &ResourceLimits::default()
            )
            .err(),
            Some(DecodeError::MalformedInput {
                offset: 119,
                kind: expected
            })
        );
    }
    let payload = raw_instruction_payload(4, 0, 3, &[2, 17]);
    let set = super::composition::parse_instruction_set(
        raw_metadata_box(&payload, *b"inst", 19),
        (1, 1, 0),
        100,
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(
        (
            set.instructions[0].life,
            set.instructions[0].persistent,
            set.instructions[0].next_reuse
        ),
        (6, false, 17)
    );
}

fn raw_composition_options(encoded_loop: u8) -> Vec<u8> {
    let mut payload = 2_u32.to_be_bytes().to_vec();
    payload.extend_from_slice(&3_u32.to_be_bytes());
    payload.push(encoded_loop);
    box32(*b"copt", &payload)
}

#[test]
fn actual_raw_composition_retains_every_loop_byte_owned_instruction_set_and_unknown_flag() {
    for encoded_loop in 0..=u8::MAX {
        let mut payload = box32(*b"free", &[7]);
        payload.extend_from_slice(&raw_composition_options(encoded_loop));
        payload.extend_from_slice(&box32(
            *b"inst",
            &raw_instruction_payload(1, 17, 19, &[23, 29]),
        ));
        payload.extend_from_slice(&box32(*b"inst", &raw_instruction_payload(0, 31, 37, &[])));
        let composition = parse_composition(
            raw_metadata_box(&payload, *b"comp", 99),
            &ResourceLimits::default(),
        )
        .unwrap();
        payload.fill(0);
        assert_eq!((composition.width, composition.height), (3, 2));
        assert_eq!(
            composition.loop_count,
            if encoded_loop == u8::MAX {
                0
            } else {
                encoded_loop + 1
            }
        );
        assert!(composition.has_unknown_boxes);
        assert_eq!(composition.instruction_sets.len(), 2);
        assert_eq!(
            (
                composition.instruction_sets[0].flags,
                composition.instruction_sets[0].repeat,
                composition.instruction_sets[0].tick
            ),
            (1, 17, 19)
        );
        assert_eq!(
            (
                composition.instruction_sets[0].instructions[0].target_x,
                composition.instruction_sets[0].instructions[0].target_y
            ),
            (23, 29)
        );
        assert_eq!(
            (
                composition.instruction_sets[0].instructions[0].target_width,
                composition.instruction_sets[0].instructions[0].target_height
            ),
            (3, 2)
        );
        assert_eq!(
            (
                composition.instruction_sets[1].repeat,
                composition.instruction_sets[1].tick
            ),
            (31, 37)
        );
        assert!(composition.instruction_sets[1].instructions.is_empty());
    }
}

#[test]
fn actual_raw_composition_keeps_options_order_missing_geometry_and_reader_error_priority() {
    let limits = ResourceLimits::default();
    for payload in [&[][..], box32(*b"free", &[]).as_slice()] {
        assert_eq!(
            parse_composition(raw_metadata_box(payload, *b"comp", 99), &limits).err(),
            Some(DecodeError::MalformedInput {
                offset: 107,
                kind: MalformedKind::MissingRequiredStructure
            })
        );
    }
    let payload = box32(*b"inst", &[]);
    assert_eq!(
        parse_composition(raw_metadata_box(&payload, *b"comp", 99), &limits).err(),
        Some(DecodeError::MalformedInput {
            offset: 107,
            kind: MalformedKind::InvalidBoxOrder
        })
    );
    let mut payload = raw_composition_options(0);
    let offset = 107 + payload.len() as u64;
    payload.extend_from_slice(&box32(*b"copt", &[]));
    assert_eq!(
        parse_composition(raw_metadata_box(&payload, *b"comp", 99), &limits).err(),
        Some(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::InvalidBoxOrder
        })
    );
    assert_eq!(
        parse_composition(raw_metadata_box(&[0], *b"comp", 99), &limits).err(),
        Some(DecodeError::MalformedInput {
            offset: 107,
            kind: MalformedKind::InvalidBoxLength
        })
    );
    let composition = parse_composition(
        raw_metadata_box(&raw_composition_options(0), *b"comp", 99),
        &limits,
    )
    .unwrap();
    assert!(!composition.has_unknown_boxes);
    assert!(composition.instruction_sets.is_empty());
}

#[test]
fn actual_raw_layer_references_preserve_implicit_index_explicit_source_and_first_error_offset() {
    assert_eq!(validate_layer_references(&[], 0), Ok(()));
    let first = parse_compositing_layer(
        raw_metadata_box(&[], *b"jplh", 19),
        &ResourceLimits::default(),
    )
    .unwrap();
    let second = parse_compositing_layer(
        raw_metadata_box(&[], *b"jplh", 27),
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(
        validate_layer_references(&[first, second], 1),
        Err(DecodeError::MalformedInput {
            offset: 27,
            kind: MalformedKind::InvalidBoxContents
        })
    );
    let payload = box32(*b"creg", &[0, 1, 0, 1, 255, 255, 1, 1, 0, 0]);
    let layer = parse_compositing_layer(
        raw_metadata_box(&payload, *b"jplh", 41),
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(
        validate_layer_references(std::slice::from_ref(&layer), usize::from(u16::MAX)),
        Err(DecodeError::MalformedInput {
            offset: 41,
            kind: MalformedKind::InvalidBoxContents
        })
    );
    assert_eq!(
        validate_layer_references(std::slice::from_ref(&layer), usize::from(u16::MAX) + 1),
        Ok(())
    );
}

fn valid_ht_codestream(width: u32, height: u32, style: u8) -> Vec<u8> {
    let mut siz = Vec::new();
    siz.extend_from_slice(&0x4000_u16.to_be_bytes());
    siz.extend_from_slice(&width.to_be_bytes());
    siz.extend_from_slice(&height.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&width.to_be_bytes());
    siz.extend_from_slice(&height.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&1_u16.to_be_bytes());
    siz.extend_from_slice(&[7, 1, 1]);

    let mut bytes = 0xff4f_u16.to_be_bytes().to_vec();
    bytes.extend(marker_segment(0xff51, &siz));
    bytes.extend(marker_segment(0xff50, &[0, 2, 0, 0, 0, 8]));
    bytes.extend(marker_segment(0xff52, &[0, 0, 0, 1, 0, 0, 2, 2, style, 1]));
    bytes.extend(marker_segment(0xff5c, &[0, 0x40]));
    let tile_part_start = bytes.len();
    let mut sot = Vec::new();
    sot.extend_from_slice(&0_u16.to_be_bytes());
    sot.extend_from_slice(&14_u32.to_be_bytes());
    sot.extend_from_slice(&[0, 1]);
    bytes.extend(marker_segment(0xff90, &sot));
    bytes.extend_from_slice(&0xff93_u16.to_be_bytes());
    assert_eq!(bytes.len() - tile_part_start, 14);
    bytes.extend_from_slice(&0xffd9_u16.to_be_bytes());
    bytes
}

fn boxed_file(file_type: &[u8], codestream: &[u8]) -> Vec<u8> {
    let mut bytes = box32(*b"jP  ", &SIGNATURE_MAGIC);
    bytes.extend(box32(*b"ftyp", file_type));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&32_u32.to_be_bytes());
    image_header.extend_from_slice(&64_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut jp2_header = box32(*b"ihdr", &image_header);
    jp2_header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 16]));
    bytes.extend(box32(*b"jp2h", &jp2_header));
    bytes.extend(box32(*b"jp2c", codestream));
    bytes
}

#[test]
fn routes_canonical_jph_inspection_past_ht_decoder_construction() {
    let bytes = boxed_file(b"jph \0\0\0\0jph ", &valid_ht_codestream(64, 32, 0x40));
    let inspected = inspect_jph(&bytes, &ResourceLimits::default()).unwrap();
    assert!(inspected.file().file_type().is_jph_compatible());
    assert!(
        inspected
            .codestream(0)
            .unwrap()
            .profile
            .uses_high_throughput()
    );
    let decoded = crate::decode::decode_jph(&bytes, &crate::DecodeOptions::default());
    assert!(matches!(
        decoded,
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::Truncated,
            ..
        })
    ));
}

#[test]
fn accepts_canonical_jph_with_all_legacy_htdeclared_codestream() {
    let mut codestream = valid_ht_codestream(64, 32, 0x00);
    let capability = codestream
        .windows(6)
        .position(|window| window == [0x00, 0x02, 0x00, 0x00, 0x00, 0x08])
        .unwrap();
    codestream[capability + 4..capability + 6].copy_from_slice(&0x8008_u16.to_be_bytes());
    let bytes = boxed_file(b"jph \0\0\0\0jph ", &codestream);
    let inspected = inspect_jph(&bytes, &ResourceLimits::default()).unwrap();
    let profile = &inspected.codestream(0).unwrap().profile;
    assert!(profile.is_part15());
    assert!(!profile.uses_high_throughput());
}

#[test]
fn rejects_jph_brand_and_codestream_profile_inconsistencies() {
    for file_type in [
        &b"jph \0\0\0\0jp2 "[..],
        &b"jp2 \0\0\0\0jph "[..],
        &b"jph \0\0\0\x01jph "[..],
    ] {
        let bytes = boxed_file(file_type, &valid_ht_codestream(64, 32, 0x40));
        assert!(matches!(
            parse(&bytes, &ResourceLimits::default()),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::InvalidProfile,
                ..
            })
        ));
    }

    let branded_jph = boxed_file(b"jph \0\0\0\0jph ", &valid_codestream(64, 32));
    assert!(matches!(
        inspect_jph(&branded_jph, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidProfile,
            ..
        })
    ));
    let mislabeled_jp2 = boxed_file(b"jp2 \0\0\0\0jp2 ", &valid_ht_codestream(64, 32, 0xc0));
    assert!(matches!(
        parse_and_inspect(&mislabeled_jp2, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidProfile,
            ..
        })
    ));
}

fn raw_container_start(jpx: bool, header: Option<&[u8]>) -> Vec<u8> {
    let mut bytes = box32(*b"jP  ", &SIGNATURE_MAGIC);
    bytes.extend(box32(
        *b"ftyp",
        if jpx {
            b"jpx \0\0\0\0jpx "
        } else {
            b"jp2 \0\0\0\0jp2 "
        },
    ));
    if let Some(header) = header {
        bytes.extend(box32(*b"jp2h", header));
    }
    bytes
}

fn raw_container_owned_header() -> Vec<u8> {
    let mut header = raw_jp2_header_image(u8::MAX, 3);
    header.extend(box32(*b"bpcc", &[7, 0x87, 37]));
    header.extend(box32(*b"colr", &[3, 173, 219, 1, 128, 255, 0, 17]));
    header.extend(box32(*b"pclr", &[0, 2, 2, 7, 0x87, 5, 0x80, 7, 0x7f]));
    header.extend(box32(*b"cmap", &[0, 0, 1, 0, 0, 1, 1, 1]));
    header.extend(box32(
        *b"cdef",
        &raw_channel_definition_payload(&[(0, 0, 1), (1, 2, 0)]),
    ));
    header.extend(box32(*b"res ", &box32(*b"resc", &raw_resolution_payload())));
    header
}

#[test]
fn actual_raw_container_retains_complete_header_and_original_uninspected_codestream_bytes() {
    let mut bytes = raw_container_start(false, Some(&raw_container_owned_header()));
    let offset = bytes.len();
    bytes.extend(box32(*b"jp2c", &[0, 255, 128, 17]));
    let file = parse(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(file.box_count, 4);
    assert_eq!((file.metadata_boxes, file.metadata_depth), (0, 0));
    assert_eq!(
        (
            file.header.image.width,
            file.header.image.height,
            file.header.image.components
        ),
        (3, 2, 3)
    );
    assert!(file.header.image.unknown_color_space && file.header.image.intellectual_property);
    assert_eq!(file.header.image.bit_depth, ComponentBitDepth::Variable);
    assert_eq!(
        (
            file.header.color.precedence,
            file.header.color.approximation
        ),
        (173, 219)
    );
    assert_eq!(
        file.header.color.icc_profile(),
        Some(&[1, 128, 255, 0, 17][..])
    );
    assert_eq!(
        (
            file.header.nested_box_count,
            file.header.palette_entries,
            file.header.palette_columns
        ),
        (7, 2, 2)
    );
    assert_eq!(
        file.header.palette.as_ref().unwrap().values,
        [5, -128, 7, 127]
    );
    assert_eq!(
        (
            file.header.component_mappings.len(),
            file.header.channel_definition_records.len()
        ),
        (2, 2)
    );
    assert!(file.header.capture_resolution.is_some());
    assert_eq!(file.header.display_resolution, None);
    assert_eq!(file.codestreams[0].header.offset(), offset as u64);
    assert!(std::ptr::eq(file.codestreams[0].data, &bytes[offset + 8..]));
    assert_eq!(file.codestreams[0].codestream_header, None);
    assert!(parse_and_inspect(&bytes, &ResourceLimits::default()).is_err());
}

#[test]
fn actual_raw_container_attaches_every_owned_association_without_changing_other_streams() {
    for count in 0..6 {
        let mut bytes = raw_container_start(true, Some(&raw_container_owned_header()));
        let mut headers = Vec::new();
        for index in 0..count {
            let payload = box32(*b"colr", &[3, index as u8, 201, 255, index as u8]);
            let start = bytes.len();
            bytes.extend(box32(*b"jpch", &payload));
            headers.push((start, bytes.len()));
        }
        let mut streams = Vec::new();
        for index in 0..count + 2 {
            let start = bytes.len();
            bytes.extend(box32(*b"jp2c", &[index as u8, 255, 0]));
            streams.push((start, bytes.len()));
        }
        let file = parse(&bytes, &ResourceLimits::default()).unwrap();
        assert_eq!(file.box_count, (5 + 2 * count) as u64);
        for (index, (start, end)) in streams.iter().copied().enumerate() {
            let stream = &file.codestreams[index];
            assert_eq!(stream.header.offset(), start as u64);
            assert!(std::ptr::eq(stream.data, &bytes[start + 8..end]));
            if index < count {
                let association = stream.codestream_header.as_ref().unwrap();
                let (header_start, header_end) = headers[index];
                assert_eq!(association.header.offset(), header_start as u64);
                assert!(std::ptr::eq(
                    association.payload,
                    &bytes[header_start + 8..header_end]
                ));
                let parsed = association.parsed.as_ref().unwrap();
                assert_eq!(
                    (parsed.color.precedence, parsed.color.approximation),
                    (index as u8, 201)
                );
                assert_eq!(parsed.color.icc_profile(), Some(&[255, index as u8][..]));
                assert_eq!(parsed.palette, file.header.palette);
                assert_eq!(parsed.component_mappings, file.header.component_mappings);
                assert_eq!(
                    parsed.channel_definition_records,
                    file.header.channel_definition_records
                );
                assert_eq!(parsed.nested_box_count, 1);
                assert_ne!(
                    parsed.palette.as_ref().unwrap().values.as_ptr(),
                    file.header.palette.as_ref().unwrap().values.as_ptr()
                );
            } else {
                assert_eq!(stream.codestream_header, None);
            }
        }
    }
}

#[test]
fn actual_raw_container_retains_borrowed_layers_owned_composition_and_all_instruction_defaults() {
    let mut bytes = raw_container_start(true, Some(&image_header_box(3, 2)));
    let mut layer = box32(*b"creg", &[0, 2, 0, 2, 0, 1, 1, 1, 0, 0]);
    layer.extend(box32(*b"cgrp", &box32(*b"colr", &[3, 17, 19, 255, 0])));
    layer.extend(box32(*b"opct", &[2, 3, 17, 128, 255, 0]));
    layer.extend(box32(*b"xml ", &[11]));
    let start = bytes.len();
    bytes.extend(box32(*b"jplh", &layer));
    let end = bytes.len();
    let mut composition = raw_composition_options(7);
    composition.extend(box32(*b"inst", &[0, 0, 0, 11, 0, 0, 0, 9]));
    composition.extend(box32(*b"free", &[17]));
    bytes.extend(box32(*b"comp", &composition));
    bytes.extend(box32(*b"jp2c", &[]));
    bytes.extend(box32(*b"jp2c", &[17]));
    let file = parse(&bytes, &ResourceLimits::default()).unwrap();
    let layer = &file.compositing_layers[0];
    assert!(std::ptr::eq(layer.payload, &bytes[start + 8..end]));
    assert_eq!(
        (layer.horizontal_grid_size, layer.vertical_grid_size),
        (2, 2)
    );
    assert_eq!(layer.registrations[0].codestream_index, 1);
    assert_eq!(layer.color_group[0].icc_profile(), Some(&[255, 0][..]));
    assert_eq!(
        layer.opacity,
        Some(LayerOpacity::ChromaKey {
            channels: 3,
            values: vec![17, 128, 255, 0]
        })
    );
    assert_eq!(layer.nested_metadata_boxes, 1);
    let composition = file.composition.unwrap();
    assert_eq!(
        (
            composition.width,
            composition.height,
            composition.loop_count
        ),
        (3, 2, 8)
    );
    assert!(composition.has_unknown_boxes);
    assert_eq!(
        (
            composition.instruction_sets[0].flags,
            composition.instruction_sets[0].repeat,
            composition.instruction_sets[0].tick
        ),
        (0, 11, 9)
    );
    assert!(composition.instruction_sets[0].instructions.is_empty());
}

#[test]
fn actual_raw_container_keeps_profile_order_and_count_before_payload_priorities() {
    for jpx in [false, true] {
        for kind in [*b"jpch", *b"jplh", *b"comp"] {
            let mut bytes = raw_container_start(jpx, None);
            let offset = bytes.len() as u64;
            bytes.extend(box32(kind, &[0]));
            assert_eq!(
                parse(&bytes, &ResourceLimits::default()).err(),
                Some(DecodeError::MalformedInput {
                    offset,
                    kind: if jpx {
                        MalformedKind::InvalidBoxOrder
                    } else {
                        MalformedKind::InvalidFileType
                    },
                })
            );
        }
    }
    let limits = ResourceLimits::default()
        .with_maximum_codestreams(1)
        .unwrap();
    let mut bytes = raw_container_start(true, Some(&image_header_box(3, 2)));
    bytes.extend(box32(*b"jpch", &[]));
    bytes.extend(box32(*b"jpch", &[0]));
    assert_eq!(
        parse(&bytes, &limits).err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::Codestreams,
            limit: 1,
            actual: 2
        })
    );
    let mut bytes = minimal_jp2();
    let offset = bytes.len() as u64;
    bytes.extend(box32(*b"jp2c", &[]));
    assert_eq!(
        parse(&bytes, &limits).err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::Codestreams,
            limit: 1,
            actual: 2
        })
    );
    assert_eq!(
        parse(&bytes, &ResourceLimits::default()).err(),
        Some(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::InvalidBoxContents
        })
    );
    let mut bytes = raw_container_start(true, Some(&image_header_box(3, 2)));
    bytes.extend(box32(*b"jplh", &[0]));
    let limits = ResourceLimits::default().with_coding_style_limits_for_test(0, 33);
    assert_eq!(
        parse(&bytes, &limits).err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::Layers,
            limit: 0,
            actual: 1
        })
    );
}

#[test]
fn actual_raw_container_keeps_missing_excess_association_and_first_reference_error_priority() {
    let header = image_header_box(3, 2);
    for count in 0..3 {
        let mut bytes = raw_container_start(true, Some(&header));
        for _ in 0..count {
            bytes.extend(box32(*b"jpch", &[]));
        }
        assert_eq!(
            parse(&bytes, &ResourceLimits::default()).err(),
            Some(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::MissingRequiredStructure
            })
        );
    }
    let mut bytes = raw_container_start(true, Some(&header));
    bytes.extend(box32(*b"jpch", &[]));
    bytes.extend(box32(*b"jpch", &[]));
    let layer_offset = bytes.len() as u64;
    bytes.extend(box32(
        *b"jplh",
        &box32(*b"creg", &[0, 1, 0, 1, 0, 9, 1, 1, 0, 0]),
    ));
    bytes.extend(box32(*b"jp2c", &[]));
    assert_eq!(
        parse(&bytes, &ResourceLimits::default()).err(),
        Some(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidBoxContents
        })
    );
    bytes.extend(box32(*b"jp2c", &[]));
    assert_eq!(
        parse(&bytes, &ResourceLimits::default()).err(),
        Some(DecodeError::MalformedInput {
            offset: layer_offset,
            kind: MalformedKind::InvalidBoxContents
        })
    );
}

#[test]
fn actual_raw_container_derives_metadata_depth_counts_progress_and_empty_stream_admission() {
    let mut bytes = raw_container_start(true, Some(&image_header_box(3, 2)));
    let mut association = box32(*b"xml ", &[1]);
    association.extend(box32(*b"asoc", &box32(*b"xml ", &[2])));
    bytes.extend(box32(*b"asoc", &association));
    bytes.extend(box32(*b"jp2c", &[]));
    bytes.extend(box32(*b"uuid", &[17]));
    let file = parse(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(
        (file.metadata_boxes, file.metadata_depth, file.box_count),
        (5, 3, 6)
    );
    assert!(file.codestreams[0].data.is_empty());
    let offset = bytes.len() as u64;
    bytes.push(0);
    assert_eq!(
        parse(&bytes, &ResourceLimits::default()).err(),
        Some(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::InvalidBoxLength
        })
    );
    let mut bytes = minimal_jp2();
    bytes.extend(box32(*b"asoc", &[0]));
    assert_eq!(
        parse(&bytes, &ResourceLimits::default()).err(),
        Some(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::Truncated
        })
    );
}

fn minimal_jp2() -> Vec<u8> {
    let mut bytes = box32(*b"jP  ", &SIGNATURE_MAGIC);
    bytes.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&32_u32.to_be_bytes());
    image_header.extend_from_slice(&64_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut jp2_header = box32(*b"ihdr", &image_header);
    jp2_header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 16]));
    bytes.extend(box32(*b"jp2h", &jp2_header));
    bytes.extend(box32(*b"jp2c", &[0xff, 0x4f, 0xff, 0xd9]));
    bytes
}

#[test]
fn icc_color_specification_preserves_bounded_profile_bytes() {
    let mut bytes = box32(*b"jP  ", &SIGNATURE_MAGIC);
    bytes.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut jp2_header = box32(*b"ihdr", &image_header);
    jp2_header.extend(box32(*b"colr", &[2, 0, 0, 0xde, 0xad, 0xbe, 0xef]));
    bytes.extend(box32(*b"jp2h", &jp2_header));
    bytes.extend(box32(*b"jp2c", &[0xff, 0x4f, 0xff, 0xd9]));

    let parsed = parse(&bytes, &ResourceLimits::default()).unwrap();
    assert!(matches!(
        parsed.header().color.method,
        ColorMethod::RestrictedIcc { profile_bytes: 4 }
    ));
    assert_eq!(
        parsed.header().color.icc_profile(),
        Some(&[0xde, 0xad, 0xbe, 0xef][..])
    );
    let component = crate::image::TypedComponent::from_parts(
        1,
        1,
        crate::codestream::ComponentInfo {
            precision: 8,
            signed: false,
            x_subsampling: 1,
            y_subsampling: 1,
            x_registration: 0,
            y_registration: 0,
        },
        crate::image::TypedSamples::Unsigned(vec![0]),
    );
    let image = crate::image::TypedImage::from_components(
        1,
        1,
        vec![component],
        &ResourceLimits::default(),
    )
    .unwrap();
    assert!(matches!(
        crate::color::convert_jp2_color(&image, &parsed.header().color, &ResourceLimits::default()),
        Err(DecodeError::UnsupportedColorConversion {
            reason: crate::UnsupportedColorConversion::IccProfile
        })
    ));
}

fn image_header_box(width: u32, height: u32) -> Vec<u8> {
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&height.to_be_bytes());
    image_header.extend_from_slice(&width.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 16]));
    header
}

fn jpx_with_codestreams(
    file_type_payload: &[u8],
    codestreams: &[Vec<u8>],
    codestream_headers: &[Vec<u8>],
) -> Vec<u8> {
    let mut bytes = box32(*b"jP  ", &SIGNATURE_MAGIC);
    bytes.extend(box32(*b"ftyp", file_type_payload));
    bytes.extend(box32(*b"jp2h", &image_header_box(64, 32)));
    for header in codestream_headers {
        bytes.extend(box32(*b"jpch", header));
    }
    for codestream in codestreams {
        bytes.extend(box32(*b"jp2c", codestream));
    }
    bytes
}

#[test]
fn sarah_dev_2d75f3e8f6_repeated_signature_is_not_ignorable_metadata() {
    assert_eq!(assert_unique_container_prefix(*b"jP  "), 9);
}

#[test]
fn sarah_dev_056d9fbfb2_repeated_file_type_is_not_ignorable_metadata() {
    assert_eq!(assert_unique_container_prefix(*b"ftyp"), 9);
}

fn assert_unique_container_prefix(kind: [u8; 4]) -> usize {
    let original = include_bytes!("../../validation/image-consumer-probe/tests/fixtures/gray.jp2");
    let limits = ResourceLimits::default();
    assert!(parse(original, &limits).is_ok());
    assert!(parse_and_inspect(original, &limits).is_ok());
    assert!(crate::decode::decode_jp2(original, &crate::DecodeOptions::default()).is_ok());
    let mut positions = Vec::new();
    let mut position = 0;
    while position < original.len() {
        positions.push(position);
        let length = u32::from_be_bytes(original[position..position + 4].try_into().unwrap());
        position += usize::try_from(length).unwrap();
    }
    positions.push(position);
    assert_eq!(positions.len(), 5);
    assert_eq!(position, original.len());
    let payload = if kind == *b"jP  " {
        &original[8..positions[1]]
    } else {
        &original[positions[1] + 8..positions[2]]
    };
    let mut cases = 0;
    for &offset in &positions[2..] {
        for header in 0..3 {
            let duplicate = match header {
                0 => box32(kind, payload),
                1 => {
                    let mut bytes = 1_u32.to_be_bytes().to_vec();
                    bytes.extend_from_slice(&kind);
                    bytes.extend_from_slice(
                        &u64::try_from(16 + payload.len()).unwrap().to_be_bytes(),
                    );
                    bytes.extend_from_slice(payload);
                    bytes
                }
                _ => {
                    let mut bytes = 0_u32.to_be_bytes().to_vec();
                    bytes.extend_from_slice(&kind);
                    bytes.extend_from_slice(payload);
                    bytes
                }
            };
            let insert = |extra: &[u8]| {
                let mut bytes = original[..offset].to_vec();
                bytes.extend_from_slice(extra);
                bytes.extend_from_slice(&original[offset..]);
                bytes
            };
            let bytes = insert(&duplicate);
            let snapshot = bytes.clone();
            let expected = Some(DecodeError::MalformedInput {
                offset: u64::try_from(offset).unwrap(),
                kind: MalformedKind::InvalidBoxOrder,
            });
            assert_eq!(
                parse(&bytes, &limits).err(),
                expected,
                "kind={kind:?} offset={offset} header={header}"
            );
            assert_eq!(parse_and_inspect(&bytes, &limits).err(), expected);
            assert_eq!(
                crate::decode::decode_jp2(&bytes, &crate::DecodeOptions::default()).err(),
                expected,
            );
            assert_eq!(bytes, snapshot);

            let benign = insert(&box32(*b"free", &duplicate));
            assert!(parse(&benign, &limits).is_ok());
            assert!(crate::decode::decode_jp2(&benign, &crate::DecodeOptions::default()).is_ok());
            cases += 1;
        }
    }
    let mut invalid_length = 7_u32.to_be_bytes().to_vec();
    invalid_length.extend_from_slice(&kind);
    let mut bytes = original[..positions[2]].to_vec();
    bytes.extend(invalid_length);
    bytes.extend_from_slice(&original[positions[2]..]);
    assert_eq!(
        parse(&bytes, &limits).err(),
        Some(DecodeError::MalformedInput {
            offset: u64::try_from(positions[2]).unwrap(),
            kind: MalformedKind::InvalidBoxLength,
        })
    );
    cases
}

#[test]
fn parses_minimal_file() {
    let bytes = minimal_jp2();
    let file = parse(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(file.file_type.brand, BoxType::JP2_BRAND);
    assert_eq!(file.header.image.width, 64);
    assert_eq!(file.header.image.height, 32);
    assert_eq!(file.header.image.components, 1);
    assert_eq!(
        file.header.image.bit_depth,
        ComponentBitDepth::Uniform {
            bits: 8,
            signed: false
        }
    );
    assert_eq!(
        file.header.color.method,
        ColorMethod::Enumerated { color_space: 16 }
    );
    assert_eq!(file.codestream(0).unwrap().data, [0xff, 0x4f, 0xff, 0xd9]);
    assert_eq!(file.box_count, 4);
}

#[test]
fn parses_extended_and_to_eof_boxes() {
    let mut extended = 1_u32.to_be_bytes().to_vec();
    extended.extend_from_slice(b"uuid");
    extended.extend_from_slice(&20_u64.to_be_bytes());
    extended.extend_from_slice(b"data");

    let reader = BoxReader::new(&extended, &ResourceLimits::default()).unwrap();
    let boxes = reader.collect::<Result<Vec<_>, _>>().unwrap();
    assert_eq!(boxes[0].header.header_length(), 16);
    assert_eq!(boxes[0].payload, b"data");

    let mut to_eof = 0_u32.to_be_bytes().to_vec();
    to_eof.extend_from_slice(b"xml ");
    to_eof.extend_from_slice(b"content");
    let boxes = BoxReader::new(&to_eof, &ResourceLimits::default())
        .unwrap()
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    assert_eq!(boxes[0].header.total_length(), 15);
    assert_eq!(boxes[0].payload, b"content");
}

#[test]
fn rejects_invalid_length_and_order() {
    let mut invalid = 7_u32.to_be_bytes().to_vec();
    invalid.extend_from_slice(b"free");
    assert!(matches!(
        BoxReader::new(&invalid, &ResourceLimits::default())
            .unwrap()
            .next()
            .unwrap(),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBoxLength,
            ..
        })
    ));

    let mut bytes = box32(*b"jP  ", &SIGNATURE_MAGIC);
    bytes.extend(box32(*b"jp2h", &[]));
    assert!(matches!(
        parse(&bytes, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBoxOrder,
            ..
        })
    ));
}

#[test]
fn every_prefix_fails_without_panicking() {
    let bytes = minimal_jp2();
    for length in 0..bytes.len() {
        assert!(parse(&bytes[..length], &ResourceLimits::default()).is_err());
    }
}

#[test]
fn enforces_metadata_limit() {
    let bytes = minimal_jp2();
    let limits = ResourceLimits::default()
        .with_maximum_metadata_bytes(31)
        .unwrap();
    assert!(matches!(
        parse(&bytes, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::MetadataBytes,
            ..
        })
    ));
}

#[test]
fn requires_bpcc_for_variable_component_depths() {
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&2_u16.to_be_bytes());
    image_header.extend_from_slice(&[0xff, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 16]));
    assert!(matches!(
        parse_jp2_header(&header, &ResourceLimits::default(), 0),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::MissingRequiredStructure,
            ..
        })
    ));

    let mut with_bpcc = box32(*b"ihdr", &image_header);
    with_bpcc.extend(box32(*b"bpcc", &[7, 0x87]));
    with_bpcc.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 16]));
    let parsed = parse_jp2_header(&with_bpcc, &ResourceLimits::default(), 0).unwrap();
    assert_eq!(parsed.image.components, 2);
}

#[test]
fn palette_lookup_matches_independent_complete_native_shape_oracle() {
    let mut contexts = 0;
    for entries in [0, 1, 2, 3, u16::MAX] {
        for column_count in [0, 1, 2, 3, 255, 256, 257] {
            for value_count in [0, 1, 2, 5, 6, 11, 16] {
                let columns = (0..column_count)
                    .map(|index| PaletteColumn {
                        precision: [0, 8, 38, u8::MAX][index % 4],
                        signed: index % 2 == 0,
                    })
                    .collect();
                let values = (0..value_count)
                    .map(|index| [i64::MIN, -1, 0, 1, i64::MAX][index % 5])
                    .collect::<Vec<_>>();
                let palette = Palette {
                    entries,
                    columns,
                    values: values.clone(),
                };
                assert_eq!(palette.entries(), entries);
                assert_eq!(palette.columns().len(), column_count);
                for entry in [0, 1, 2, 3, u16::MAX - 1, u16::MAX] {
                    for column in [0, 1, 2, 3, u8::MAX - 1, u8::MAX] {
                        let address = u128::from(entry) * column_count as u128 + u128::from(column);
                        let expected = if column_count > u8::MAX as usize {
                            Err(DecodeError::MalformedInput {
                                offset: 0,
                                kind: MalformedKind::ArithmeticOverflow,
                            })
                        } else if entry >= entries || usize::from(column) >= column_count {
                            Err(DecodeError::MalformedInput {
                                offset: 0,
                                kind: MalformedKind::InvalidBoxContents,
                            })
                        } else if address > usize::MAX as u128 {
                            Err(DecodeError::MalformedInput {
                                offset: 0,
                                kind: MalformedKind::ArithmeticOverflow,
                            })
                        } else {
                            values.get(address as usize).copied().ok_or(
                                DecodeError::MalformedInput {
                                    offset: 0,
                                    kind: MalformedKind::InvalidBoxContents,
                                },
                            )
                        };
                        assert_eq!(
                            palette.value(entry, column),
                            expected,
                            "entries={entries}, columns={column_count}, values={value_count}, entry={entry}, column={column}"
                        );
                        contexts += 1;
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 8_820);
}

#[test]
fn palette_lookup_preserves_physical_stride_and_first_error() {
    let values = [i64::MIN, -1, 0, i64::MAX, 42, -17];
    let mut palette = Palette {
        entries: 2,
        columns: vec![
            PaletteColumn {
                precision: 0,
                signed: false,
            };
            3
        ],
        values: values.to_vec(),
    };
    for entry in 0..2 {
        for column in 0..3 {
            assert_eq!(
                palette.value(entry, column),
                Ok(values[usize::from(entry) * 3 + usize::from(column)])
            );
        }
    }
    palette.entries = 0;
    assert_eq!(
        palette.value(0, 0),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidBoxContents,
        })
    );
    palette.columns.resize(
        256,
        PaletteColumn {
            precision: 255,
            signed: true,
        },
    );
    palette.values.clear();
    assert_eq!(
        palette.value(u16::MAX, u8::MAX),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        })
    );
}

#[test]
fn validates_palette_mapping_relationships() {
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 16]));
    header.extend(box32(*b"pclr", &[0, 1, 1, 7, 42]));
    assert!(matches!(
        parse_jp2_header(&header, &ResourceLimits::default(), 0),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::MissingRequiredStructure,
            ..
        })
    ));

    header.extend(box32(*b"cmap", &[0, 0, 1, 0]));
    let parsed = parse_jp2_header(&header, &ResourceLimits::default(), 0).unwrap();
    assert_eq!(parsed.palette_entries, 1);
    assert_eq!(parsed.palette_columns, 1);
    assert_eq!(parsed.component_mapping_entries, 1);
    let palette = parsed.palette.as_ref().unwrap();
    assert_eq!(palette.columns()[0].precision, 8);
    assert!(!palette.columns()[0].signed);
    assert_eq!(palette.value(0, 0).unwrap(), 42);
    assert_eq!(
        parsed.component_mappings[0],
        ComponentMapping {
            component: 0,
            mapping_type: MappingType::Palette { column: 0 },
        }
    );
}

#[test]
fn retains_signed_palette_and_channel_definition_records() {
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 16]));
    header.extend(box32(*b"pclr", &[0, 1, 1, 0x84, 0x1d]));
    header.extend(box32(*b"cmap", &[0, 0, 1, 0]));
    header.extend(box32(
        *b"cdef",
        &[0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0xff, 0xff, 0xff, 0xff],
    ));
    let parsed = parse_jp2_header(&header, &ResourceLimits::default(), 0).unwrap();
    let palette = parsed.palette.as_ref().unwrap();
    assert_eq!(
        palette.columns()[0],
        PaletteColumn {
            precision: 5,
            signed: true,
        }
    );
    assert_eq!(palette.value(0, 0).unwrap(), -3);
    assert_eq!(parsed.channel_definition_records.len(), 2);
    assert_eq!(
        parsed.channel_definition_records[0]
            .definition
            .channel_type(),
        ChannelType::Color
    );
    assert_eq!(
        parsed.channel_definition_records[1]
            .definition
            .association(),
        ChannelAssociation::Unassociated
    );
}

#[test]
fn rejects_invalid_mapping_type_and_bounds_output_channels() {
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 16]));
    header.extend(box32(*b"cmap", &[0, 0, 2, 0]));
    assert!(matches!(
        parse_jp2_header(&header, &ResourceLimits::default(), 0),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBoxContents,
            ..
        })
    ));

    let mut mappings = Vec::new();
    for _ in 0..65 {
        mappings.extend_from_slice(&[0, 0, 0, 0]);
    }
    let mut bounded = box32(*b"ihdr", &image_header);
    bounded.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 16]));
    bounded.extend(box32(*b"cmap", &mappings));
    assert!(matches!(
        parse_jp2_header(&bounded, &ResourceLimits::default(), 0),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Components,
            limit: 64,
            actual: 65,
        })
    ));
}

#[test]
fn complete_native_association_and_selected_header_validation_preserve_raw_choices() {
    let bytes = minimal_jp2();
    let parsed = parse(&bytes, &ResourceLimits::default()).unwrap();
    let fallback = parsed.header().clone();
    let mut explicit = fallback.clone();
    explicit.image.width = u32::MAX;
    explicit.color = ColorSpecification::enumerated(u32::MAX);
    for offset in [0, 1, u64::MAX] {
        let box_header = BoxHeader {
            box_type: BoxType::JP2_BRAND,
            offset,
            header_length: 0,
            total_length: 0,
        };
        let stream = CodestreamBox {
            header: box_header,
            data: &[],
            codestream_header: None,
        };
        assert_eq!(
            associated_header_for_codestream(&stream, &fallback),
            Ok(&fallback)
        );
        let stream = CodestreamBox {
            header: box_header,
            data: &[],
            codestream_header: Some(CodestreamHeaderAssociation {
                header: box_header,
                payload: &[],
                parsed: Some(explicit.clone()),
            }),
        };
        assert_eq!(
            associated_header_for_codestream(&stream, &fallback),
            Ok(&explicit)
        );
        let stream = CodestreamBox {
            header: box_header,
            data: &[],
            codestream_header: Some(CodestreamHeaderAssociation {
                header: box_header,
                payload: &[255],
                parsed: None,
            }),
        };
        assert_eq!(
            associated_header_for_codestream(&stream, &fallback),
            Err(DecodeError::MalformedInput {
                offset,
                kind: MalformedKind::MissingRequiredStructure
            })
        );
        let mut file = parsed.clone();
        file.file_type.brand = BoxType::JPX_BRAND;
        file.codestreams = vec![stream];
        let options = crate::DecodeOptions::new(
            ResourceLimits::HARDENED
                .with_maximum_input_bytes(0)
                .unwrap(),
        );
        assert_eq!(
            crate::decode::decode_jpx_file(&file, 0, &options),
            Err(DecodeError::MalformedInput {
                offset,
                kind: MalformedKind::MissingRequiredStructure
            })
        );
    }
    let data = valid_codestream(64, 32);
    let mut info = crate::codestream::parse(&data, &ResourceLimits::default()).unwrap();
    let mut contexts = 0;
    for header_width in [0, 64] {
        for source_width in [0, 64] {
            for bits in [0, 1, 8, u8::MAX] {
                for uniform in [None, Some(0), Some(8), Some(u8::MAX)] {
                    for sign in [false, true] {
                        for source_sign in [None, Some(false), Some(true)] {
                            for variable in [false, true] {
                                for offset in [0, u64::MAX] {
                                    let mut header = fallback.clone();
                                    header.image.width = header_width;
                                    header.image.bit_depth = if variable {
                                        ComponentBitDepth::Variable
                                    } else {
                                        ComponentBitDepth::Uniform { bits, signed: sign }
                                    };
                                    info.image_size.width = source_width;
                                    info.image_size.uniform_bit_depth = uniform;
                                    info.image_size.uniform_signed = source_sign;
                                    let expected = if header_width != source_width
                                        || (!variable
                                            && (uniform != Some(bits) || source_sign != Some(sign)))
                                    {
                                        Err(DecodeError::MalformedInput {
                                            offset,
                                            kind: MalformedKind::ContainerCodestreamMismatch,
                                        })
                                    } else {
                                        Ok(())
                                    };
                                    assert_eq!(
                                        validate_selected_header(&header, &info, offset),
                                        expected
                                    );
                                    contexts += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 1_536);
}

#[test]
fn cross_checks_container_and_codestream_headers() {
    let codestream = valid_codestream(64, 32);
    let mut bytes = box32(*b"jP  ", &SIGNATURE_MAGIC);
    bytes.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&32_u32.to_be_bytes());
    image_header.extend_from_slice(&64_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut jp2_header = box32(*b"ihdr", &image_header);
    jp2_header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 16]));
    bytes.extend(box32(*b"jp2h", &jp2_header));
    bytes.extend(box32(*b"jp2c", &codestream));
    let inspected = parse_and_inspect(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(inspected.codestream(0).unwrap().image_size.width, 64);

    let height_offset = 12 + 20 + 8 + 8;
    bytes[height_offset..height_offset + 4].copy_from_slice(&31_u32.to_be_bytes());
    assert!(matches!(
        parse_and_inspect(&bytes, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::ContainerCodestreamMismatch,
            ..
        })
    ));
}

#[test]
fn retains_and_inspects_explicit_jpx_codestreams_and_headers() {
    let first = valid_codestream(64, 32);
    let second = valid_codestream(17, 9);
    let bytes = jpx_with_codestreams(
        b"vend\0\0\0\0jpxb",
        &[first.clone(), second.clone()],
        &[image_header_box(64, 32), image_header_box(17, 9)],
    );
    let inspected = parse_and_inspect(&bytes, &ResourceLimits::default()).unwrap();
    assert!(inspected.file.file_type.is_jpx_compatible());
    assert_eq!(
        inspected.file.file_type.compatible_brands(),
        &[BoxType::JPX_BASELINE_BRAND]
    );
    assert_eq!(inspected.codestream_count(), 2);
    assert_eq!(inspected.codestream(0).unwrap().image_size.width, 64);
    assert_eq!(inspected.codestream(1).unwrap().image_size.height, 9);
    assert_eq!(inspected.file.codestream(0).unwrap().data, first);
    assert_eq!(inspected.file.codestream(1).unwrap().data, second);
    assert!(
        inspected
            .file
            .codestream(1)
            .unwrap()
            .codestream_header()
            .unwrap()
            .parsed_header()
            .is_some()
    );
    assert!(matches!(
        inspected.file.codestream(2),
        Err(DecodeError::CodestreamIndexOutOfRange {
            index: 2,
            codestreams: 2,
        })
    ));

    let mismatched = jpx_with_codestreams(
        b"jpx \0\0\0\0jpx ",
        &[valid_codestream(64, 32), valid_codestream(17, 9)],
        &[image_header_box(64, 32), image_header_box(18, 9)],
    );
    assert!(matches!(
        parse_and_inspect(&mismatched, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::ContainerCodestreamMismatch,
            ..
        })
    ));
}

#[test]
fn bounds_jpx_codestream_count_and_rejects_jp2_duplicates() {
    let codestream = valid_codestream(64, 32);
    let bytes = jpx_with_codestreams(
        b"jpx \0\0\0\0jpx ",
        &[codestream.clone(), codestream.clone()],
        &[],
    );
    let limits = ResourceLimits::default()
        .with_maximum_codestreams(1)
        .unwrap();
    assert!(matches!(
        parse(&bytes, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Codestreams,
            limit: 1,
            actual: 2,
        })
    ));

    let jp2 = jpx_with_codestreams(b"jp2 \0\0\0\0jp2 ", &[codestream.clone(), codestream], &[]);
    assert!(matches!(
        parse(&jp2, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBoxContents,
            ..
        })
    ));
}

#[test]
fn rejects_duplicate_compatible_brands_and_late_codestream_headers() {
    let duplicate = jpx_with_codestreams(b"jpx \0\0\0\0jpxbjpxb", &[valid_codestream(64, 32)], &[]);
    assert!(matches!(
        parse(&duplicate, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBoxContents,
            ..
        })
    ));

    let brand_bounded =
        jpx_with_codestreams(b"jpx \0\0\0\0jp2 jpxb", &[valid_codestream(64, 32)], &[]);
    let limits = ResourceLimits::default()
        .with_maximum_compatible_brands(1)
        .unwrap();
    assert!(matches!(
        parse(&brand_bounded, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::CompatibleBrands,
            limit: 1,
            actual: 2,
        })
    ));

    let mut late = jpx_with_codestreams(b"jpx \0\0\0\0jpx ", &[valid_codestream(64, 32)], &[]);
    late.extend(box32(*b"jpch", &image_header_box(64, 32)));
    assert!(matches!(
        parse(&late, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBoxOrder,
            ..
        })
    ));
}

#[test]
fn rejects_contradictory_jp2_primary_and_jpx_compatibility() {
    let contradictory = boxed_file(b"jp2 \0\0\0\0jp2 jpx ", &valid_codestream(64, 32));
    assert!(matches!(
        parse(&contradictory, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidFileType,
            ..
        })
    ));
}

#[test]
fn retains_validated_layer_registration_and_static_composition_options() {
    let codestream = valid_codestream(64, 32);
    let mut layered = box32(*b"jP  ", &SIGNATURE_MAGIC);
    layered.extend(box32(*b"ftyp", b"jpx \0\0\0\0jpx "));
    layered.extend(box32(*b"jp2h", &image_header_box(64, 32)));
    let mut registration = 10_u16.to_be_bytes().to_vec();
    registration.extend_from_slice(&10_u16.to_be_bytes());
    registration.extend_from_slice(&0_u16.to_be_bytes());
    registration.extend_from_slice(&[10, 10, 7, 9]);
    layered.extend(box32(*b"jplh", &box32(*b"creg", &registration)));
    let mut options = 32_u32.to_be_bytes().to_vec();
    options.extend_from_slice(&64_u32.to_be_bytes());
    options.push(0);
    layered.extend(box32(*b"comp", &box32(*b"copt", &options)));
    layered.extend(box32(*b"jp2c", &codestream));
    let parsed = parse(&layered, &ResourceLimits::default()).unwrap();
    let layer = parsed.compositing_layer(0).unwrap();
    assert_eq!(layer.horizontal_grid_size(), 10);
    assert_eq!(
        layer.registrations()[0],
        CodestreamRegistration {
            codestream_index: 0,
            horizontal_subsampling: 10,
            vertical_subsampling: 10,
            horizontal_offset: 7,
            vertical_offset: 9,
        }
    );
    assert_eq!(parsed.composition().unwrap().width, 64);
    assert_eq!(parsed.composition().unwrap().height, 32);

    let mut invalid_reference = layered.clone();
    let reference = invalid_reference
        .windows(4)
        .position(|window| window == *b"creg")
        .unwrap()
        + 8;
    invalid_reference[reference..reference + 2].copy_from_slice(&1_u16.to_be_bytes());
    assert!(matches!(
        parse(&invalid_reference, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBoxContents,
            ..
        })
    ));
}

#[test]
fn parses_layer_color_opacity_and_instruction_fields() {
    let codestream = valid_codestream(64, 32);
    let mut layered = box32(*b"jP  ", &SIGNATURE_MAGIC);
    layered.extend(box32(*b"ftyp", b"jpx \0\0\0\0jpx "));
    layered.extend(box32(*b"jp2h", &image_header_box(64, 32)));
    let color_group = box32(*b"cgrp", &box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
    let mut layer_header = color_group;
    layer_header.extend(box32(*b"opct", &[2, 1, 7]));
    layered.extend(box32(*b"jplh", &layer_header));
    let mut options = 32_u32.to_be_bytes().to_vec();
    options.extend_from_slice(&64_u32.to_be_bytes());
    options.push(1);
    let mut instruction = 0x27_u16.to_be_bytes().to_vec();
    instruction.extend_from_slice(&1_u16.to_be_bytes());
    instruction.extend_from_slice(&10_u32.to_be_bytes());
    for value in [1_u32, 2, 3, 4, 0x8000_0005, 1, 6, 7, 8, 9] {
        instruction.extend_from_slice(&value.to_be_bytes());
    }
    let mut composition = box32(*b"copt", &options);
    composition.extend(box32(*b"inst", &instruction));
    layered.extend(box32(*b"comp", &composition));
    layered.extend(box32(*b"jp2c", &codestream));
    let parsed = parse(&layered, &ResourceLimits::default()).unwrap();
    let layer = parsed.compositing_layer(0).unwrap();
    assert!(layer.has_color_group());
    assert!(matches!(
        layer.opacity(),
        Some(LayerOpacity::ChromaKey {
            channels: 1,
            values,
        }) if values == &[7]
    ));
    let composition = parsed.composition().unwrap();
    assert_eq!(composition.loop_count, 2);
    assert_eq!(composition.instruction_sets.len(), 1);
    let parsed_instruction = composition.instruction_sets[0].instructions[0];
    assert_eq!(parsed_instruction.target_x, 1);
    assert_eq!(parsed_instruction.life, 50);
    assert!(parsed_instruction.persistent);
    assert_eq!(parsed_instruction.source_width, 8);
}

#[test]
fn rejects_reserved_opacity_and_instruction_flags() {
    let codestream = valid_codestream(64, 32);
    let mut invalid_opacity = box32(*b"jP  ", &SIGNATURE_MAGIC);
    invalid_opacity.extend(box32(*b"ftyp", b"jpx \0\0\0\0jpx "));
    invalid_opacity.extend(box32(*b"jp2h", &image_header_box(64, 32)));
    invalid_opacity.extend(box32(*b"jplh", &box32(*b"opct", &[3])));
    invalid_opacity.extend(box32(*b"jp2c", &codestream));
    assert!(matches!(
        parse(&invalid_opacity, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBoxContents,
            ..
        })
    ));

    let mut invalid_instruction = box32(*b"jP  ", &SIGNATURE_MAGIC);
    invalid_instruction.extend(box32(*b"ftyp", b"jpx \0\0\0\0jpx "));
    invalid_instruction.extend(box32(*b"jp2h", &image_header_box(64, 32)));
    invalid_instruction.extend(box32(*b"jplh", &[]));
    let mut options = 32_u32.to_be_bytes().to_vec();
    options.extend_from_slice(&64_u32.to_be_bytes());
    options.push(0);
    let mut reserved = 8_u16.to_be_bytes().to_vec();
    reserved.extend_from_slice(&0_u16.to_be_bytes());
    reserved.extend_from_slice(&1_u32.to_be_bytes());
    let mut composition = box32(*b"copt", &options);
    composition.extend(box32(*b"inst", &reserved));
    invalid_instruction.extend(box32(*b"comp", &composition));
    invalid_instruction.extend(box32(*b"jp2c", &codestream));
    assert!(matches!(
        parse(&invalid_instruction, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBoxContents,
            ..
        })
    ));
}

#[test]
fn inherits_partial_jpx_codestream_header_color_metadata() {
    let codestream = valid_codestream(64, 32);
    let mut bytes = box32(*b"jP  ", &SIGNATURE_MAGIC);
    bytes.extend(box32(*b"ftyp", b"jpx \0\0\0\0jpx "));
    bytes.extend(box32(*b"jp2h", &image_header_box(64, 32)));
    let full_header = image_header_box(64, 32);
    let first_box_length = u32::from_be_bytes([
        full_header[0],
        full_header[1],
        full_header[2],
        full_header[3],
    ]) as usize;
    bytes.extend(box32(*b"jpch", &full_header[..first_box_length]));
    bytes.extend(box32(*b"jp2c", &codestream));
    let parsed = parse_and_inspect(&bytes, &ResourceLimits::default()).unwrap();
    let inherited = parsed
        .file()
        .codestream(0)
        .unwrap()
        .codestream_header()
        .unwrap()
        .parsed_header()
        .unwrap();
    assert!(matches!(
        inherited.color.method(),
        ColorMethod::Enumerated {
            color_space: ENUMERATED_SRGB
        }
    ));
}

#[test]
fn applies_palette_mapping_and_channel_overrides_in_partial_jpch() {
    let codestream = valid_codestream(64, 32);
    let mut override_boxes = box32(*b"pclr", &[0, 2, 1, 7, 3, 11]);
    override_boxes.extend(box32(*b"cmap", &[0, 0, 1, 0]));
    override_boxes.extend(box32(*b"cdef", &[0, 1, 0, 0, 0, 0, 0, 1]));
    let bytes = jpx_with_codestreams(b"jpx \0\0\0\0jpx ", &[codestream], &[override_boxes]);
    let parsed = parse(&bytes, &ResourceLimits::default()).unwrap();
    let header = parsed
        .codestream(0)
        .unwrap()
        .codestream_header()
        .unwrap()
        .parsed_header()
        .unwrap();
    assert_eq!(header.palette_entries, 2);
    assert_eq!(header.palette.as_ref().unwrap().value(1, 0).unwrap(), 11);
    assert_eq!(header.component_mapping_entries, 1);
    assert_eq!(header.channel_definitions, 1);
}

#[test]
fn retains_general_layer_cdef_and_nested_metadata() {
    let codestream = valid_codestream(64, 32);
    let mut bytes = box32(*b"jP  ", &SIGNATURE_MAGIC);
    bytes.extend(box32(*b"ftyp", b"jpx \0\0\0\0jpx "));
    bytes.extend(box32(*b"jp2h", &image_header_box(64, 32)));
    let cdef = box32(*b"cdef", &[0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]);
    let nested = box32(*b"asoc", &box32(*b"lbl ", b"layer"));
    let mut layer = cdef;
    layer.extend(nested);
    bytes.extend(box32(*b"jplh", &layer));
    bytes.extend(box32(*b"asoc", &box32(*b"asoc", &box32(*b"xml ", b"<x/>"))));
    bytes.extend(box32(*b"jp2c", &codestream));
    let parsed = parse(&bytes, &ResourceLimits::default()).unwrap();
    let layer = parsed.compositing_layer(0).unwrap();
    assert_eq!(layer.channel_definition_records().len(), 2);
    assert_eq!(layer.nested_metadata_boxes(), 2);
    assert_eq!(parsed.metadata_boxes(), 3);
    assert_eq!(parsed.metadata_depth(), 3);
}
