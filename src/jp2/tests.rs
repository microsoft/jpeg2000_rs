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
