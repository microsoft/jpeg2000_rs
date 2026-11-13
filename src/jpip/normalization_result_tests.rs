use super::*;

#[test]
fn checked_word_writes_preserve_big_endian_bytes_errors_and_every_outside_byte() {
    for length in [0, 1, 3, 4, 5, 9] {
        for position in [0, 1, 3, length, length + 1, usize::MAX - 2, usize::MAX] {
            for value in [0_u32, 0x01_23_fe_ff, u32::MAX] {
                let mut actual: Vec<u8> = (0..length).map(|index| 0xa0 + index as u8).collect();
                let mut expected = actual.clone();
                let owner = (actual.as_ptr(), actual.len(), actual.capacity());
                let end = position.saturating_add(4);
                let error = DecodeError::malformed(position as u64, MalformedKind::Truncated);
                let expected_result = if position <= end && end <= length {
                    let count = end - position;
                    expected[position..end].copy_from_slice(&value.to_be_bytes()[..count]);
                    if count == 4 { Ok(()) } else { Err(error) }
                } else {
                    Err(error)
                };
                assert_eq!(write_u32_be(&mut actual, position, value), expected_result);
                assert_eq!(actual, expected);
                assert_eq!((actual.as_ptr(), actual.len(), actual.capacity()), owner);
            }
        }
    }
    crate::allocation::with_refusal(0, || {
        let mut bytes = [0_u8; 4];
        assert_eq!(write_u32_be(&mut bytes, 0, 0x12_34_56_78), Ok(()));
        assert_eq!(bytes, [0x12, 0x34, 0x56, 0x78]);
        assert_eq!(
            crate::allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn checked_empty_packets_preserve_prefix_framing_sequence_and_storage() {
    for sop in [false, true] {
        for eph in [false, true] {
            for sequence in [0_u16, 255, 256, u16::MAX] {
                let mut actual = Vec::with_capacity(12);
                actual.extend_from_slice(&[7, 0xff, 19]);
                let owner = (actual.as_ptr(), actual.capacity());
                let mut expected = actual.clone();
                if sop {
                    expected.extend_from_slice(&[0xff, 0x91, 0, 4]);
                    expected.extend_from_slice(&sequence.to_be_bytes());
                }
                expected.push(0);
                if eph {
                    expected.extend_from_slice(&[0xff, 0x92]);
                }
                assert_eq!(append_empty_packet(&mut actual, sop, eph, sequence), Ok(()));
                assert_eq!(actual, expected);
                assert_eq!((actual.as_ptr(), actual.capacity()), owner);
            }
        }
    }
}

#[test]
fn automatic_templates_preserve_all_parts_psot_bytes_and_patch_before_final_limit_errors() {
    let main = vec![0xff, 0x4f, 19];
    let first = vec![0xff, 0x90, 0, 10, 0, 0, 9, 8, 7, 6, 0, 2, 0xff, 0x93];
    let mut second = first.clone();
    second.extend_from_slice(&[21, 22, 23]);
    let flat = vec![first.clone(), second.clone(), first.clone()];
    let nested = vec![vec![first.clone(), second.clone()], Vec::new(), vec![first]];
    let mut expected = main.clone();
    for header in &flat {
        let mut patched = header.clone();
        patched[6..10].copy_from_slice(&u32::try_from(header.len()).unwrap().to_be_bytes());
        expected.extend(patched);
    }
    expected.extend_from_slice(&EOC);
    let limits = ResourceLimits::default();
    assert_eq!(
        build_automatic_transition_template(&main, &nested, &limits).unwrap(),
        expected
    );
    assert_eq!(
        build_automatic_template(&main, &flat, &limits).unwrap(),
        expected
    );
    assert_eq!(nested[0][0][6..10], [9, 8, 7, 6]);
    let limited = limits
        .with_maximum_input_bytes(expected.len() as u64 - 1)
        .unwrap();
    let error = DecodeError::limit(
        Resource::InputBytes,
        expected.len() as u64 - 1,
        expected.len() as u64,
    );
    assert_eq!(
        build_automatic_transition_template(&main, &nested, &limited),
        Err(error)
    );
    assert_eq!(build_automatic_template(&main, &flat, &limited), Err(error));
    let tiny = limits.with_maximum_input_bytes(1).unwrap();
    let malformed = vec![vec![vec![0; 9]]];
    assert_eq!(
        build_automatic_transition_template(&main, &malformed, &tiny),
        Err(DecodeError::malformed(9, MalformedKind::Truncated))
    );
    assert_eq!(
        build_automatic_template(&main, &malformed[0], &tiny),
        Err(DecodeError::malformed(9, MalformedKind::Truncated))
    );
}

#[test]
fn automatic_cardinality_preserves_first_siz_and_geometry_before_tile_limit_errors() {
    let limits = ResourceLimits::default();
    let mut payload = vec![0_u8; 36];
    for (offset, value) in [(2, 10_u32), (6, 7), (18, 4), (22, 3), (26, 1), (30, 1)] {
        payload[offset..offset + 4].copy_from_slice(&value.to_be_bytes());
    }
    payload[34..36].copy_from_slice(&3_u16.to_be_bytes());
    let main = |payload: &[u8]| {
        let mut bytes = vec![0xff, 0x4f, 0xff, 0x51];
        bytes.extend_from_slice(&u16::try_from(payload.len() + 2).unwrap().to_be_bytes());
        bytes.extend_from_slice(payload);
        bytes
    };
    // Cardinality does not inspect the following component records or admit a complete SIZ.
    let mut first = main(&payload);
    first.extend_from_slice(&[0xff, 0x51, 0, 2]);
    assert_eq!(super::super::siz_cardinality(&first, &limits), Ok((6, 3)));
    assert_eq!(
        super::super::siz_cardinality(&main(&payload[..35]), &limits),
        Err(DecodeError::malformed(
            2,
            MalformedKind::InvalidImageGeometry
        ))
    );
    let mut preceding_error = vec![0xff, 0x4f, 0xff, 0x64, 0, 1];
    preceding_error.extend_from_slice(&first[2..]);
    assert_eq!(
        super::super::siz_cardinality(&preceding_error, &limits),
        Err(DecodeError::malformed(
            2,
            MalformedKind::InvalidMarkerLength
        ))
    );
    payload[2..6].copy_from_slice(&(limits.maximum_tiles() + 1).to_be_bytes());
    payload[6..10].copy_from_slice(&1_u32.to_be_bytes());
    payload[18..22].copy_from_slice(&1_u32.to_be_bytes());
    payload[22..26].copy_from_slice(&1_u32.to_be_bytes());
    payload[26..34].fill(0);
    assert_eq!(
        super::super::siz_cardinality(&main(&payload), &limits),
        Err(DecodeError::limit(
            Resource::Tiles,
            u64::from(limits.maximum_tiles()),
            u64::from(limits.maximum_tiles()) + 1,
        ))
    );
    payload[34..36].copy_from_slice(&(limits.maximum_components() + 1).to_be_bytes());
    assert_eq!(
        super::super::siz_cardinality(&main(&payload), &limits),
        Err(DecodeError::malformed(
            2,
            MalformedKind::InvalidImageGeometry
        ))
    );
    assert_eq!(ceil_div_jpip(9, 4), Ok(3));
    for (value, divisor) in [(0, 0), (u64::MAX, 2)] {
        assert_eq!(
            ceil_div_jpip(value, divisor),
            Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))
        );
    }
}

#[test]
fn automatic_main_header_requests_preserve_validation_and_reservation_error_order() {
    let input = [0xff, 0x4f, 0xff, 0x64, 0, 3, 7, 0xff, 0x57, 0, 3, 0];
    assert_eq!(normalize_main_header(&input).unwrap(), input[..7]);
    for input in [&[][..], &[0xff][..], &[0xff, 0x50][..]] {
        crate::allocation::with_refusal(0, || {
            assert_eq!(
                normalize_main_header(input),
                Err(DecodeError::malformed(
                    0,
                    MalformedKind::MissingRequiredStructure
                ))
            );
            assert_eq!(
                crate::allocation::empty_with_capacity::<u8>(1),
                Err(DecodeError::AllocationFailed)
            );
        });
    }
    crate::allocation::with_refusal(1, || {
        assert_eq!(normalize_main_header(&SOC), Ok(SOC.to_vec()));
        assert_eq!(
            crate::allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            normalize_main_header(&[0xff, 0x4f, 0xff]),
            Err(DecodeError::AllocationFailed)
        );
    });
    crate::allocation::with_refusal(1, || {
        assert_eq!(
            normalize_main_header(&[0xff, 0x4f, 0xff]),
            Err(DecodeError::malformed(2, MalformedKind::Truncated))
        );
        assert_eq!(
            crate::allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn automatic_main_header_refusal_preserves_input_and_exact_recovery() {
    let input = [0xff, 0x4f, 0xff, 0x64, 0, 3, 7, 0xff, 0x52, 0, 3, 9];
    let before = input;
    assert_eq!(
        crate::allocation::with_refusal(0, || normalize_main_header(&input)),
        Err(DecodeError::AllocationFailed)
    );
    assert_eq!(input, before);
    assert_eq!(normalize_main_header(&input).unwrap(), input);
    assert_eq!(
        normalize_main_header(&[0xff, 0x4f, 0xff]),
        Err(DecodeError::malformed(2, MalformedKind::Truncated))
    );
    assert_eq!(normalize_main_header(&input).unwrap(), input);
}

#[test]
fn raw_normalization_preserves_exact_markers_framing_optional_sod_and_input_storage() {
    let sources: &[(&[u8], &[u8])] = &[
        (&[], &[]),
        (&[0xff, 0x93], &[]),
        (&[0xff, 0x64, 0, 3, 7], &[0xff, 0x64, 0, 3, 7]),
        (&[0xff, 0x64, 0, 3, 7, 0xff, 0x93], &[0xff, 0x64, 0, 3, 7]),
        (&[0xff, 0x58, 0, 3, 0], &[]),
        (&[0xff, 0x58, 0, 3, 0, 0xff, 0x93], &[]),
        (&[0xff, 0x52, 0, 3, 9], &[0xff, 0x52, 0, 3, 9]),
    ];
    let mut cases = 0;
    for (source, retained) in sources {
        for tile in [0_u16, 1, 255, 256, u16::MAX] {
            for index in [0, 1, 255, 256, usize::MAX] {
                for count in [0, 1, 255] {
                    for framed in [false, true] {
                        let mut input = if framed {
                            vec![0xff, 0x90, 0, 10, 0x12, 0x34, 0, 0, 0, 0, 89, 22]
                        } else {
                            Vec::new()
                        };
                        input.extend_from_slice(source);
                        let before = input.clone();
                        let owner = (input.as_ptr(), input.len(), input.capacity());
                        let actual = normalize_tile_header(&input, tile, index, count);
                        if let Ok(index) = u8::try_from(index) {
                            let mut expected = vec![0xff, 0x90, 0, 10];
                            expected.extend_from_slice(&tile.to_be_bytes());
                            expected.extend_from_slice(&[0, 0, 0, 0, index, count]);
                            expected.extend_from_slice(retained);
                            expected.extend_from_slice(&[0xff, 0x93]);
                            assert_eq!(actual.as_ref().unwrap(), &expected);
                            assert_ne!(actual.as_ref().unwrap().as_ptr(), input.as_ptr());
                            if !framed && index == 0 && count == 1 {
                                assert_eq!(
                                    normalize_automatic_tile_headers(&input, tile).unwrap(),
                                    vec![expected]
                                );
                            }
                        } else {
                            assert_eq!(
                                actual,
                                Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))
                            );
                        }
                        assert_eq!(input, before);
                        assert_eq!((input.as_ptr(), input.len(), input.capacity()), owner);
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 1050);
}

#[test]
fn raw_normalization_retains_malformed_marker_and_index_error_precedence() {
    let cases: &[(&[u8], u64, MalformedKind)] = &[
        (&[0xff], 0, MalformedKind::Truncated),
        (&[0xff, 0x64, 0], 2, MalformedKind::Truncated),
        (&[0xff, 0x64, 0, 1], 0, MalformedKind::InvalidMarkerLength),
        (&[0xff, 0x64, 0, 3], 0, MalformedKind::Truncated),
        (&[0xff, 0x93, 0], 2, MalformedKind::MissingRequiredStructure),
        (&[0xff, 0x90, 0, 2], 0, MalformedKind::InvalidTilePart),
        (&[0xff, 0x90, 0, 10], 0, MalformedKind::Truncated),
    ];
    for (source, offset, kind) in cases {
        assert_eq!(
            normalize_tile_header(source, 0, 0, 1),
            Err(DecodeError::malformed(*offset, *kind))
        );
        let expected = if source.starts_with(&[0xff, 0x90]) {
            DecodeError::malformed(*offset, *kind)
        } else {
            DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
        };
        assert_eq!(normalize_tile_header(source, 0, 256, 1), Err(expected));
    }
}
