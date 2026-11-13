use super::*;

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
