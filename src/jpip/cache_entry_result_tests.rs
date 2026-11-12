use super::*;

fn id(class: u64, stream: u64, bin: u64) -> DatabinId {
    DatabinId::from_wire(class, stream, bin).unwrap()
}

#[test]
fn actual_jpip_owned_fragment_derives_all_fields_and_moves_original_bytes_across_raw_frontiers() {
    let databin = id(7, 129, u64::MAX);
    let mut cases = 0;
    for offset in [0, 1, 15, 128, u64::MAX - 2, u64::MAX] {
        for size in [0_usize, 1, 2, 3, 9] {
            for last in [false, true] {
                for auxiliary in [None, Some(0), Some(u64::MAX)] {
                    for limit in [0, 1, 3, 128, 1_024] {
                        let limits = ResourceLimits::HARDENED
                            .with_maximum_input_bytes(limit)
                            .unwrap();
                        let mut bytes = Vec::with_capacity(size + 7);
                        bytes.extend((0..size).map(|index| u8::try_from(index).unwrap() ^ 0x80));
                        let expected = bytes.clone();
                        let pointer = bytes.as_ptr();
                        let result =
                            JpipFragment::new(databin, offset, bytes, last, auxiliary, &limits);
                        let end = u128::from(offset) + size as u128;
                        let error = if size == 0 && !last {
                            Some(DecodeError::malformed(
                                offset,
                                MalformedKind::InvalidJpipFragment,
                            ))
                        } else if end > u128::from(u64::MAX) {
                            Some(DecodeError::malformed(
                                offset,
                                MalformedKind::ArithmeticOverflow,
                            ))
                        } else if end > u128::from(limit) {
                            Some(DecodeError::LimitExceeded {
                                resource: Resource::InputBytes,
                                limit,
                                actual: u64::try_from(end).unwrap(),
                            })
                        } else {
                            None
                        };
                        if let Some(error) = error {
                            assert_eq!(result, Err(error));
                        } else {
                            let fragment = result.unwrap();
                            assert_eq!(fragment.databin(), databin);
                            assert_eq!(fragment.offset(), offset);
                            assert_eq!(fragment.bytes(), expected);
                            assert_eq!(
                                fragment.final_length(),
                                if last {
                                    Some(u64::try_from(end).unwrap())
                                } else {
                                    None
                                }
                            );
                            assert_eq!(fragment.auxiliary(), auxiliary);
                            assert_eq!(fragment.bytes().as_ptr(), pointer);
                        }
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 900);
}

#[test]
fn actual_jpip_owned_fragment_from_header_preserves_length_validation_and_owned_payload() {
    let limits = ResourceLimits::HARDENED
        .with_maximum_input_bytes(128)
        .unwrap();
    let databin = id(3, 0, 16);
    for body in [vec![], vec![0], vec![0xff, 0x80, 0, 1]] {
        for declared in [0, 1, body.len() as u64, u64::MAX] {
            for last in [false, true] {
                let header = super::super::JpipMessageHeader {
                    databin,
                    offset: 7,
                    length: declared,
                    last_byte: last,
                    auxiliary: Some(u64::MAX),
                    header_length: usize::MAX,
                };
                let result = JpipFragment::from_message(header, &body, &limits);
                if declared != body.len() as u64 || (body.is_empty() && !last) {
                    assert_eq!(
                        result,
                        Err(DecodeError::malformed(
                            7,
                            MalformedKind::InvalidJpipFragment
                        ))
                    );
                } else {
                    let fragment = result.unwrap();
                    assert_eq!((fragment.databin(), fragment.offset()), (databin, 7));
                    assert_eq!(fragment.bytes(), body);
                    assert_eq!(
                        fragment.final_length(),
                        if last { Some(7 + declared) } else { None }
                    );
                    assert_eq!(fragment.auxiliary(), Some(u64::MAX));
                    if !body.is_empty() {
                        assert_ne!(fragment.bytes().as_ptr(), body.as_ptr());
                    }
                }
            }
        }
    }
    let header = super::super::JpipMessageHeader {
        databin,
        offset: u64::MAX,
        length: 1,
        last_byte: true,
        auxiliary: None,
        header_length: 0,
    };
    let zero = limits.with_maximum_input_bytes(0).unwrap();
    assert_eq!(
        JpipFragment::from_message(header, &[0], &zero),
        Err(DecodeError::malformed(
            u64::MAX,
            MalformedKind::ArithmeticOverflow
        ))
    );
    assert_eq!(
        JpipFragment::from_message(header, &[], &zero),
        Err(DecodeError::malformed(
            u64::MAX,
            MalformedKind::InvalidJpipFragment
        ))
    );
}

#[test]
fn actual_jpip_byte_copy_and_point_copy_preserve_full_outside_frames_and_every_error() {
    let mut cases = 0;
    for output_size in [0_usize, 1, 3, 9] {
        for input_size in [0_usize, 1, 4, 11] {
            let input = vec![0x81; input_size];
            let copied = copy_bytes(&input);
            assert_eq!(copied, input);
            if !input.is_empty() {
                assert_ne!(copied.as_ptr(), input.as_ptr());
            }
            for start in [0, 1, 3, output_size, usize::MAX] {
                for offset in [0, 7, u64::MAX] {
                    let mut output = vec![0x55; output_size];
                    let mut expected = output.clone();
                    let end = start as u128 + input_size as u128;
                    let valid = end <= output_size as u128;
                    let result = copy_into(&mut output, start, &input, offset);
                    if valid {
                        expected[start..usize::try_from(end).unwrap()].copy_from_slice(&input);
                        assert_eq!(result, Ok(()));
                    } else {
                        assert_eq!(
                            result,
                            Err(DecodeError::malformed(
                                offset,
                                MalformedKind::ArithmeticOverflow
                            ))
                        );
                    }
                    assert_eq!(output, expected);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 240);
}

#[test]
fn actual_jpip_cache_empty_state_and_lookup_preserve_first_normalized_databin_identity() {
    let limits = ResourceLimits::HARDENED
        .with_maximum_input_bytes(129)
        .unwrap();
    let cache = DatabinCache::new(limits);
    assert_eq!(cache.limits, limits);
    assert_eq!(
        (
            cache.stored_bytes(),
            cache.accepted_fragments(),
            cache.databin_count()
        ),
        (0, 0, 0)
    );
    assert_eq!(cache.find_databin_index(id(0, 1, 2)), None);
    let ids = [id(0, 1, 2), id(1, 1, 2), id(2, 1, 2), id(8, u64::MAX, 16)];
    let cache = DatabinCache {
        limits,
        databins: ids
            .into_iter()
            .map(|id| super::super::Databin {
                id,
                fragments: Vec::new(),
                final_length: Some(0),
            })
            .collect(),
        stored_bytes: u64::MAX,
        accepted_fragments: 127,
    };
    assert_eq!(
        (
            cache.stored_bytes(),
            cache.accepted_fragments(),
            cache.databin_count()
        ),
        (u64::MAX, 127, 4)
    );
    for (wanted, expected) in [
        (id(0, 1, 2), Some(0)),
        (id(1, 1, 2), Some(0)),
        (id(2, 1, 2), Some(2)),
        (id(3, 1, 2), None),
        (id(8, u64::MAX, 16), Some(3)),
        (id(8, 1, 16), Some(3)),
        (id(0, 1, 3), None),
    ] {
        assert_eq!(cache.find_databin_index(wanted), expected);
    }
}

#[test]
fn actual_jpip_stored_extent_and_status_getters_retain_saturation_and_exact_completeness() {
    for offset in [0, 1, u64::MAX - 1, u64::MAX] {
        for size in [0_usize, 1, 2, 9] {
            let fragment = super::super::StoredFragment {
                offset,
                bytes: vec![0x80; size],
            };
            let end = u128::from(offset) + size as u128;
            assert_eq!(
                fragment.end(),
                u64::try_from(end.min(u128::from(u64::MAX))).unwrap()
            );
        }
    }
    for final_length in [None, Some(0), Some(1), Some(u64::MAX)] {
        for prefix in [0, 1, 2, u64::MAX] {
            let status = DatabinStatus {
                final_length,
                contiguous_prefix: prefix,
                stored_bytes: 127,
                intervals: u64::MAX,
            };
            assert_eq!(status.final_length(), final_length);
            assert_eq!(
                (
                    status.contiguous_prefix(),
                    status.stored_bytes(),
                    status.interval_count()
                ),
                (prefix, 127, u64::MAX)
            );
            assert_eq!(status.is_complete(), final_length == Some(prefix));
        }
    }
}

#[test]
fn actual_jpip_owned_byte_view_getters_and_move_keep_original_storage_without_cloning() {
    for size in [0_usize, 1, 3, 129] {
        let mut bytes = Vec::with_capacity(size + 7);
        bytes.extend((0..size).map(|index| u8::try_from(index).unwrap() ^ 0x80));
        let expected = bytes.clone();
        let pointer = bytes.as_ptr();
        let capacity = bytes.capacity();
        let view = JpipByteView { bytes };
        assert_eq!(view.as_bytes(), expected);
        assert_eq!((view.len(), view.is_empty()), (size, size == 0));
        assert_eq!(view.as_bytes().as_ptr(), pointer);
        let borrowed: &[u8] = view.as_ref();
        assert_eq!(borrowed.as_ptr(), pointer);
        let returned = view.into_bytes();
        assert_eq!(returned, expected);
        assert_eq!(returned.as_ptr(), pointer);
        assert_eq!(returned.capacity(), capacity);
    }
}
