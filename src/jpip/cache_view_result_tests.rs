use super::*;

fn id(class: u64, stream: u64, bin: u64) -> DatabinId {
    DatabinId::new(class, stream, bin).unwrap()
}

fn bin(id: DatabinId, fragments: &[(u64, &[u8])], final_length: Option<u64>) -> Databin {
    Databin {
        id,
        fragments: fragments
            .iter()
            .map(|(offset, bytes)| StoredFragment {
                offset: *offset,
                bytes: bytes.to_vec(),
            })
            .collect(),
        final_length,
    }
}

fn cache(databins: Vec<Databin>, limit: u64) -> DatabinCache {
    DatabinCache {
        limits: ResourceLimits::HARDENED
            .with_maximum_input_bytes(limit)
            .unwrap(),
        databins,
        stored_bytes: 123,
        accepted_fragments: 456,
    }
}

fn missing(offset: u64) -> DecodeError {
    DecodeError::malformed(offset, MalformedKind::MissingRequiredStructure)
}

fn limit(limit: u64, actual: u64) -> DecodeError {
    DecodeError::LimitExceeded {
        resource: Resource::InputBytes,
        limit,
        actual,
    }
}

#[test]
fn actual_jpip_cache_status_derives_every_field_and_native_fragment_order_without_validity_premises()
 {
    let bases: [(u64, &[u8]); 4] = [(0, b""), (0, b"ab"), (2, b"cd"), (1, b"z")];
    let databin = id(6, 3, 9);
    let mut cases = 0;
    for code in 0..=64 {
        let fragments = if code == 64 {
            Vec::new()
        } else {
            vec![
                bases[code % 4],
                bases[(code / 4) % 4],
                bases[(code / 16) % 4],
            ]
        };
        let (prefix, total) =
            fragments
                .iter()
                .fold((0_u64, 0_u128), |(prefix, total), (offset, bytes)| {
                    let end = u128::from(*offset) + bytes.len() as u128;
                    let next = if *offset == prefix {
                        u64::try_from(end.min(u128::from(u64::MAX))).unwrap()
                    } else {
                        prefix
                    };
                    (next, total + bytes.len() as u128)
                });
        let stored_bytes = u64::try_from(total.min(u128::from(u64::MAX))).unwrap();
        for final_length in [None, Some(0), Some(1), Some(2), Some(4), Some(u64::MAX)] {
            let state = cache(vec![bin(databin, &fragments, final_length)], 0);
            for alias in [6, 7] {
                let query = id(alias, 3, 9);
                let expected = DatabinStatus {
                    final_length,
                    contiguous_prefix: prefix,
                    stored_bytes,
                    intervals: fragments.len() as u64,
                };
                assert_eq!(state.status(query), Some(expected));
                assert_eq!(state.is_complete(query), final_length == Some(prefix));
                assert_eq!(expected.final_length(), final_length);
                assert_eq!(expected.contiguous_prefix(), prefix);
                assert_eq!(expected.stored_bytes(), stored_bytes);
                assert_eq!(expected.interval_count(), fragments.len() as u64);
                assert_eq!(state.stored_bytes(), 123);
                assert_eq!(state.accepted_fragments(), 456);
                cases += 1;
            }
            assert_eq!(state.status(id(6, 4, 9)), None);
            assert!(!state.is_complete(id(6, 3, 10)));
        }
    }
    assert_eq!(cases, 780);
}

#[test]
fn actual_jpip_cache_view_keeps_first_normalized_match_first_fragment_and_exact_missing_errors() {
    let first = id(6, 5, 0);
    let state = cache(
        vec![
            bin(first, &[(0, b"ab"), (2, b"cd")], Some(4)),
            bin(id(7, 5, 0), &[(0, b"later")], Some(5)),
            bin(id(2, 5, 0), &[], Some(0)),
            bin(id(0, 5, 0), &[(0, b"x")], Some(2)),
        ],
        0,
    );
    let view = state.databin_view(id(7, 5, 0)).unwrap();
    assert_eq!(state.status(first).unwrap().contiguous_prefix(), 4);
    assert_eq!(view.as_bytes(), b"ab");
    assert_ne!(
        view.as_bytes().as_ptr(),
        state.databins[0].fragments[0].bytes.as_ptr()
    );
    assert_eq!(state.databin_view(id(3, 5, 0)).unwrap().as_bytes(), b"");
    assert_eq!(state.databin_view(id(1, 5, 0)), Err(missing(1)));
    assert_eq!(state.databin_view(id(6, 6, 0)), Err(missing(0)));
    assert_eq!(state.databin_view(id(6, 5, 1)), Err(missing(0)));
    assert_eq!(state.databins[0].fragments[1].bytes, b"cd");
    assert_eq!(state.stored_bytes(), 123);
    assert_eq!(state.accepted_fragments(), 456);
}

#[test]
fn actual_jpip_cache_prefix_derives_first_fragment_offset_and_keeps_independent_owned_storage() {
    let state = cache(
        vec![
            bin(id(6, 8, 0), &[(0, b"abc"), (3, b"def")], None),
            bin(id(7, 8, 0), &[(0, b"later")], Some(5)),
            bin(id(2, 8, 0), &[(1, b"offset")], Some(7)),
            bin(id(0, 8, 0), &[], None),
        ],
        0,
    );
    let mut prefix = state.databin_prefix(id(7, 8, 0));
    assert_eq!(prefix, b"abc");
    assert!(!state.is_complete(id(6, 8, 0)));
    assert_ne!(
        prefix.as_ptr(),
        state.databins[0].fragments[0].bytes.as_ptr()
    );
    prefix[0] = 0;
    assert_eq!(state.databins[0].fragments[0].bytes, b"abc");
    for query in [id(3, 8, 0), id(1, 8, 0), id(6, 9, 0), id(6, 8, 1)] {
        assert!(state.databin_prefix(query).is_empty());
    }
}

#[test]
fn actual_jpip_cache_reconstruction_keeps_requested_order_repetition_and_original_cache_storage() {
    let first = id(6, 10, 0);
    let second = id(2, 10, 0);
    let state = cache(
        vec![
            bin(first, &[(0, b"AB")], Some(2)),
            bin(second, &[(0, b"CD")], Some(2)),
        ],
        64,
    );
    let cases: &[(&[DatabinId], &[u8])] = &[
        (&[], b""),
        (&[first], b"AB"),
        (&[second], b"CD"),
        (&[first, second], b"ABCD"),
        (&[second, first], b"CDAB"),
        (&[first, first], b"ABAB"),
        (&[id(7, 10, 0), id(3, 10, 0), first], b"ABCDAB"),
    ];
    for (layout, expected) in cases {
        let view = state.reconstruct(layout).unwrap();
        assert_eq!(view.as_bytes(), *expected);
        if !view.is_empty() {
            assert_ne!(
                view.as_bytes().as_ptr(),
                state.databins[0].fragments[0].bytes.as_ptr()
            );
            assert_ne!(
                view.as_bytes().as_ptr(),
                state.databins[1].fragments[0].bytes.as_ptr()
            );
        }
        let mut owned = view.into_bytes();
        if !owned.is_empty() {
            owned[0] = 0;
        }
        assert_eq!(state.databins[0].fragments[0].bytes, b"AB");
        assert_eq!(state.databins[1].fragments[0].bytes, b"CD");
        assert_eq!(state.stored_bytes(), 123);
        assert_eq!(state.accepted_fragments(), 456);
    }
}

#[test]
fn actual_jpip_cache_reconstruction_preserves_first_view_error_and_exact_input_budget_frontiers() {
    let first = id(6, 12, 0);
    let second = id(2, 12, 0);
    let incomplete = id(0, 12, 0);
    let absent = id(6, 12, 1);
    let mut cases = 0;
    for budget in [0, 1, 2, 4, 5] {
        let state = cache(
            vec![
                bin(first, &[(0, b"ab")], Some(2)),
                bin(second, &[(0, b"cde")], Some(3)),
                bin(incomplete, &[(0, b"x")], Some(2)),
            ],
            budget,
        );
        let cases_with_expected = [
            (vec![], Ok(Vec::new())),
            (vec![absent], Err(missing(0))),
            (
                vec![first, absent],
                Err(if budget < 2 {
                    limit(budget, 2)
                } else {
                    missing(0)
                }),
            ),
            (
                vec![first, second],
                if budget < 2 {
                    Err(limit(budget, 2))
                } else if budget < 5 {
                    Err(limit(budget, 5))
                } else {
                    Ok(b"abcde".to_vec())
                },
            ),
            (
                vec![first, incomplete],
                Err(if budget < 2 {
                    limit(budget, 2)
                } else {
                    missing(1)
                }),
            ),
            (
                vec![second, incomplete],
                Err(if budget < 3 {
                    limit(budget, 3)
                } else {
                    missing(1)
                }),
            ),
            (vec![absent, second], Err(missing(0))),
            (vec![incomplete, first], Err(missing(1))),
        ];
        for (layout, expected) in cases_with_expected {
            assert_eq!(
                state.reconstruct(&layout).map(JpipByteView::into_bytes),
                expected
            );
            assert_eq!(state.databins[0].fragments[0].bytes, b"ab");
            assert_eq!(state.databins[1].fragments[0].bytes, b"cde");
            assert_eq!(state.stored_bytes(), 123);
            assert_eq!(state.accepted_fragments(), 456);
            cases += 1;
        }
    }
    assert_eq!(cases, 40);
}

#[test]
fn actual_jpip_cache_read_producers_compose_original_fragment_normalization_and_reconstruction() {
    let mut state = DatabinCache::new(
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(64)
            .unwrap(),
    );
    let main = id(6, 14, 0);
    let tile = id(2, 14, 0);
    for (databin, offset, bytes, last) in [
        (main, 0, b"abcd".as_slice(), false),
        (id(7, 14, 0), 2, b"cdef".as_slice(), false),
        (main, 6, b"gh".as_slice(), true),
        (tile, 0, b"IJK".as_slice(), true),
    ] {
        let fragment =
            JpipFragment::new(databin, offset, bytes.to_vec(), last, None, &state.limits).unwrap();
        state.insert(fragment).unwrap();
    }
    let status = state.status(id(7, 14, 0)).unwrap();
    assert_eq!(status.final_length(), Some(8));
    assert_eq!(status.contiguous_prefix(), 8);
    assert_eq!(status.stored_bytes(), 8);
    assert_eq!(status.interval_count(), 1);
    assert!(state.is_complete(main));
    assert_eq!(state.databin_view(main).unwrap().as_bytes(), b"abcdefgh");
    assert_eq!(state.databin_prefix(main), b"abcdefgh");
    assert_eq!(
        state.reconstruct(&[main, tile, main]).unwrap().as_bytes(),
        b"abcdefghIJKabcdefgh"
    );
    assert_eq!(state.stored_bytes(), 11);
    assert_eq!(state.accepted_fragments(), 4);
    assert_eq!(state.databin_count(), 2);
}
