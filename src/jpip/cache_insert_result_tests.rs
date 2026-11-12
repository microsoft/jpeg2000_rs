use super::*;

type BinSnapshot = (DatabinId, Vec<(u64, Vec<u8>)>, Option<u64>);
type CacheSnapshot = (ResourceLimits, Vec<BinSnapshot>, u64, u64);
type Storage = (usize, usize, usize);
type CacheStorage = (Storage, Vec<(Storage, Vec<Storage>)>);

fn storage<T>(values: &Vec<T>) -> Storage {
    (values.as_ptr() as usize, values.len(), values.capacity())
}

fn cache_storage(cache: &DatabinCache) -> CacheStorage {
    (
        storage(&cache.databins),
        cache
            .databins
            .iter()
            .map(|bin| {
                (
                    storage(&bin.fragments),
                    bin.fragments
                        .iter()
                        .map(|fragment| storage(&fragment.bytes))
                        .collect(),
                )
            })
            .collect(),
    )
}

fn snapshot(cache: &DatabinCache) -> CacheSnapshot {
    (
        cache.limits,
        cache
            .databins
            .iter()
            .map(|bin| {
                (
                    bin.id,
                    bin.fragments
                        .iter()
                        .map(|stored| (stored.offset, stored.bytes.clone()))
                        .collect(),
                    bin.final_length,
                )
            })
            .collect(),
        cache.stored_bytes,
        cache.accepted_fragments,
    )
}

fn id(class: u64, bin: u64) -> DatabinId {
    DatabinId::from_wire(class, 3, bin).unwrap()
}

#[test]
fn actual_jpip_cache_insert_checked_clones_preserve_fields_and_independent_storage() {
    let mut cases = 0;
    for offset in [0, 1, u64::MAX] {
        for bytes in [vec![], vec![0], vec![0x80, 0xff, 0, 7]] {
            for final_length in [None, Some(0), Some(u64::MAX)] {
                let original = Databin {
                    id: id(7, u64::MAX),
                    fragments: vec![
                        StoredFragment {
                            offset,
                            bytes: bytes.clone(),
                        },
                        StoredFragment {
                            offset: 0,
                            bytes: vec![9, 8],
                        },
                    ],
                    final_length,
                };
                let mut cloned = original.clone();
                assert_eq!(cloned.id, original.id);
                assert_eq!(cloned.final_length, original.final_length);
                assert_ne!(cloned.fragments.as_ptr(), original.fragments.as_ptr());
                for (copy, source) in cloned.fragments.iter().zip(&original.fragments) {
                    assert_eq!(copy.offset, source.offset);
                    assert_eq!(copy.bytes, source.bytes);
                    if !source.bytes.is_empty() {
                        assert_ne!(copy.bytes.as_ptr(), source.bytes.as_ptr());
                    }
                }
                cloned.fragments[0].offset ^= 1;
                cloned.fragments[0].bytes.push(42);
                cloned.fragments[1].bytes[0] = 0;
                cloned.final_length = Some(11);
                assert_eq!(original.fragments[0].offset, offset);
                assert_eq!(original.fragments[0].bytes, bytes);
                assert_eq!(original.fragments[1].bytes, [9, 8]);
                assert_eq!(original.final_length, final_length);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 27);
}

#[test]
fn actual_jpip_cache_insert_errors_preserve_complete_physical_state_and_error_precedence() {
    let mut cases = 0;
    let mut errors = 0;
    let mut successes = 0;
    for stored in [
        vec![],
        vec![(0, vec![1, 2])],
        vec![(4, vec![5]), (0, vec![1, 2])],
        vec![(0, vec![1, 2]), (0, vec![1, 2])],
        vec![(u64::MAX, vec![9])],
    ] {
        for final_length in [None, Some(0), Some(2), Some(u64::MAX)] {
            for offset in [0, 1, 2, 4, u64::MAX] {
                for bytes in [vec![], vec![1], vec![1, 2], vec![0xff, 0x80]] {
                    for announced in [None, Some(0), Some(2), Some(u64::MAX)] {
                        for count in [0, 2, u64::MAX] {
                            let limits = ResourceLimits::HARDENED
                                .with_maximum_input_bytes(8)
                                .unwrap()
                                .with_maximum_jpip_fragments(2)
                                .unwrap();
                            let mut cache = DatabinCache {
                                limits,
                                databins: vec![
                                    Databin {
                                        id: id(4, 1),
                                        fragments: stored
                                            .iter()
                                            .map(|(offset, bytes)| StoredFragment {
                                                offset: *offset,
                                                bytes: bytes.clone(),
                                            })
                                            .collect(),
                                        final_length,
                                    },
                                    Databin {
                                        id: id(5, 1),
                                        fragments: vec![StoredFragment {
                                            offset: 0,
                                            bytes: vec![42],
                                        }],
                                        final_length: Some(1),
                                    },
                                    Databin {
                                        id: id(0, 9),
                                        fragments: vec![],
                                        final_length: Some(0),
                                    },
                                ],
                                stored_bytes: stored
                                    .iter()
                                    .map(|(_, bytes)| bytes.len() as u64)
                                    .sum(),
                                accepted_fragments: count,
                            };
                            let before = snapshot(&cache);
                            let owners = cache_storage(&cache);
                            let result = cache.insert(JpipFragment {
                                databin: id(5, 1),
                                offset,
                                bytes: bytes.clone(),
                                final_length: announced,
                                auxiliary: Some(u64::MAX),
                            });
                            if count == u64::MAX {
                                assert_eq!(
                                    result,
                                    Err(DecodeError::malformed(
                                        offset,
                                        MalformedKind::ArithmeticOverflow
                                    ))
                                );
                            } else if count == 2 {
                                assert_eq!(
                                    result,
                                    Err(DecodeError::limit(Resource::JpipFragments, 2, 3))
                                );
                            } else if offset == u64::MAX && !bytes.is_empty() {
                                assert_eq!(
                                    result,
                                    Err(DecodeError::malformed(
                                        offset,
                                        MalformedKind::ArithmeticOverflow
                                    ))
                                );
                            }
                            if result.is_err() {
                                assert_eq!(snapshot(&cache), before);
                                assert_eq!(cache_storage(&cache), owners);
                                errors += 1;
                            } else {
                                let after = snapshot(&cache);
                                assert_eq!(after.0, before.0);
                                assert_eq!(after.1.len(), before.1.len());
                                assert_eq!(after.1[0].0, before.1[0].0);
                                assert_eq!(&after.1[1..], &before.1[1..]);
                                assert_eq!(after.3, before.3 + 1);
                                assert!(after.2 <= 8);
                                successes += 1;
                            }
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 4_800);
    assert!(errors > 3_200);
    assert!(successes > 0);
}

#[test]
fn sarah_metadata_target_identity_preserves_sparse_union_and_error_frames() {
    let limits = ResourceLimits::HARDENED;
    let metadata = |stream| DatabinId::new(8, stream, 17).unwrap();
    let mut cache = DatabinCache::new(limits);
    for (stream, offset, bytes, last) in [
        (3, 2, &[3, 4][..], true),
        (9, 0, &[1, 2][..], false),
        (u64::MAX, 1, &[2, 3][..], false),
    ] {
        cache
            .insert(
                JpipFragment::new(
                    metadata(stream),
                    offset,
                    bytes.to_vec(),
                    last,
                    None,
                    &limits,
                )
                .unwrap(),
            )
            .unwrap();
    }
    assert_eq!(
        (
            cache.databin_count(),
            cache.stored_bytes(),
            cache.accepted_fragments()
        ),
        (1, 4, 3)
    );
    for stream in [0, 1, 3, 9, u64::MAX] {
        let query = metadata(stream);
        assert!(cache.is_complete(query));
        assert_eq!(cache.databin_view(query).unwrap().as_bytes(), &[1, 2, 3, 4]);
    }
    let before = snapshot(&cache);
    let owners = cache_storage(&cache);
    assert!(matches!(
        cache.insert(JpipFragment::new(metadata(127), 1, vec![255], false, None, &limits).unwrap()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::ConflictingJpipFragment,
            ..
        })
    ));
    assert_eq!(snapshot(&cache), before);
    assert_eq!(cache_storage(&cache), owners);
    for stream in [3, 9] {
        cache
            .insert(
                JpipFragment::new(
                    DatabinId::new(6, stream, 0).unwrap(),
                    0,
                    vec![42],
                    true,
                    None,
                    &limits,
                )
                .unwrap(),
            )
            .unwrap();
    }
    assert_eq!((cache.databin_count(), cache.stored_bytes()), (3, 6));
}

#[test]
fn reserved_wire_classes_cannot_mutate_recognized_or_physical_cache_state() {
    let mut cases = 0;
    for class in [3, 7] {
        for count in [0, 2, u64::MAX] {
            for limit in [0, 8] {
                for offset in [0, u64::MAX] {
                    let mut cache = DatabinCache {
                        limits: ResourceLimits::HARDENED
                            .with_maximum_input_bytes(limit)
                            .unwrap(),
                        databins: vec![
                            Databin {
                                id: id(class - 1, 1),
                                fragments: vec![StoredFragment {
                                    offset: 0,
                                    bytes: vec![42],
                                }],
                                final_length: Some(1),
                            },
                            Databin {
                                id: id(class, 1),
                                fragments: vec![StoredFragment {
                                    offset: 0,
                                    bytes: vec![9],
                                }],
                                final_length: Some(1),
                            },
                        ],
                        stored_bytes: u64::MAX,
                        accepted_fragments: count,
                    };
                    let before = snapshot(&cache);
                    let owners = cache_storage(&cache);
                    assert_eq!(
                        cache.insert(JpipFragment {
                            databin: id(class, 1),
                            offset,
                            bytes: vec![1, 2],
                            final_length: Some(0),
                            auxiliary: Some(u64::MAX),
                        }),
                        Err(DecodeError::malformed(0, MalformedKind::InvalidJpipHeader))
                    );
                    assert_eq!(snapshot(&cache), before);
                    assert_eq!(cache_storage(&cache), owners);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 24);
}

#[test]
fn actual_jpip_cache_insert_normalizes_exact_bytes_and_retains_first_alias_metadata() {
    let limits = ResourceLimits::HARDENED
        .with_maximum_input_bytes(16)
        .unwrap();
    let mut cache = DatabinCache::new(limits);
    let insert = |cache: &mut DatabinCache, class, offset, bytes: &[u8], last| {
        cache.insert(
            JpipFragment::new(id(class, 1), offset, bytes.to_vec(), last, None, &limits).unwrap(),
        )
    };
    insert(&mut cache, 4, 4, &[5, 6], false).unwrap();
    insert(&mut cache, 5, 0, &[1, 2], false).unwrap();
    assert_eq!(
        snapshot(&cache),
        (
            limits,
            vec![(id(4, 1), vec![(0, vec![1, 2]), (4, vec![5, 6])], None)],
            4,
            2
        )
    );
    insert(&mut cache, 5, 1, &[2, 3, 4, 5], false).unwrap();
    assert_eq!(
        snapshot(&cache),
        (
            limits,
            vec![(id(4, 1), vec![(0, vec![1, 2, 3, 4, 5, 6])], None)],
            6,
            3
        )
    );
    insert(&mut cache, 5, 6, &[], true).unwrap();
    insert(&mut cache, 5, 2, &[3, 4], false).unwrap();
    assert_eq!(
        snapshot(&cache),
        (
            limits,
            vec![(id(4, 1), vec![(0, vec![1, 2, 3, 4, 5, 6])], Some(6))],
            6,
            5
        )
    );
    let before = snapshot(&cache);
    let owners = cache_storage(&cache);
    assert_eq!(
        insert(&mut cache, 5, 2, &[0xff], false),
        Err(DecodeError::malformed(
            2,
            MalformedKind::ConflictingJpipFragment
        ))
    );
    assert_eq!(snapshot(&cache), before);
    assert_eq!(cache_storage(&cache), owners);
}
