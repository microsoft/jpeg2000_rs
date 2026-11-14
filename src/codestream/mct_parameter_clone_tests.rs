use super::*;

#[test]
fn resolved_owner_storage_first_later_empty_and_validation_frontier() {
    let limits = ResourceLimits::default();
    let parser = new_parser(&[], &limits).unwrap();
    let mut parameters = MctParameters {
        arrays: vec![
            MctArray::from_values(
                1,
                MctArrayKind::Decorrelation,
                MctNumericFormat::Int16,
                0,
                vec![1, 1],
            ),
            MctArray::from_values(2, MctArrayKind::Offset, MctNumericFormat::Int16, 0, vec![0]),
        ],
        records: vec![MctRecord {
            index: 7,
            collections: vec![MctCollectionReference {
                input_components: vec![0],
                output_components: vec![0],
                transform: MctCollectionReferenceTransform::Array {
                    kind: MctArrayKind::Decorrelation,
                    reversible: true,
                    transform_index: 1,
                    offset_index: 2,
                },
            }],
        }],
        order: vec![7],
    };
    let expected = parser
        .resolve_multiple_component_transform(&parameters, ResolvedCopyRole::Tile)
        .unwrap();
    for after in [0, 2, 5] {
        assert!(matches!(
            crate::allocation::with_refusal(after, || parser
                .resolve_multiple_component_transform(&parameters, ResolvedCopyRole::Tile)),
            Err(DecodeError::AllocationFailed)
        ));
        assert_eq!(
            parser
                .resolve_multiple_component_transform(&parameters, ResolvedCopyRole::Tile)
                .unwrap(),
            expected
        );
    }
    parameters.arrays[0].values.pop();
    let ordinary = parser
        .resolve_multiple_component_transform(&parameters, ResolvedCopyRole::Main)
        .unwrap_err();
    crate::allocation::with_refusal(4, || {
        assert_eq!(
            parser
                .resolve_multiple_component_transform(&parameters, ResolvedCopyRole::Main)
                .unwrap_err(),
            ordinary
        );
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
    parameters.order.clear();
    crate::allocation::with_refusal(0, || {
        assert!(
            parser
                .resolve_multiple_component_transform(&parameters, ResolvedCopyRole::Tile)
                .unwrap()
                .is_none()
        );
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn mct_owner_storage_nested_refusal_restore_and_empty_preserve_every_owner() {
    let original = MctParameters {
        arrays: vec![
            MctArray::from_values(
                0,
                MctArrayKind::Decorrelation,
                MctNumericFormat::Int32,
                0,
                vec![1, 2, 3],
            ),
            MctArray::from_values(
                7,
                MctArrayKind::Offset,
                MctNumericFormat::Int32,
                0,
                Vec::new(),
            ),
        ],
        records: vec![
            MctRecord {
                index: 3,
                collections: vec![reference(0, 1, 2), reference(24, 0, 1)],
            },
            MctRecord {
                index: 19,
                collections: Vec::new(),
            },
        ],
        order: vec![3, 19],
    };
    let before = original.clone();
    for after in [0, 4, 6, 7] {
        assert!(matches!(
            crate::allocation::with_refusal(after, || original.try_duplicate()),
            Err(DecodeError::AllocationFailed)
        ));
        assert_eq!(original, before);
        let copied = original.try_duplicate().unwrap();
        assert_eq!(copied, original);
        separate(&original.arrays, &copied.arrays);
        for (left, right) in original.arrays.iter().zip(&copied.arrays) {
            separate(&left.values, &right.values);
        }
        separate(&original.records, &copied.records);
        for (left, right) in original.records.iter().zip(&copied.records) {
            separate_record(left, right);
        }
        separate(&original.order, &copied.order);
    }
    let empty = MctParameters {
        arrays: Vec::new(),
        records: Vec::new(),
        order: Vec::new(),
    };
    crate::allocation::with_refusal(0, || {
        assert_eq!(empty.try_duplicate().unwrap(), empty);
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
}

fn reference(variant: usize, inputs: usize, outputs: usize) -> MctCollectionReference {
    let transform = if variant < 24 {
        MctCollectionReferenceTransform::Array {
            kind: [
                MctArrayKind::Dependency,
                MctArrayKind::Decorrelation,
                MctArrayKind::Offset,
            ][variant / 8],
            reversible: !variant.is_multiple_of(2),
            transform_index: [0, u8::MAX][variant / 2 % 2],
            offset_index: [0, u8::MAX][variant / 4 % 2],
        }
    } else {
        let variant = variant - 24;
        MctCollectionReferenceTransform::Wavelet(MctWavelet {
            transform: [
                MctWaveletType::Irreversible9x7,
                MctWaveletType::Reversible5x3,
            ][variant / 9],
            levels: [0, 1, u8::MAX][variant / 3 % 3],
            component_offset: [i32::MIN, 0, i32::MAX][variant % 3],
        })
    };
    MctCollectionReference {
        input_components: (0..inputs)
            .map(|index| [0, u16::MAX, 0, 17][index % 4])
            .collect(),
        output_components: (0..outputs)
            .map(|index| [7, u16::MAX, 7, 0][index % 4])
            .collect(),
        transform,
    }
}

fn record(index: u8, count: usize, variant: usize) -> MctRecord {
    MctRecord {
        index,
        collections: (0..count)
            .map(|slot| {
                reference(
                    (variant + slot * 13) % 42,
                    [0, 1, 3][slot % 3],
                    [0, 1, 4][(slot + variant) % 3],
                )
            })
            .collect(),
    }
}

fn separate<T>(left: &[T], right: &[T]) {
    assert_eq!(left.len(), right.len());
    if !left.is_empty() {
        assert_ne!(left.as_ptr(), right.as_ptr());
    }
}

fn separate_reference(left: &MctCollectionReference, right: &MctCollectionReference) {
    separate(&left.input_components, &right.input_components);
    separate(&left.output_components, &right.output_components);
}

fn separate_record(left: &MctRecord, right: &MctRecord) {
    separate(&left.collections, &right.collections);
    for (left, right) in left.collections.iter().zip(&right.collections) {
        separate_reference(left, right);
    }
}

#[test]
fn actual_mct_reference_clone_preserves_all_raw_fields_and_independent_buffers() {
    let mut cases = 0;
    for variant in 0..42 {
        for inputs in [0, 1, 3] {
            for outputs in [0, 1, 4] {
                let original = reference(variant, inputs, outputs);
                let before = format!("{original:?}");
                let mut copied = original.clone();
                assert_eq!(copied, original);
                separate_reference(&original, &copied);
                copied.input_components.push(31);
                copied.output_components.push(37);
                copied.transform = MctCollectionReferenceTransform::Wavelet(MctWavelet {
                    transform: MctWaveletType::Reversible5x3,
                    levels: 17,
                    component_offset: -19,
                });
                assert_eq!(format!("{original:?}"), before);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 378);
}

#[test]
fn actual_mct_record_clone_preserves_every_index_collection_and_nested_buffer() {
    let mut cases = 0;
    for index in 0..=u8::MAX {
        for count in [0, 1, 3] {
            for variant in [0, 11, 24, 41] {
                let original = record(index, count, variant);
                let before = format!("{original:?}");
                let mut copied = original.clone();
                assert_eq!(copied, original);
                separate_record(&original, &copied);
                copied.index ^= 0xff;
                for collection in &mut copied.collections {
                    collection.input_components.push(u16::MAX);
                    collection.output_components.push(31);
                }
                copied.collections.push(reference(41, 3, 4));
                assert_eq!(format!("{original:?}"), before);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 3_072);
}

#[test]
fn actual_mct_parameters_clone_preserves_unused_duplicate_dangling_data_and_order() {
    let mut cases = 0;
    for variant in 0..36 {
        for arrays in [0, 1, 3] {
            for records in [0, 1, 3] {
                for order in [0, 1, 4] {
                    let original = MctParameters {
                        arrays: (0..arrays)
                            .map(|slot| MctArray {
                                index: if slot == 2 { u8::MAX } else { 0 },
                                kind: [
                                    MctArrayKind::Dependency,
                                    MctArrayKind::Decorrelation,
                                    MctArrayKind::Offset,
                                ][variant / 12],
                                numeric_format: [
                                    MctNumericFormat::Int16,
                                    MctNumericFormat::Int32,
                                    MctNumericFormat::Float32,
                                    MctNumericFormat::Float64,
                                ][variant / 3 % 4],
                                fraction_bits: [0, 1, u8::MAX][variant % 3],
                                values: [i64::MIN, 0, i64::MAX, -1][..(slot + variant) % 5]
                                    .to_vec(),
                            })
                            .collect(),
                        records: (0..records)
                            .map(|slot| {
                                record(
                                    if slot == 0 { u8::MAX } else { 0 },
                                    [0, 1, 3][slot % 3],
                                    variant,
                                )
                            })
                            .collect(),
                        order: [u8::MAX, 0, u8::MAX, 1][..order].to_vec(),
                    };
                    let before = format!("{original:?}");
                    let mut copied = original.clone();
                    assert_eq!(copied, original);
                    separate(&original.arrays, &copied.arrays);
                    separate(&original.records, &copied.records);
                    separate(&original.order, &copied.order);
                    for (left, right) in original.arrays.iter().zip(&copied.arrays) {
                        separate(&left.values, &right.values);
                    }
                    for (left, right) in original.records.iter().zip(&copied.records) {
                        separate_record(left, right);
                    }
                    for array in &mut copied.arrays {
                        array.index ^= 0xff;
                        array.values.push(17);
                    }
                    for record in &mut copied.records {
                        for collection in &mut record.collections {
                            collection.input_components.push(31);
                            collection.output_components.push(37);
                        }
                        record.collections.push(reference(41, 3, 4));
                    }
                    copied.order.push(19);
                    assert_eq!(format!("{original:?}"), before);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 972);
}

#[test]
fn actual_layout_mct_clones_retain_main_and_persistent_unused_arrays() {
    let [cod, qcd] = baseline_headers();
    let bytes = codestream_with_headers(
        1,
        &[
            cod,
            qcd,
            mct_i16(1, 1, &[1, 4]),
            mct_i16(200, 1, &[1, 8]),
            mcc(7, 1, true, 1, 0),
            mco(&[7]),
        ],
        &[],
        &[],
    );
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(
        layout
            .info
            .multiple_component_transform
            .as_ref()
            .unwrap()
            .stages()[0]
            .collections()[0]
            .matrix()
            .unwrap()
            .values(),
        &[1, 4],
    );
    assert_eq!(
        layout.tile_parts[0]
            .multiple_component_transform
            .as_ref()
            .unwrap()
            .stages()[0]
            .collections()[0]
            .matrix()
            .unwrap()
            .values(),
        &[1, 4],
    );
    let first = [
        mct_i16(1, 1, &[1, 4]),
        mct_i16(200, 1, &[1, 8]),
        mcc(7, 1, true, 1, 0),
        mco(&[7]),
    ];
    let second = [mcc(8, 1, true, 200, 0), mco(&[8])];
    let bytes = two_part_codestream(&first, &second);
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(layout.tile_parts.len(), 2);
    for (index, expected) in [(0, 4), (1, 8)] {
        let transform = layout.tile_parts[index]
            .multiple_component_transform
            .as_ref()
            .unwrap();
        assert_eq!(
            transform.stages()[0].collections()[0]
                .matrix()
                .unwrap()
                .values(),
            &[1, expected]
        );
    }
}
