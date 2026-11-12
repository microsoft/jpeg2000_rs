use super::*;

#[test]
fn native_mct_wavelet_partitions_match_signed_integer_intervals() {
    for value in [
        i64::MIN,
        i64::MIN + 1,
        -257,
        -3,
        -2,
        -1,
        0,
        1,
        2,
        3,
        257,
        i64::MAX - 1,
        i64::MAX,
    ] {
        assert_eq!(
            ceil_divide_by_two(value),
            Ok(((i128::from(value) + 1).div_euclid(2)) as i64)
        );
    }
    for transform in [
        MctWaveletType::Reversible5x3,
        MctWaveletType::Irreversible9x7,
    ] {
        for offset in [i32::MIN, -33, -2, -1, 0, 1, 2, 33, i32::MAX] {
            for levels in [0, 1, 2, 3, 8, 31, u8::MAX] {
                let collection =
                    MctCollection::from_wavelet(vec![], vec![], transform, levels, offset);
                let wavelet = collection.wavelet().unwrap();
                for count in [0, 1, 2, 3, 4, 7, 11, 65535, i64::MAX as usize, usize::MAX] {
                    let expected = (|| -> Result<(Vec<bool>, Vec<usize>, usize), DecodeError> {
                        let overflow = DecodeError::MalformedInput {
                            offset: 0,
                            kind: MalformedKind::ArithmeticOverflow,
                        };
                        if count as u128 > i64::MAX as u128 {
                            return Err(overflow);
                        }
                        let mut start = i128::from(offset);
                        let mut end = start + count as i128;
                        if end > i128::from(i64::MAX) {
                            return Err(overflow);
                        }
                        let mut first = Vec::new();
                        let mut high = Vec::new();
                        for _ in 0..levels {
                            let next_start = (start + 1).div_euclid(2);
                            let next_end = (end + 1).div_euclid(2);
                            first.push(start.rem_euclid(2) == 0);
                            high.push(
                                usize::try_from(end - start - (next_end - next_start)).unwrap(),
                            );
                            start = next_start;
                            end = next_end;
                        }
                        Ok((first, high, usize::try_from(end - start).unwrap()))
                    })();
                    assert_eq!(prepare_mct_wavelet_partition(count, wavelet), expected);
                }
            }
        }
    }
}

#[test]
fn native_mct_wavelet_scaled_snapshot_keeps_full_precision_and_error_priority() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    for reversible in [false, true] {
        for bits in 0..=u8::MAX {
            for value in [i64::MIN, -7, 0, 7, i64::MAX] {
                let expected = if reversible {
                    Ok(value)
                } else if bits <= 32 {
                    i64::try_from(i128::from(value) * (1_i128 << (32 - bits))).map_err(|_| overflow)
                } else if bits - 32 > 126 {
                    Err(overflow)
                } else {
                    let shift = bits - 32;
                    let rounded =
                        (i128::from(value).abs() + (1_i128 << (shift - 1))) / (1_i128 << shift);
                    Ok(if value < 0 {
                        -rounded as i64
                    } else {
                        rounded as i64
                    })
                };
                let mut samples = [value];
                let mut precision = u8::MAX;
                let components = [TransformComponentMut {
                    component: 0,
                    x: 0,
                    y: 0,
                    width: 0,
                    height: 0,
                    x_subsampling: 0,
                    y_subsampling: 0,
                    fraction_bits: &mut precision,
                    samples: &mut samples,
                }];
                let mut source = vec![123];
                let result = begin_mct_wavelet_pixel(
                    &mut source,
                    &components,
                    &[0, 2],
                    &[bits],
                    0,
                    2,
                    reversible,
                );
                assert_eq!(
                    result,
                    match expected {
                        Err(error) => Err(error),
                        Ok(_) => Err(invalid),
                    }
                );
                assert_eq!(
                    source,
                    match expected {
                        Ok(value) => vec![value],
                        Err(_) => vec![],
                    }
                );
                let mut source = vec![123];
                assert_eq!(
                    begin_mct_wavelet_pixel(&mut source, &components, &[2], &[], 0, 0, reversible),
                    Ok(())
                );
                assert!(source.is_empty());
            }
        }
    }
}

#[test]
fn native_mct_wavelet_reversible_collection_matches_independent_synthesis() {
    fn inverse(low: &[i64], high: &[i64], first: bool) -> Vec<i64> {
        let mut values = Vec::new();
        for index in 0..low.len() + high.len() {
            values.push(if (index % 2 == 0) == first {
                low[index / 2]
            } else {
                high[index / 2]
            });
        }
        if values.len() == 1 && !first {
            values[0] = values[0].div_euclid(2);
            return values;
        }
        if values.len() < 2 {
            return values;
        }
        for index in 0..values.len() {
            if (index % 2 == 0) == first {
                let left = values[if index == 0 { 1 } else { index - 1 }];
                let right = values[if index + 1 == values.len() {
                    index - 1
                } else {
                    index + 1
                }];
                values[index] -= (left + right + 2).div_euclid(4);
            }
        }
        for index in 0..values.len() {
            if (index % 2 == 0) != first {
                let left = values[if index == 0 { 1 } else { index - 1 }];
                let right = values[if index + 1 == values.len() {
                    index - 1
                } else {
                    index + 1
                }];
                values[index] += (left + right).div_euclid(2);
            }
        }
        values
    }
    for count in 1..=6 {
        for offset in -3_i32..=3 {
            for levels in 0..=4 {
                let original = [-2, 3, 0, 7, -5, 2][..count].to_vec();
                let mut start = i64::from(offset);
                let mut end = start + count as i64;
                let mut partitions = Vec::new();
                for _ in 0..levels {
                    let next_start = (start + 1).div_euclid(2);
                    let next_end = (end + 1).div_euclid(2);
                    partitions.push((
                        start.rem_euclid(2) == 0,
                        (end - start - (next_end - next_start)) as usize,
                    ));
                    start = next_start;
                    end = next_end;
                }
                let mut cursor = (end - start) as usize;
                let mut expected = original[..cursor].to_vec();
                for &(first, length) in partitions.iter().rev() {
                    expected = inverse(&expected, &original[cursor..cursor + length], first);
                    cursor += length;
                }
                assert_eq!(cursor, count);
                let mut samples: Vec<_> = original.iter().map(|&value| vec![value]).collect();
                let mut fractions = vec![0; count];
                let mut components: Vec<_> = samples
                    .iter_mut()
                    .zip(fractions.iter_mut())
                    .enumerate()
                    .map(
                        |(component, (samples, fraction_bits))| TransformComponentMut {
                            component: component as u16,
                            x: 0,
                            y: 0,
                            width: 1,
                            height: 1,
                            x_subsampling: 1,
                            y_subsampling: 1,
                            fraction_bits,
                            samples,
                        },
                    )
                    .collect();
                let references: Vec<_> = (0..count).map(|index| index as u16).collect();
                let collection = MctCollection::from_wavelet(
                    references.clone(),
                    references,
                    MctWaveletType::Reversible5x3,
                    levels,
                    offset,
                );
                let mut work = 7;
                assert_eq!(
                    apply_mct_wavelet(
                        &mut components,
                        &collection,
                        &ResourceLimits::default(),
                        &mut work
                    ),
                    Ok(())
                );
                assert_eq!(work, 7 + count as u64 * (u64::from(levels) + 1) * 8);
                drop(components);
                assert_eq!(
                    samples.iter().map(|value| value[0]).collect::<Vec<_>>(),
                    expected
                );
                assert_eq!(fractions, vec![0; count]);
            }
        }
    }
}

#[test]
fn native_mct_dependency_counts_and_admission_match_wide_thresholds() {
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let square_root = usize::MAX.isqrt();
    let counts = [
        0,
        1,
        2,
        3,
        7,
        square_root.saturating_sub(1),
        square_root,
        square_root.saturating_add(1),
        usize::MAX / 2,
        usize::MAX - 1,
        usize::MAX,
    ];
    for reversible in [false, true] {
        for count in counts {
            let n = count as u128;
            let following = if reversible {
                n + 1
            } else {
                n.saturating_sub(1)
            };
            let product = n * following;
            let expected = if (reversible && (following > usize::MAX as u128 || product / 2 == 0))
                || product > usize::MAX as u128
            {
                Err(overflow)
            } else {
                Ok((product / 2 - u128::from(reversible)) as usize)
            };
            assert_eq!(
                mct_dependency_coefficient_count(count, reversible),
                expected
            );
        }
    }
    for count in [0, 1, 2, 7, usize::MAX / 3, usize::MAX] {
        for coefficients in [0, 1, 2, usize::MAX / 2, usize::MAX] {
            for samples in [0, 1, 2, usize::MAX] {
                for before in [0, 7, u64::MAX - 1, u64::MAX] {
                    for maximum_work in [1, 16, ResourceLimits::HARDENED.maximum_work_units()] {
                        for maximum_bytes in
                            [1, 48, ResourceLimits::HARDENED.maximum_decoded_bytes()]
                        {
                            let expected = (|| -> (Result<(), DecodeError>, u64) {
                                let twice = u128::from(coefficients as u64) * 2;
                                let per_sample = twice + u128::from(count as u64);
                                if twice > u128::from(u64::MAX) || per_sample > u128::from(u64::MAX)
                                {
                                    return (Err(overflow), before);
                                }
                                let operations = u128::from(samples as u64) * per_sample;
                                if operations > u128::from(u64::MAX)
                                    || u128::from(before) + operations > u128::from(u64::MAX)
                                {
                                    return (Err(overflow), before);
                                }
                                let charged = (u128::from(before) + operations) as u64;
                                if charged > maximum_work {
                                    return (
                                        Err(DecodeError::LimitExceeded {
                                            resource: Resource::WorkUnits,
                                            limit: maximum_work,
                                            actual: charged,
                                        }),
                                        charged,
                                    );
                                }
                                let scratch = (count as u128 * 3).min(usize::MAX as u128) as u64;
                                let bytes = u128::from(scratch) * 8;
                                if bytes > u128::from(u64::MAX) {
                                    return (Err(overflow), charged);
                                }
                                if bytes > u128::from(maximum_bytes) {
                                    return (
                                        Err(DecodeError::LimitExceeded {
                                            resource: Resource::DecodedBytes,
                                            limit: maximum_bytes,
                                            actual: bytes as u64,
                                        }),
                                        charged,
                                    );
                                }
                                (Ok(()), charged)
                            })();
                            let limits = ResourceLimits::default()
                                .with_maximum_work_units(maximum_work)
                                .unwrap()
                                .with_maximum_decoded_bytes(maximum_bytes)
                                .unwrap();
                            let mut work = before;
                            let result = admit_mct_dependency(
                                samples,
                                coefficients,
                                count,
                                &limits,
                                &mut work,
                            );
                            assert_eq!((result, work), expected);
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn native_mct_dependency_preparation_checks_destination_precision_and_exact_caps() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    for reversible in [false, true] {
        for precision in 0..=u8::MAX {
            let mut samples = [vec![3], vec![7]];
            let mut fractions = [0, precision];
            let components: Vec<_> = samples
                .iter_mut()
                .zip(fractions.iter_mut())
                .zip([0, 1])
                .map(
                    |((samples, fraction_bits), component)| TransformComponentMut {
                        component,
                        x: 0,
                        y: 0,
                        width: 0,
                        height: 0,
                        x_subsampling: 0,
                        y_subsampling: 0,
                        fraction_bits,
                        samples,
                    },
                )
                .collect();
            let collection = MctCollection::from_wavelet(
                vec![0],
                vec![1],
                if reversible {
                    MctWaveletType::Reversible5x3
                } else {
                    MctWaveletType::Irreversible9x7
                },
                u8::MAX,
                i32::MIN,
            );
            for maximum_work in [7, 8, 9] {
                for maximum_bytes in [23, 24, 25] {
                    let expected_error = if precision > 32 || (reversible && precision != 0) {
                        Some(invalid)
                    } else if maximum_work < 8 {
                        Some(DecodeError::LimitExceeded {
                            resource: Resource::WorkUnits,
                            limit: maximum_work,
                            actual: 8,
                        })
                    } else if maximum_bytes < 24 {
                        Some(DecodeError::LimitExceeded {
                            resource: Resource::DecodedBytes,
                            limit: maximum_bytes,
                            actual: 24,
                        })
                    } else {
                        None
                    };
                    let limits = ResourceLimits::default()
                        .with_maximum_work_units(maximum_work)
                        .unwrap()
                        .with_maximum_decoded_bytes(maximum_bytes)
                        .unwrap();
                    let mut work = 7;
                    let result =
                        prepare_mct_dependency(&components, &collection, &limits, &mut work);
                    assert_eq!(result.as_ref().err().copied(), expected_error);
                    assert_eq!(
                        work,
                        if precision > 32 || (reversible && precision != 0) {
                            7
                        } else {
                            8
                        }
                    );
                    if let Ok(prepared) = result {
                        assert_eq!(prepared.source_indexes, [0]);
                        assert_eq!(prepared.destination_indexes, [1]);
                        assert_eq!((prepared.sample_count, prepared.count), (1, 1));
                    }
                }
            }
            drop(components);
            assert_eq!(samples, [vec![3], vec![7]]);
            assert_eq!(fractions, [0, precision]);
        }
    }
}

#[test]
fn native_mct_dependency_collection_matches_floor_and_q32_composition() {
    use crate::codestream::{MctArrayKind, MctNumericFormat};
    for reversible in [false, true] {
        for coefficient in [-2_i64, 0, 3] {
            for scale in [1_i64, 2, 3, 7] {
                for first in [-3_i64, 0, 4] {
                    for second in [-5_i64, 1, 7] {
                        let mut samples = [vec![first, second], vec![second, first], vec![123]];
                        let mut expected = samples.clone();
                        for index in 0..2 {
                            let base = i128::from(samples[1][index]);
                            let previous = i128::from(samples[0][index]);
                            let value = if reversible {
                                base + (i128::from(scale / 2) + i128::from(coefficient) * previous)
                                    .div_euclid(i128::from(scale))
                            } else {
                                (base + i128::from(coefficient) * previous) * (1_i128 << 32)
                            };
                            expected[0][index] = if reversible {
                                samples[0][index]
                            } else {
                                samples[0][index] * (1_i64 << 32)
                            };
                            expected[1][index] = i64::try_from(value).unwrap();
                        }
                        let mut fractions = [0, 0, u8::MAX];
                        let mut components: Vec<_> = samples
                            .iter_mut()
                            .zip(fractions.iter_mut())
                            .zip([0, 1, 99])
                            .map(|((samples, fraction_bits), component)| {
                                // Keep each mutable sample/precision pair in the same component.
                                TransformComponentMut {
                                    component,
                                    x: 0,
                                    y: 0,
                                    width: 2,
                                    height: 1,
                                    x_subsampling: 1,
                                    y_subsampling: 1,
                                    fraction_bits,
                                    samples,
                                }
                            })
                            .collect();
                        let values = if reversible {
                            vec![coefficient, scale]
                        } else {
                            vec![coefficient]
                        };
                        let collection = MctCollection::from_dependency(
                            reversible,
                            vec![0, 1],
                            Some(MctArray::from_values(
                                u8::MAX,
                                MctArrayKind::Offset,
                                MctNumericFormat::Float64,
                                0,
                                values,
                            )),
                            None,
                        );
                        let mut work = 5;
                        assert_eq!(
                            apply_mct_dependency(
                                &mut components,
                                &collection,
                                &ResourceLimits::default(),
                                &mut work
                            ),
                            Ok(())
                        );
                        assert_eq!(work, if reversible { 17 } else { 13 });
                        drop(components);
                        assert_eq!(samples, expected);
                        assert_eq!(
                            fractions,
                            if reversible {
                                [0, 0, u8::MAX]
                            } else {
                                [32, 32, u8::MAX]
                            }
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn native_mct_dependency_pixel_uses_exact_count_and_preserves_duplicate_store_errors() {
    let indexes: &[&[usize]] = &[
        &[],
        &[0],
        &[1],
        &[0, 0],
        &[0, 1],
        &[1, 0],
        &[0, 2],
        &[2, 0],
        &[2],
    ];
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let collection = MctCollection::from_dependency(true, vec![u16::MAX], None, None);
    for source_indexes in indexes {
        for destinations in indexes {
            for count in 0..=3 {
                for sample in 0..=2 {
                    let mut samples = [vec![3, 5], vec![7]];
                    let mut expected_samples = samples.clone();
                    let mut expected_source = Vec::new();
                    let mut expected_output = Vec::new();
                    let expected = (|| -> Result<(), DecodeError> {
                        for position in 0..count {
                            let component = *source_indexes.get(position).ok_or(invalid)?;
                            expected_source.push(
                                *samples
                                    .get(component)
                                    .ok_or(invalid)?
                                    .get(sample)
                                    .ok_or(invalid)?,
                            );
                        }
                        expected_output.extend_from_slice(&expected_source);
                        for (row, &value) in expected_output.iter().enumerate() {
                            let destination = *destinations.get(row).ok_or(invalid)?;
                            *expected_samples
                                .get_mut(destination)
                                .ok_or(invalid)?
                                .get_mut(sample)
                                .ok_or(invalid)? = value;
                        }
                        Ok(())
                    })();
                    let mut fractions = [u8::MAX, 1];
                    let mut components: Vec<_> = samples
                        .iter_mut()
                        .zip(fractions.iter_mut())
                        .zip([0, 1])
                        .map(
                            |((samples, fraction_bits), component)| TransformComponentMut {
                                component,
                                x: 0,
                                y: 0,
                                width: 0,
                                height: 0,
                                x_subsampling: 0,
                                y_subsampling: 0,
                                fraction_bits,
                                samples,
                            },
                        )
                        .collect();
                    let prepared = MctDependencyPreparation {
                        source_indexes: source_indexes.to_vec(),
                        destination_indexes: destinations.to_vec(),
                        sample_count: usize::MAX,
                        count,
                    };
                    let mut source = vec![-9];
                    let mut output = vec![42];
                    assert_eq!(
                        apply_mct_dependency_pixel(
                            &mut components,
                            &collection,
                            &prepared,
                            &[u8::MAX],
                            sample,
                            &mut source,
                            &mut output,
                        ),
                        expected
                    );
                    assert_eq!(source, expected_source);
                    assert_eq!(output, expected_output);
                    drop(components);
                    assert_eq!(samples, expected_samples);
                    assert_eq!(fractions, [u8::MAX, 1]);
                }
            }
        }
    }
}

#[test]
fn native_mct_pixel_transition_preserves_raw_snapshot_and_store_error_frontiers() {
    let indexes: &[&[usize]] = &[
        &[],
        &[0],
        &[1],
        &[0, 0],
        &[0, 1],
        &[1, 0],
        &[0, 2],
        &[2, 0],
        &[2],
    ];
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let collection = MctCollection::from_dependency(true, vec![u16::MAX], None, None);
    for source_indexes in indexes {
        for destinations in indexes {
            for rows in 0..=3 {
                for sample in 0..=2 {
                    let mut samples = [vec![3, 5], vec![7]];
                    let mut expected_samples = samples.clone();
                    let mut expected_source = Vec::new();
                    let mut expected_output = Vec::new();
                    let expected = (|| -> Result<(), DecodeError> {
                        for &index in source_indexes.iter() {
                            expected_source.push(
                                *samples
                                    .get(index)
                                    .ok_or(invalid)?
                                    .get(sample)
                                    .ok_or(invalid)?,
                            );
                        }
                        for row in 0..rows {
                            expected_output.push(*expected_source.get(row).ok_or(invalid)?);
                        }
                        for (row, &value) in expected_output.iter().enumerate() {
                            let destination = *destinations.get(row).ok_or(invalid)?;
                            *expected_samples
                                .get_mut(destination)
                                .ok_or(invalid)?
                                .get_mut(sample)
                                .ok_or(invalid)? = value;
                        }
                        Ok(())
                    })();
                    let mut fractions = [u8::MAX, 1];
                    let mut components: Vec<_> = samples
                        .iter_mut()
                        .zip(fractions.iter_mut())
                        .zip([0, 1])
                        .map(
                            |((samples, fraction_bits), component)| TransformComponentMut {
                                component,
                                x: component as u32,
                                y: u32::MAX,
                                width: 0,
                                height: 7,
                                x_subsampling: 0,
                                y_subsampling: u8::MAX,
                                fraction_bits,
                                samples,
                            },
                        )
                        .collect();
                    let metadata: Vec<_> = components
                        .iter()
                        .map(|component| {
                            (
                                component.component,
                                component.x,
                                component.y,
                                component.width,
                                component.height,
                                component.x_subsampling,
                                component.y_subsampling,
                            )
                        })
                        .collect();
                    let prepared = MctDecorrelationPreparation {
                        source_indexes: source_indexes.to_vec(),
                        destination_indexes: destinations.to_vec(),
                        source_fraction_bits: vec![u8::MAX; source_indexes.len()],
                        sample_count: usize::MAX,
                        rows,
                        columns: 0,
                    };
                    let mut source = vec![-9, 123];
                    let mut output = vec![42, -7];
                    assert_eq!(
                        apply_mct_decorrelation_pixel(
                            &mut components,
                            &collection,
                            &prepared,
                            sample,
                            &mut source,
                            &mut output,
                        ),
                        expected
                    );
                    assert_eq!(source, expected_source);
                    assert_eq!(output, expected_output);
                    assert_eq!(
                        components
                            .iter()
                            .map(|component| (
                                component.component,
                                component.x,
                                component.y,
                                component.width,
                                component.height,
                                component.x_subsampling,
                                component.y_subsampling
                            ))
                            .collect::<Vec<_>>(),
                        metadata
                    );
                    drop(components);
                    assert_eq!(samples, expected_samples);
                    assert_eq!(fractions, [u8::MAX, 1]);
                }
            }
        }
    }
}

#[test]
fn native_mct_destination_precision_preserves_all_tags_and_partial_error_order() {
    for precision in 0..=u8::MAX {
        for destinations in [
            &[][..],
            &[0][..],
            &[1][..],
            &[0, 0][..],
            &[1, 0][..],
            &[0, 2][..],
            &[2, 0][..],
        ] {
            let mut expected = [1, u8::MAX];
            let expected_result = (|| -> Result<(), DecodeError> {
                for &destination in destinations {
                    let tag = expected
                        .get_mut(destination)
                        .ok_or(DecodeError::MalformedInput {
                            offset: 0,
                            kind: MalformedKind::InvalidTransform,
                        })?;
                    *tag = precision;
                }
                Ok(())
            })();
            let mut samples = [vec![3, 5], vec![7]];
            let original = samples.clone();
            let mut fractions = [1, u8::MAX];
            let mut components: Vec<_> = samples
                .iter_mut()
                .zip(fractions.iter_mut())
                .zip([0, 1])
                .map(
                    |((samples, fraction_bits), component)| TransformComponentMut {
                        component,
                        x: 0,
                        y: 0,
                        width: 0,
                        height: 0,
                        x_subsampling: 0,
                        y_subsampling: 0,
                        fraction_bits,
                        samples,
                    },
                )
                .collect();
            assert_eq!(
                apply_mct_destination_precisions(&mut components, destinations, precision),
                expected_result
            );
            drop(components);
            assert_eq!(fractions, expected);
            assert_eq!(samples, original);
        }
    }
}

#[test]
fn native_mct_decorrelation_rows_preserve_lazy_precision_domains_and_partial_output() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    for reversible in [false, true] {
        let collection = MctCollection::from_dependency(reversible, vec![u16::MAX], None, None);
        for bits in 0..=u8::MAX {
            for sample in [i64::MIN, -7, 0, 7, i64::MAX] {
                let expected = if reversible {
                    Ok(sample)
                } else if bits <= 32 {
                    i64::try_from(i128::from(sample) * (1_i128 << (32 - bits)))
                        .map_err(|_| overflow)
                } else if bits - 32 > 126 {
                    Err(overflow)
                } else {
                    let magnitude = i128::from(sample).abs();
                    let shift = bits - 32;
                    let rounded = (magnitude + (1_i128 << (shift - 1))) / (1_i128 << shift);
                    Ok(if sample < 0 {
                        -rounded as i64
                    } else {
                        rounded as i64
                    })
                };
                assert_eq!(
                    decorrelation_mct_row(&collection, &[sample], &[bits], 0),
                    expected
                );
                for rows in 0..=2 {
                    let mut output = vec![42, -99];
                    let result = append_mct_decorrelation_rows(
                        &mut output,
                        &collection,
                        &[sample],
                        &[bits],
                        rows,
                    );
                    let expected_result = if rows == 0 {
                        Ok(())
                    } else {
                        match expected {
                            Err(error) => Err(error),
                            Ok(value) => {
                                assert_eq!(output, [42, -99, value]);
                                if rows == 1 { Ok(()) } else { Err(invalid) }
                            }
                        }
                    };
                    assert_eq!(result, expected_result);
                    if rows == 0 || expected.is_err() {
                        assert_eq!(output, [42, -99]);
                    }
                }
            }
        }
        assert_eq!(
            decorrelation_mct_row(&collection, &[], &[], 0),
            Err(invalid)
        );
        assert_eq!(
            decorrelation_mct_row(&collection, &[1], &[], 0),
            if reversible { Ok(1) } else { Err(invalid) }
        );
    }
}

#[test]
fn native_mct_decorrelation_dispatch_preserves_partial_matrix_rows() {
    use crate::codestream::{MctArrayKind, MctNumericFormat};
    for reversible in [false, true] {
        let array = |values| {
            MctArray::from_values(
                u8::MAX,
                MctArrayKind::Offset,
                MctNumericFormat::Float64,
                0,
                values,
            )
        };
        let collection = MctCollection::from_arrays(
            reversible,
            vec![0, 1],
            vec![0, 1],
            array(if reversible {
                vec![3, 2, 4, -1, 5, 8]
            } else {
                vec![2, 3, 4, 5]
            }),
            Some(array(vec![1, -1])),
        );
        let scale = if reversible { 1 } else { 1_i64 << 32 };
        let mut output = vec![123];
        assert_eq!(
            append_mct_decorrelation_rows(&mut output, &collection, &[7, -2], &[0, 0], 3),
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidTransform,
            })
        );
        assert_eq!(
            output,
            if reversible {
                [123, 5, -17]
            } else {
                [123, 9 * scale, 17 * scale]
            }
        );
    }
}

fn t801_reversible_decorrelation_array(values: Vec<i64>) -> crate::codestream::MctArray {
    crate::codestream::MctArray::from_values(
        7,
        crate::codestream::MctArrayKind::Decorrelation,
        crate::codestream::MctNumericFormat::Int16,
        0,
        values,
    )
}

#[test]
fn t801_reversible_mct_stages_keep_order_signed_ties_and_post_transform_offsets() {
    let matrix = t801_reversible_decorrelation_array(vec![3, 2, 4, -1, 5, -8]);
    assert_eq!(
        super::mct::inverse_reversible_mct(&matrix, &[7, -2]),
        Ok(vec![4, 16])
    );
    let offsets = t801_reversible_decorrelation_array(vec![10, -20]);
    let collection =
        MctCollection::from_arrays(true, vec![0, 1], vec![0, 1], matrix, Some(offsets));
    let mut output = vec![42];
    append_mct_decorrelation_rows(&mut output, &collection, &[7, -2], &[0, 0], 2).unwrap();
    assert_eq!(output, [42, 14, -4]);
    let ties = t801_reversible_decorrelation_array(vec![-1, 2, 1, 0, 0, 1]);
    assert_eq!(
        super::mct::inverse_reversible_mct(&ties, &[1, 0]),
        Ok(vec![1, 0])
    );
    assert_eq!(
        super::mct::inverse_reversible_mct(&ties, &[-1, 0]),
        Ok(vec![-1, -1])
    );
    for (final_scale, sign) in [(1, 1), (2, 1), (-1, -1), (i64::MIN, -1)] {
        let single = t801_reversible_decorrelation_array(vec![4, final_scale]);
        assert_eq!(
            super::mct::inverse_reversible_mct(&single, &[17]),
            Ok(vec![sign * 17])
        );
    }
}

#[test]
fn t801_reversible_mct_matches_independently_reversed_integer_lifting() {
    fn encode(original: &[i64], coefficients: &[i64], offsets: &[i64]) -> Vec<i64> {
        let n = original.len();
        let mut values: Vec<i64> = original
            .iter()
            .zip(offsets)
            .map(|(&sample, &offset)| sample - offset)
            .collect();
        for stage in (0..=n).rev() {
            let target = if stage == n { n - 1 } else { n - 1 - stage };
            let row = &coefficients[stage * n..(stage + 1) * n];
            let divisor = i128::from(row[target].unsigned_abs());
            let dot: i128 = row
                .iter()
                .zip(&values)
                .enumerate()
                .filter(|(index, _)| *index != target)
                .map(|(_, (&coefficient, &sample))| i128::from(coefficient) * i128::from(sample))
                .sum();
            let prediction = (2 * dot + divisor).div_euclid(2 * divisor);
            let signed_sample = if row[target] < 0 {
                -i128::from(values[target])
            } else {
                i128::from(values[target])
            };
            values[target] = i64::try_from(signed_sample + prediction).unwrap();
        }
        values
    }
    let mut seed = 0x49c7_bafd_u32;
    for n in 1..=8 {
        for case in 0..64 {
            let mut coefficients = Vec::new();
            for _ in 0..n * (n + 1) {
                seed = seed.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
                coefficients.push(i64::from(seed % 3) - 1);
            }
            for stage in 0..=n {
                let target = if stage == n { n - 1 } else { n - 1 - stage };
                coefficients[stage * n + target] =
                    (1_i64 << (stage % 4)) * if stage == n && case % 2 == 0 { -1 } else { 1 };
            }
            let original: Vec<i64> = (0..n)
                .map(|index| i64::try_from((index * 3 + case) % 31).unwrap() - 15)
                .collect();
            let offsets: Vec<i64> = (0..n)
                .map(|index| i64::try_from((index + case) % 11).unwrap() - 5)
                .collect();
            let encoded = encode(&original, &coefficients, &offsets);
            let matrix = t801_reversible_decorrelation_array(coefficients);
            let offsets = t801_reversible_decorrelation_array(offsets);
            let collection = MctCollection::from_arrays(
                true,
                (0..n).map(|index| u16::try_from(index).unwrap()).collect(),
                (0..n).map(|index| u16::try_from(index).unwrap()).collect(),
                matrix,
                Some(offsets),
            );
            let mut actual = Vec::new();
            append_mct_decorrelation_rows(&mut actual, &collection, &encoded, &[], n).unwrap();
            assert_eq!(actual, original, "N={n}, case={case}");
        }
    }
    let n = 63;
    let mut identity = vec![0; n * (n + 1)];
    for stage in 0..=n {
        let target = if stage == n { n - 1 } else { n - 1 - stage };
        identity[stage * n + target] = 1;
    }
    let source: Vec<i64> = (0..n)
        .map(|index| i64::try_from(index).unwrap() - 31)
        .collect();
    assert_eq!(
        super::mct::inverse_reversible_mct(&t801_reversible_decorrelation_array(identity), &source),
        Ok(source)
    );
}

#[test]
fn t801_reversible_mct_rejects_bad_scales_and_reports_integer_overflow() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    for (values, source) in [
        (vec![1], vec![7]),
        (vec![0, 1], vec![7]),
        (vec![-2, 1], vec![7]),
        (vec![3, 1], vec![7]),
        (vec![1, 0], vec![7]),
        (vec![1, -3], vec![7]),
        (vec![], vec![]),
    ] {
        assert_eq!(
            super::mct::inverse_reversible_mct(
                &t801_reversible_decorrelation_array(values),
                &source
            ),
            Err(invalid)
        );
    }
    let negative = t801_reversible_decorrelation_array(vec![1, -1]);
    assert_eq!(
        super::mct::inverse_reversible_mct(&negative, &[i64::MIN]),
        Err(overflow)
    );
    let mut coefficients = vec![0; 20];
    for (stage, target) in [(0, 3), (1, 2), (2, 1), (3, 0), (4, 3)] {
        coefficients[stage * 4 + target] = 1;
    }
    coefficients[..3].fill(i64::MAX);
    let source = [i64::MAX; 4];
    let matrix = t801_reversible_decorrelation_array(coefficients);
    assert_eq!(
        super::mct::inverse_reversible_mct(&matrix, &source),
        Err(overflow)
    );
    assert_eq!(source, [i64::MAX; 4]);
    let offsets = t801_reversible_decorrelation_array(vec![1]);
    assert_eq!(
        reversible_mct_row(
            &t801_reversible_decorrelation_array(vec![1, 1]),
            Some(&offsets),
            &[i64::MAX],
            0
        ),
        Err(overflow)
    );
}

#[test]
fn native_mct_decorrelation_keeps_pixel_transactions_and_duplicate_destinations() {
    use crate::codestream::{MctArrayKind, MctNumericFormat};
    for duplicates in [false, true] {
        let mut samples = [vec![1, 2], vec![3, if duplicates { 4 } else { i64::MAX }]];
        let mut fractions = [0, 0];
        let mut components: Vec<_> = samples
            .iter_mut()
            .zip(fractions.iter_mut())
            .zip([0, 1])
            .map(
                |((samples, fraction_bits), component)| TransformComponentMut {
                    component,
                    x: 7,
                    y: 9,
                    width: 2,
                    height: 1,
                    x_subsampling: 1,
                    y_subsampling: 1,
                    fraction_bits,
                    samples,
                },
            )
            .collect();
        let collection = MctCollection::from_arrays(
            false,
            vec![0, if duplicates { 0 } else { 1 }],
            vec![0, 1],
            MctArray::from_values(
                0,
                MctArrayKind::Offset,
                MctNumericFormat::Float64,
                0,
                vec![1, 0, 0, 1],
            ),
            None,
        );
        let mut work = 5;
        assert_eq!(
            apply_mct_decorrelation(
                &mut components,
                &collection,
                &ResourceLimits::default(),
                &mut work,
            ),
            if duplicates {
                Ok(())
            } else {
                Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::ArithmeticOverflow,
                })
            }
        );
        assert_eq!(work, 17);
        drop(components);
        if duplicates {
            assert_eq!(samples, [vec![3_i64 << 32, 4_i64 << 32], vec![3, 4]]);
            assert_eq!(fractions, [32, 0]);
        } else {
            assert_eq!(samples, [vec![1_i64 << 32, 2], vec![3_i64 << 32, i64::MAX]]);
            assert_eq!(fractions, [0, 0]);
        }
    }
}

#[test]
fn native_mct_preparation_derives_real_ordered_indexes_fractions_and_late_work_errors() {
    use crate::codestream::{MctArrayKind, MctNumericFormat};
    let matrix = || {
        MctArray::from_values(
            u8::MAX,
            MctArrayKind::Offset,
            MctNumericFormat::Float64,
            u8::MAX,
            vec![0, 1, 1, 0, 0, 1],
        )
    };
    let collection = MctCollection::from_arrays(true, vec![17, 0], vec![0, 17], matrix(), None);
    let mut samples = [vec![1, 2], vec![3, 4]];
    let before_samples = samples.clone();
    let mut fractions = [0, 0];
    let components: Vec<_> = samples
        .iter_mut()
        .zip(fractions.iter_mut())
        .zip([0, 17])
        .map(
            |((samples, fraction_bits), component)| TransformComponentMut {
                component,
                x: u32::MAX,
                y: 0,
                width: 0,
                height: u32::MAX,
                x_subsampling: 0,
                y_subsampling: u8::MAX,
                fraction_bits,
                samples,
            },
        )
        .collect();
    let mut work = 7;
    let prepared = prepare_mct_decorrelation(
        &components,
        &collection,
        &ResourceLimits::default(),
        &mut work,
    )
    .unwrap();
    assert_eq!(prepared.source_indexes, [0, 1]);
    assert_eq!(prepared.destination_indexes, [1, 0]);
    assert_eq!(prepared.source_fraction_bits, [0, 0]);
    assert_eq!(
        (prepared.sample_count, prepared.rows, prepared.columns, work),
        (2, 2, 2, 23)
    );
    for maximum_work in [22, 23, 24] {
        for maximum_bytes in [47, 48, 49] {
            let limits = ResourceLimits::default()
                .with_maximum_work_units(maximum_work)
                .unwrap()
                .with_maximum_decoded_bytes(maximum_bytes)
                .unwrap();
            let expected_error = if maximum_work < 23 {
                Some(DecodeError::LimitExceeded {
                    resource: Resource::WorkUnits,
                    limit: maximum_work,
                    actual: 23,
                })
            } else if maximum_bytes < 48 {
                Some(DecodeError::LimitExceeded {
                    resource: Resource::DecodedBytes,
                    limit: maximum_bytes,
                    actual: 48,
                })
            } else {
                None
            };
            let mut work = 7;
            assert_eq!(
                prepare_mct_decorrelation(&components, &collection, &limits, &mut work).err(),
                expected_error
            );
            assert_eq!(work, 23);
        }
    }
    let missing = MctCollection::from_arrays(true, vec![17, 0], vec![999, 17], matrix(), None);
    let mut work = 7;
    assert_eq!(
        prepare_mct_decorrelation(&components, &missing, &ResourceLimits::default(), &mut work)
            .err(),
        Some(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidTransform
        })
    );
    assert_eq!(work, 7);
    drop(components);
    assert_eq!(samples, before_samples);
    assert_eq!(fractions, [0, 0]);
}

#[test]
fn native_mct_decorrelation_admission_keeps_every_overflow_limit_and_counter_frontier() {
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    for maximum_work in [1, 37, 1000] {
        for maximum_bytes in [1, 56, 1000] {
            let limits = ResourceLimits::default()
                .with_maximum_work_units(maximum_work)
                .unwrap()
                .with_maximum_decoded_bytes(maximum_bytes)
                .unwrap();
            for samples in [0, 1, 2, 3, 17, usize::MAX] {
                for rows in [0, 1, 2, 3, 17, usize::MAX] {
                    for columns in [0, 1, 2, 3, 17, usize::MAX] {
                        for before in [0, 1, 7, u64::MAX - 1, u64::MAX] {
                            let sample_rows = samples as u128 * rows as u128;
                            let operations = if sample_rows > u128::from(u64::MAX) {
                                None
                            } else {
                                let products = sample_rows * columns as u128;
                                if products > u128::from(u64::MAX)
                                    || products + sample_rows > u128::from(u64::MAX)
                                {
                                    None
                                } else {
                                    Some(products + sample_rows)
                                }
                            };
                            let expected = match operations {
                                None => (Err(overflow), before),
                                Some(operations)
                                    if operations + u128::from(before) > u128::from(u64::MAX) =>
                                {
                                    (Err(overflow), before)
                                }
                                Some(operations) => {
                                    let charged =
                                        u64::try_from(operations + u128::from(before)).unwrap();
                                    if charged > maximum_work {
                                        (
                                            Err(DecodeError::LimitExceeded {
                                                resource: Resource::WorkUnits,
                                                limit: maximum_work,
                                                actual: charged,
                                            }),
                                            charged,
                                        )
                                    } else {
                                        let values = rows as u128 + columns as u128;
                                        let bytes = values * 8;
                                        if values > usize::MAX as u128 || bytes > usize::MAX as u128
                                        {
                                            (Err(overflow), charged)
                                        } else if bytes > u128::from(maximum_bytes) {
                                            (
                                                Err(DecodeError::LimitExceeded {
                                                    resource: Resource::DecodedBytes,
                                                    limit: maximum_bytes,
                                                    actual: u64::try_from(bytes).unwrap(),
                                                }),
                                                charged,
                                            )
                                        } else {
                                            (Ok(()), charged)
                                        }
                                    }
                                }
                            };
                            let mut work = before;
                            let result = admit_mct_decorrelation(
                                samples, rows, columns, &limits,
                                &mut work, // The counter is part of the checked outcome.
                            );
                            assert_eq!((result, work), expected);
                        }
                    }
                }
            }
        }
    }
    for maximum_work in [36, 37, 38] {
        for maximum_bytes in [55, 56, 57] {
            let limits = ResourceLimits::default()
                .with_maximum_work_units(maximum_work)
                .unwrap()
                .with_maximum_decoded_bytes(maximum_bytes)
                .unwrap();
            let mut work = 7;
            let expected = if maximum_work < 37 {
                Err(DecodeError::LimitExceeded {
                    resource: Resource::WorkUnits,
                    limit: maximum_work,
                    actual: 37,
                })
            } else if maximum_bytes < 56 {
                Err(DecodeError::LimitExceeded {
                    resource: Resource::DecodedBytes,
                    limit: maximum_bytes,
                    actual: 56,
                })
            } else {
                Ok(())
            };
            assert_eq!(
                admit_mct_decorrelation(2, 3, 4, &limits, &mut work),
                expected
            );
            assert_eq!(work, 37);
        }
    }
}

#[test]
fn native_mct_layout_matches_raw_geometry_precision_and_index_reference() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let base = (u32::MAX, 0_u32, 0_u32, u32::MAX, 0_u8, u8::MAX);
    let sources = [
        vec![],
        vec![0],
        vec![1],
        vec![0, 1],
        vec![1, 0],
        vec![2, 2],
        vec![3],
        vec![usize::MAX],
    ];
    let destinations = [vec![], vec![0], vec![1, 2], vec![0, 3], vec![usize::MAX]];
    for perturbation in 0..9 {
        let mut geometry = [base; 3];
        let mut lengths = [2, 2, 2];
        match perturbation {
            1 => geometry[1].0 = 0,
            2 => geometry[1].1 = u32::MAX,
            3 => geometry[1].2 = 1,
            4 => geometry[1].3 = 0,
            5 => geometry[1].4 = 1,
            6 => geometry[1].5 = 0,
            7 => lengths[1] = 1,
            8 => lengths[0] = 0,
            _ => {}
        }
        for first_bits in [0, 1, 32, 33, u8::MAX] {
            for second_bits in [0, 1, 32, 33, u8::MAX] {
                for third_bits in [0, 32, u8::MAX] {
                    for source in &sources {
                        for destination in &destinations {
                            for reversible in [false, true] {
                                let mut fractions = [first_bits, second_bits, third_bits];
                                let before_fractions = fractions;
                                let expected = source
                                    .first()
                                    .and_then(|first| {
                                        let first_geometry = geometry.get(*first)?;
                                        let valid =
                                            source.iter().chain(destination.iter()).all(|index| {
                                                geometry.get(*index).is_some_and(|candidate| {
                                                    candidate == first_geometry
                                                        && lengths[*index] == lengths[*first]
                                                        && fractions[*index] <= 32
                                                })
                                            });
                                        (valid
                                            && (!reversible
                                                || source
                                                    .iter()
                                                    .all(|index| fractions[*index] == 0)))
                                        .then_some(lengths[*first])
                                    })
                                    .ok_or(invalid);
                                let mut samples = lengths.map(|length| vec![i64::MIN; length]);
                                let before_samples = samples.clone();
                                let components: Vec<_> = samples
                                    .iter_mut()
                                    .zip(fractions.iter_mut())
                                    .zip(geometry)
                                    .map(
                                        |(
                                            (samples, fraction_bits),
                                            (x, y, width, height, x_subsampling, y_subsampling),
                                        )| {
                                            TransformComponentMut {
                                                component: u16::MAX,
                                                x,
                                                y,
                                                width,
                                                height,
                                                x_subsampling,
                                                y_subsampling,
                                                fraction_bits,
                                                samples,
                                            }
                                        },
                                    )
                                    .collect();
                                assert_eq!(
                                    validate_mct_components_layout(
                                        &components,
                                        source,
                                        destination,
                                        reversible
                                    ),
                                    expected
                                );
                                drop(components);
                                assert_eq!(samples, before_samples);
                                assert_eq!(fractions, before_fractions);
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn native_mct_array_store_frames_every_unselected_component_and_error() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    for destination in [0, 1, 2, 3, usize::MAX] {
        for index in [0, 1, 2, usize::MAX] {
            for value in [i64::MIN, 0, i64::MAX] {
                let mut samples = [vec![], vec![7], vec![-3, 9]];
                let mut expected = samples.clone();
                let expected_result = match expected
                    .get_mut(destination)
                    .and_then(|samples| samples.get_mut(index))
                {
                    Some(sample) => {
                        *sample = value;
                        Ok(())
                    }
                    None => Err(invalid),
                };
                let mut fractions = [u8::MAX, 32, 0];
                let before_fractions = fractions;
                let mut components: Vec<_> = samples
                    .iter_mut()
                    .zip(fractions.iter_mut())
                    .zip([0, 17, u16::MAX])
                    .map(
                        |((samples, fraction_bits), component)| TransformComponentMut {
                            component,
                            x: u32::MAX,
                            y: 1,
                            width: 0,
                            height: u32::MAX,
                            x_subsampling: 0,
                            y_subsampling: u8::MAX,
                            fraction_bits,
                            samples,
                        },
                    )
                    .collect();
                assert_eq!(
                    store_transform_sample(&mut components, destination, index, value),
                    expected_result
                );
                for component in &components {
                    assert_eq!(
                        (
                            component.x,
                            component.y,
                            component.width,
                            component.height,
                            component.x_subsampling,
                            component.y_subsampling
                        ),
                        (u32::MAX, 1, 0, u32::MAX, 0, u8::MAX)
                    );
                }
                drop(components);
                assert_eq!(samples, expected);
                assert_eq!(fractions, before_fractions);
            }
        }
    }
}

#[test]
fn native_mct_sample_store_preserves_all_metadata_and_failure_samples() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    for length in 0..=4 {
        for index in [0, 1, 3, 4, 5, usize::MAX] {
            for value in [i64::MIN, -1, 0, i64::MAX] {
                let mut samples: Vec<_> = (0..length).map(|sample| i64::from(sample) - 2).collect();
                let mut expected = samples.clone();
                let result = match expected.get_mut(index) {
                    Some(sample) => {
                        *sample = value;
                        Ok(())
                    }
                    None => Err(invalid),
                };
                let mut fraction_bits = u8::MAX;
                let mut component = TransformComponentMut {
                    component: u16::MAX,
                    x: u32::MAX,
                    y: 1,
                    width: 0,
                    height: u32::MAX,
                    x_subsampling: 0,
                    y_subsampling: u8::MAX,
                    fraction_bits: &mut fraction_bits,
                    samples: &mut samples,
                };
                assert_eq!(
                    store_transform_component_sample(&mut component, index, value),
                    result
                );
                assert_eq!(
                    (
                        component.component,
                        component.x,
                        component.y,
                        component.width,
                        component.height,
                        component.x_subsampling,
                        component.y_subsampling,
                        *component.fraction_bits
                    ),
                    (u16::MAX, u32::MAX, 1, 0, u32::MAX, 0, u8::MAX, u8::MAX)
                );
                assert_eq!(component.samples, expected);
            }
        }
    }
}

#[test]
fn native_mct_component_lookup_keeps_first_duplicate_and_all_raw_mutable_values() {
    let references = [0, u16::MAX, 17, 0];
    let mut samples = [vec![], vec![i64::MIN], vec![i64::MAX, 0], vec![3, -9, 1]];
    let mut fractions = [u8::MAX, 0, 32, 1];
    let before_samples = samples.clone();
    let before_fractions = fractions;
    let components: Vec<_> = samples
        .iter_mut()
        .zip(fractions.iter_mut())
        .zip(references)
        .map(
            |((samples, fraction_bits), component)| TransformComponentMut {
                component,
                x: u32::MAX,
                y: 0,
                width: 0,
                height: u32::MAX,
                x_subsampling: 0,
                y_subsampling: u8::MAX,
                fraction_bits,
                samples,
            },
        )
        .collect();
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    for reference in 0..=u16::MAX {
        let expected = references
            .iter()
            .position(|value| *value == reference)
            .ok_or(invalid);
        assert_eq!(find_transform_component(&components, reference), expected);
    }
    assert_eq!(find_transform_component(&[], 0), Err(invalid));
    drop(components);
    assert_eq!(samples, before_samples);
    assert_eq!(fractions, before_fractions);
}

#[test]
fn native_mct_dependency_rows_match_independent_floor_and_rational_references() {
    use crate::codestream::{MctArrayKind, MctNumericFormat};
    let array = |fraction, values| {
        MctArray::from_values(
            u8::MAX,
            MctArrayKind::Offset,
            MctNumericFormat::Float64,
            fraction,
            values,
        )
    };
    let source = [10, -20, 30, -40];
    let offsets = [1, -2, 3, -4];
    for declared_reversible in [false, true] {
        for fraction in [0, 32, u8::MAX] {
            for coefficient in -2..=2 {
                for scale in [1, 2, 3, 7] {
                    let mut matrix = vec![coefficient; 9];
                    for index in [1, 4, 8] {
                        matrix[index] = scale;
                    }
                    let collection = MctCollection::from_dependency(
                        declared_reversible,
                        vec![u16::MAX, 0, 0],
                        Some(array(fraction, matrix)),
                        Some(array(0, offsets.to_vec())),
                    );
                    for value in -5..=5 {
                        let output = [value, -value - 1, 2 * value];
                        for row in 0..4 {
                            let prediction = if row == 0 {
                                0
                            } else {
                                let dot: i128 = output
                                    .iter()
                                    .take(row)
                                    .map(|sample| i128::from(coefficient) * i128::from(*sample))
                                    .sum();
                                (i128::from(scale / 2) + dot).div_euclid(i128::from(scale))
                            };
                            let expected =
                                i128::from(source[row]) + i128::from(offsets[row]) + prediction;
                            assert_eq!(
                                reversible_dependency_row(&collection, &source, &output, row),
                                Ok(i64::try_from(expected).unwrap())
                            );
                        }
                    }
                }
            }
        }
    }
    let nearest = |value: i128, bits: u8| {
        if bits == 0 {
            value
        } else {
            let divisor = 1_i128 << bits;
            let magnitude = (value.abs() + divisor / 2) / divisor;
            if value < 0 { -magnitude } else { magnitude }
        }
    };
    let output = [-7, 11, -13];
    for declared_reversible in [false, true] {
        for coefficient in -3..=3 {
            for coefficient_bits in [0, 1, 4] {
                for offset_bits in [0, 1, 4] {
                    for source_bits in [0, 1, 4, 32] {
                        let collection = MctCollection::from_dependency(
                            declared_reversible,
                            vec![],
                            Some(array(coefficient_bits, vec![coefficient; 6])),
                            Some(array(offset_bits, offsets.to_vec())),
                        );
                        for row in 0..4 {
                            let initial = i128::from(source[row]) * (1_i128 << (32 - source_bits))
                                + i128::from(offsets[row]) * (1_i128 << (32 - offset_bits));
                            let expected = initial
                                + output
                                    .iter()
                                    .take(row)
                                    .map(|sample| {
                                        nearest(
                                            i128::from(coefficient) * i128::from(*sample),
                                            coefficient_bits,
                                        )
                                    })
                                    .sum::<i128>();
                            assert_eq!(
                                irreversible_dependency_row(
                                    &collection,
                                    &source,
                                    &[source_bits; 4],
                                    &output,
                                    row
                                ),
                                Ok(i64::try_from(expected).unwrap())
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn native_mct_dependency_rows_preserve_lazy_raw_precision_and_first_error_frontiers() {
    use crate::codestream::{MctArrayKind, MctNumericFormat};
    let array = |fraction, values| {
        MctArray::from_values(
            u8::MAX,
            MctArrayKind::Offset,
            MctNumericFormat::Float32,
            fraction,
            values,
        )
    };
    let collection =
        |matrix, offsets| MctCollection::from_dependency(false, vec![], matrix, offsets);
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    for precision in 0..=u8::MAX {
        let empty = collection(Some(array(precision, vec![])), None);
        assert_eq!(reversible_dependency_row(&empty, &[7], &[], 0), Ok(7));
        assert_eq!(
            irreversible_dependency_row(&empty, &[7], &[32], &[], 0),
            Ok(7)
        );
        let reversible = collection(Some(array(precision, vec![0, 1])), None);
        assert_eq!(
            reversible_dependency_row(&reversible, &[0, 0], &[0], 1),
            Ok(0)
        );
        let irreversible = collection(Some(array(precision, vec![0])), None);
        assert_eq!(
            irreversible_dependency_row(&irreversible, &[0, 0], &[0, 0], &[0], 1),
            if precision <= 126 {
                Ok(0)
            } else {
                Err(overflow)
            }
        );
        let no_matrix = collection(None, None);
        assert_eq!(
            irreversible_dependency_row(&no_matrix, &[0], &[precision], &[], 0),
            if precision <= 158 {
                Ok(0)
            } else {
                Err(overflow)
            }
        );
        let offsets = collection(None, Some(array(precision, vec![0])));
        assert_eq!(
            irreversible_dependency_row(&offsets, &[0], &[32], &[], 0),
            if precision <= 32 { Ok(0) } else { Err(invalid) }
        );
        assert_eq!(
            reversible_dependency_row(&offsets, &[0], &[], 0),
            if precision == 0 { Ok(0) } else { Err(invalid) }
        );
    }
    let malformed = collection(Some(array(u8::MAX, vec![])), Some(array(u8::MAX, vec![])));
    assert_eq!(
        reversible_dependency_row(&malformed, &[], &[], usize::MAX),
        Err(invalid)
    );
    assert_eq!(
        irreversible_dependency_row(&malformed, &[0], &[159], &[], 0),
        Err(overflow)
    );
    let missing = collection(None, None);
    assert_eq!(
        irreversible_dependency_row(&missing, &[0], &[], &[], 0),
        Err(invalid)
    );
    let late = collection(Some(array(0, vec![0, 1, i64::MIN, i64::MIN, 1])), None);
    assert_eq!(
        reversible_dependency_row(&late, &[0, 0, 0], &[i64::MIN; 2], 2),
        Err(overflow)
    );
    let base = collection(Some(array(0, vec![])), Some(array(0, vec![1])));
    assert_eq!(
        reversible_dependency_row(&base, &[i64::MAX], &[], 0),
        Err(overflow)
    );
    let floor = collection(Some(array(0, vec![-1, 2])), None);
    assert_eq!(reversible_dependency_row(&floor, &[0, 0], &[4], 1), Ok(-2));
    let nearest = collection(Some(array(1, vec![-1])), None);
    assert_eq!(
        irreversible_dependency_row(&nearest, &[0, 0], &[32, 32], &[1], 1),
        Ok(-1)
    );
}

#[test]
fn native_mct_matrix_rows_preserve_numeric_values_raw_precision_domains_and_error_order() {
    use crate::codestream::{MctArrayKind, MctNumericFormat};
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let array = |fraction, values| {
        MctArray::from_values(
            u8::MAX,
            MctArrayKind::Offset,
            MctNumericFormat::Float64,
            fraction,
            values,
        )
    };
    let matrix = array(0, vec![2, -3, 4]);
    let offset = array(0, vec![1]);
    assert_eq!(
        reversible_mct_row(&matrix, Some(&offset), &[5, 7], 0),
        Err(invalid)
    );
    assert_eq!(
        fixed_mct_row_scaled(&matrix, Some(&offset), &[5, 7], &[0, 0], 0),
        Ok(-10_i64 << 32)
    );
    let fixed = array(32, vec![2_i64 << 32, -(3_i64 << 32)]);
    let offset = array(16, vec![1_i64 << 16]);
    assert_eq!(
        fixed_mct_row_scaled(
            &fixed,
            Some(&offset),
            &[5_i64 << 32, 7_i64 << 32],
            &[32, 32],
            0
        ),
        Ok(-10_i64 << 32)
    );
    let one = array(32, vec![1]);
    assert_eq!(fixed_mct_row_scaled(&one, None, &[1], &[1], 0), Ok(1));
    assert_eq!(fixed_mct_row_scaled(&one, None, &[-1], &[1], 0), Ok(-1));
    let empty = array(0, vec![]);
    assert_eq!(
        reversible_mct_row(&empty, None, &[], usize::MAX),
        Err(invalid)
    );
    assert_eq!(
        fixed_mct_row_scaled(&empty, None, &[], &[], usize::MAX),
        Ok(0)
    );
    assert_eq!(reversible_mct_row(&empty, None, &[1], 0), Err(invalid));
    assert_eq!(
        reversible_mct_row(&matrix, None, &[1, 2], usize::MAX),
        Err(invalid)
    );
    assert_eq!(
        reversible_mct_row(&matrix, Some(&empty), &[1, 2], usize::MAX),
        Err(invalid)
    );
    assert_eq!(
        fixed_mct_row_scaled(&one, Some(&empty), &[1], &[], usize::MAX),
        Err(invalid)
    );
    let wide = array(0, vec![i64::MAX; 3]);
    assert_eq!(
        reversible_mct_row(&wide, None, &[i64::MAX; 3], 0),
        Err(invalid)
    );
    let short = array(32, vec![]);
    assert_eq!(
        fixed_mct_row_scaled(&short, None, &[1], &[u8::MAX], 0),
        Err(invalid)
    );
    assert_eq!(
        fixed_mct_row_scaled(&one, None, &[1], &[u8::MAX], 0),
        Err(overflow)
    );
    for precision in 0..=u8::MAX {
        let zero = array(precision, vec![]);
        assert_eq!(
            reversible_mct_row(&zero, None, &[], usize::MAX),
            Err(invalid)
        );
        assert_eq!(
            fixed_mct_row_scaled(&zero, None, &[], &[], usize::MAX),
            if precision <= 32 { Ok(0) } else { Err(invalid) }
        );
        let zero = array(0, vec![0]);
        assert_eq!(
            fixed_mct_row_scaled(&zero, None, &[0], &[precision], 0),
            if precision <= 158 {
                Ok(0)
            } else {
                Err(overflow)
            }
        );
        let offsets = array(precision, vec![0]);
        assert_eq!(
            fixed_mct_row_scaled(&zero, Some(&offsets), &[0], &[0], 0),
            if precision <= 32 { Ok(0) } else { Err(invalid) }
        );
    }
}

#[test]
fn native_mct_round_rescale_offsets_and_work_match_wide_reference_and_full_u8_domains() {
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let round = |value: i128, bits: u8| {
        if bits == 0 {
            return Ok(value);
        }
        if bits > 126 {
            return Err(overflow);
        }
        let magnitude = value.checked_abs().ok_or(overflow)?;
        let half = 2_i128.pow(u32::from(bits - 1));
        if magnitude > i128::MAX - half {
            return Err(overflow);
        }
        let divisor = 2_i128.pow(u32::from(bits));
        let rounded = magnitude / divisor + i128::from(magnitude % divisor >= half);
        Ok(if value < 0 { -rounded } else { rounded })
    };
    let values = [
        i128::MIN,
        i128::MIN + 1,
        -(1_i128 << 126),
        -3,
        -2,
        -1,
        0,
        1,
        2,
        3,
        1_i128 << 126,
        i128::MAX - 1,
        i128::MAX,
    ];
    for bits in 0..=u8::MAX {
        for value in values {
            assert_eq!(rounded_shift_i128(value, bits), round(value, bits));
        }
        assert_eq!(rescale_i128(i128::MIN, bits, bits), Ok(i128::MIN));
    }
    for from in 0..=u8::MAX {
        for to in 0..=u8::MAX {
            for value in [-3_i128, -1, 0, 1, 3] {
                let expected = if from == to {
                    Ok(value)
                } else if from > to {
                    round(value, from - to)
                } else if to - from > 126 {
                    Err(overflow)
                } else {
                    value
                        .checked_mul(2_i128.pow(u32::from(to - from)))
                        .ok_or(overflow)
                };
                assert_eq!(
                    rescale_i128(value, from, to),
                    expected,
                    "value={value} from={from} to={to}"
                );
            }
        }
    }
    let samples = vec![i64::MIN, -3, 0, 3, i64::MAX];
    for fraction in 0..=u8::MAX {
        let array = MctArray::from_values(
            u8::MAX,
            crate::codestream::MctArrayKind::Dependency,
            crate::codestream::MctNumericFormat::Float64,
            fraction,
            samples.clone(),
        );
        for row in [0, 1, 4, 5, usize::MAX] {
            let direct = if fraction != 0 {
                Err(invalid)
            } else {
                samples.get(row).copied().ok_or(invalid)
            };
            assert_eq!(offset_value(Some(&array), row), direct);
            let scaled = if fraction > 32 {
                Err(invalid)
            } else {
                samples
                    .get(row)
                    .map(|value| i128::from(*value) * 2_i128.pow(u32::from(32 - fraction)))
                    .ok_or(invalid)
            };
            assert_eq!(offset_value_scaled(Some(&array), row), scaled);
            assert_eq!(offset_value(None, row), Ok(0));
            assert_eq!(offset_value_scaled(None, row), Ok(0));
        }
    }
    let limits = ResourceLimits::default();
    let maximum = limits.maximum_work_units();
    for before in [0, maximum, maximum + 1, u64::MAX] {
        for operations in [0, 1, 2, u64::MAX] {
            let mut work = before;
            let expected = match before.checked_add(operations) {
                None => (Err(overflow), before),
                Some(after) => (
                    if after > maximum {
                        Err(DecodeError::LimitExceeded {
                            resource: Resource::WorkUnits,
                            limit: maximum,
                            actual: after,
                        })
                    } else {
                        Ok(())
                    },
                    after,
                ),
            };
            assert_eq!(
                (charge_mct_work(&mut work, operations, &limits), work),
                expected
            );
        }
    }
    for count in [
        0,
        1,
        limits.maximum_decoded_bytes() as usize / 8,
        limits.maximum_decoded_bytes() as usize / 8 + 1,
        usize::MAX,
    ] {
        let bytes = count as u128 * 8;
        let expected = if bytes > u128::from(u64::MAX) {
            Err(overflow)
        } else if bytes > u128::from(limits.maximum_decoded_bytes()) {
            Err(DecodeError::LimitExceeded {
                resource: Resource::DecodedBytes,
                limit: limits.maximum_decoded_bytes(),
                actual: bytes as u64,
            })
        } else {
            Ok(())
        };
        assert_eq!(check_mct_scratch(count, &limits), expected);
    }
}

#[test]
fn typed_image_admission_preserves_native_count_origin_shape_and_error_priority() {
    fn components(count: usize) -> Vec<TypedComponent> {
        (0..count)
            .map(|_| {
                TypedComponent::from_parts(
                    0,
                    u32::MAX,
                    ComponentInfo {
                        precision: 0,
                        signed: true,
                        x_subsampling: 0,
                        y_subsampling: 0,
                        x_registration: u16::MAX,
                        y_registration: u16::MAX,
                    },
                    TypedSamples::Unsigned(vec![]),
                )
            })
            .collect()
    }
    let limits = ResourceLimits::default()
        .with_maximum_decoded_bytes(1)
        .unwrap();
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    for count in [0, 1, 64, 65, 65_535, 65_536] {
        for (x_origin, y_origin) in [(0, 0), (u32::MAX, 0), (0, u32::MAX)] {
            let result = typed_image_from_components_with_origin(
                1,
                1,
                x_origin,
                y_origin,
                components(count),
                &limits,
            );
            if x_origin == u32::MAX || y_origin == u32::MAX || count > usize::from(u16::MAX) {
                assert_eq!(result, Err(overflow));
            } else if count > usize::from(limits.maximum_components()) {
                assert_eq!(
                    result,
                    Err(DecodeError::LimitExceeded {
                        resource: Resource::Components,
                        limit: u64::from(limits.maximum_components()),
                        actual: count as u64,
                    })
                );
            } else {
                let result = result.unwrap();
                assert_eq!(result.components().len(), count);
                for component in result.components() {
                    assert_eq!((component.width(), component.height()), (0, u32::MAX));
                    assert_eq!(component.info().precision, 0);
                    assert_eq!(component.info().x_subsampling, 0);
                    assert!(
                        matches!(component.samples(), TypedSamples::Unsigned(values) if values.is_empty())
                    );
                }
            }
        }
    }
    let info = ComponentInfo {
        precision: 0,
        signed: false,
        x_subsampling: 0,
        y_subsampling: 0,
        x_registration: 0,
        y_registration: 0,
    };
    let malformed = || TypedComponent::from_parts(1, 1, info, TypedSamples::Signed(vec![]));
    let valid = || TypedComponent::from_parts(1, 1, info, TypedSamples::Signed(vec![7]));
    assert_eq!(
        typed_image_from_components_with_origin(0, 0, 0, 0, vec![malformed()], &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidImageGeometry
        }),
    );
    assert_eq!(
        TypedImage::from_components_with_origin(0, 0, 0, 0, vec![valid(), malformed()], &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: 1,
            actual: 8
        }),
    );
}
use crate::codestream::{
    MctArrayKind,
    MctCollection,
    MctNumericFormat,
    MctStage,
    MctWaveletType, // Raw Part 2 descriptors also exercise unknown metadata.
};

fn copy_decoded(image: &DecodedImage) -> DecodedImage {
    DecodedImage {
        width: image.width,
        height: image.height,
        x_origin: image.x_origin,
        y_origin: image.y_origin,
        components: image
            .components
            .iter()
            .map(|component| DecodedComponent {
                width: component.width,
                height: component.height,
                info: component.info,
                fraction_bits: component.fraction_bits,
                samples: component.samples.clone(),
            })
            .collect(),
    }
}

fn component_reference_values(
    y: i64,
    cb: i64,
    cr: i64,
    irreversible: bool,
) -> Result<(i64, i64, i64), DecodeError> {
    let checked = |value: i128| {
        i64::try_from(value)
            .map(i128::from)
            .map_err(|_| arithmetic_overflow())
    };
    let fixed = |value: i64, factor: i128| {
        let product = checked(i128::from(value) * factor)?;
        Ok::<i128, DecodeError>(checked(product + 32768)?.div_euclid(65536))
    };
    let y = i128::from(y);
    if irreversible {
        let red = checked(y + fixed(cr, 91881)?)?;
        let green_first = checked(y - fixed(cb, 22553)?)?;
        let green = checked(green_first - fixed(cr, 46797)?)?;
        let blue = checked(y + fixed(cb, 116130)?)?;
        Ok((red as i64, green as i64, blue as i64))
    } else {
        let sum = checked(i128::from(cb) + i128::from(cr))?;
        let green = checked(y - sum.div_euclid(4))?;
        let red = checked(green + i128::from(cr))?;
        let blue = checked(green + i128::from(cb))?;
        Ok((red as i64, green as i64, blue as i64))
    }
}

fn component_reference(image: &mut DecodedImage, irreversible: bool) -> Result<(), DecodeError> {
    if image.components.len() < 3 {
        return Err(invalid_image());
    }
    let first = &image.components[0];
    for component in &image.components[..3] {
        if component.width != first.width
            || component.height != first.height
            || component.fraction_bits != if irreversible { 16 } else { 0 }
            || component.info.x_subsampling != first.info.x_subsampling
            || component.info.y_subsampling != first.info.y_subsampling
        {
            return Err(invalid_image());
        }
    }
    let length = first.samples.len();
    if image.components[1].samples.len() != length || image.components[2].samples.len() != length {
        return Err(invalid_image());
    }
    for index in 0..length {
        let (red, green, blue) = component_reference_values(
            image.components[0].samples[index],
            image.components[1].samples[index],
            image.components[2].samples[index],
            irreversible,
        )?;
        image.components[0].samples[index] = red;
        image.components[1].samples[index] = green;
        image.components[2].samples[index] = blue;
    }
    Ok(())
}

fn raw_component_image(samples: [Vec<i64>; 3], fraction_bits: u8) -> DecodedImage {
    let mut components: Vec<_> = samples
        .into_iter()
        .enumerate()
        .map(|(i, samples)| DecodedComponent {
            width: 5,
            height: 7,
            info: ComponentInfo {
                precision: (8 + i) as u8,
                signed: i.is_multiple_of(2),
                x_subsampling: 1,
                y_subsampling: 1,
                x_registration: i as u16,
                y_registration: (i + 3) as u16,
            },
            fraction_bits,
            samples,
        })
        .collect();
    components.push(DecodedComponent {
        width: 0,
        height: 19,
        info: ComponentInfo::default(),
        fraction_bits: 255,
        samples: vec![i64::MIN, i64::MAX, 7],
    });
    DecodedImage {
        width: 31,
        height: 19,
        x_origin: 9,
        y_origin: 7,
        components,
    }
}

#[test]
fn complete_component_images_match_independent_wide_reference() {
    for irreversible in [false, true] {
        for y in [-7, -3, -1, 0, 1, 3, 7] {
            for cb in [-7, -3, -1, 0, 1, 3, 7] {
                for cr in [-7, -3, -1, 0, 1, 3, 7] {
                    let mut actual = raw_component_image(
                        [
                            vec![y, y * 65536, -y * 32768],
                            vec![cb, cb * 65536, -cb * 32768],
                            vec![cr, cr * 65536, -cr * 32768],
                        ],
                        if irreversible { 16 } else { 0 },
                    );
                    let mut expected = copy_decoded(&actual);
                    let expected_status = component_reference(&mut expected, irreversible);
                    let status = if irreversible {
                        apply_irreversible_component_transform(&mut actual)
                    } else {
                        apply_reversible_component_transform(&mut actual)
                    };
                    assert_eq!((status, actual), (expected_status, expected));
                }
            }
        }
        for samples in [
            [vec![], vec![], vec![]],
            [vec![10, i64::MIN], vec![2, i64::MAX], vec![6, 0]],
            [vec![10, i64::MAX], vec![2, -4], vec![6, 4]],
            [vec![10, i64::MAX], vec![2, 4], vec![6, -4]],
            [vec![10, 0], vec![2, i64::MAX], vec![6, i64::MIN]],
            [vec![10, i64::MIN], vec![2, 0], vec![6, 0]],
        ] {
            let mut actual = raw_component_image(samples, if irreversible { 16 } else { 0 });
            let mut expected = copy_decoded(&actual);
            let expected_status = component_reference(&mut expected, irreversible);
            let status = if irreversible {
                apply_irreversible_component_transform(&mut actual)
            } else {
                apply_reversible_component_transform(&mut actual)
            };
            assert_eq!((status, actual), (expected_status, expected));
        }
    }
}

#[test]
fn complete_component_transform_validation_preserves_error_order_and_state() {
    for irreversible in [false, true] {
        for component_count in 0..3 {
            let mut actual = raw_component_image(
                [vec![i64::MAX], vec![i64::MAX], vec![1]],
                if irreversible { 16 } else { 0 },
            );
            actual.components.truncate(component_count);
            let expected = copy_decoded(&actual);
            let status = if irreversible {
                apply_irreversible_component_transform(&mut actual)
            } else {
                apply_reversible_component_transform(&mut actual)
            };
            assert_eq!((status, actual), (Err(invalid_image()), expected));
        }
        for variant in 0..6 {
            let mut actual = raw_component_image(
                [vec![i64::MAX, 0], vec![i64::MAX, 0], vec![1, 0]],
                if irreversible { 16 } else { 0 },
            );
            match variant {
                0 => actual.components[1].width += 1,
                1 => actual.components[2].height += 1,
                2 => actual.components[0].fraction_bits ^= 1,
                3 => actual.components[1].info.x_subsampling = 0,
                4 => actual.components[2].info.y_subsampling = 0,
                _ => {
                    actual.components[1].samples.pop();
                }
            }
            let expected = copy_decoded(&actual);
            let status = if irreversible {
                apply_irreversible_component_transform(&mut actual)
            } else {
                apply_reversible_component_transform(&mut actual)
            };
            assert_eq!((status, actual), (Err(invalid_image()), expected));
        }
    }
}

#[test]
fn complete_component_pixel_frames_and_rejections_match_independent_reference() {
    for irreversible in [false, true] {
        for samples in [
            [vec![10], vec![2], vec![6]],
            [vec![i64::MAX], vec![i64::MAX], vec![1]],
            [vec![10], vec![2], vec![]],
        ] {
            for index in 0..=1 {
                let mut actual = raw_component_image(samples.clone(), 255);
                let mut expected = copy_decoded(&actual);
                let values = if expected.components[..3]
                    .iter()
                    .any(|component| index >= component.samples.len())
                {
                    Err(invalid_image())
                } else {
                    component_reference_values(
                        expected.components[0].samples[index],
                        expected.components[1].samples[index],
                        expected.components[2].samples[index],
                        irreversible,
                    )
                };
                let expected_status = match values {
                    Err(error) => Err(error),
                    Ok((red, green, blue)) => {
                        expected.components[0].samples[index] = red;
                        expected.components[1].samples[index] = green;
                        expected.components[2].samples[index] = blue;
                        Ok(())
                    }
                };
                let status = apply_component_pixel(&mut actual, index, irreversible);
                assert_eq!((status, actual), (expected_status, expected));
            }
        }
    }
}

fn image_size(components: &[ComponentInfo], width: u32, height: u32) -> ImageSize {
    let mut component_info = [ComponentInfo::default(); 64];
    component_info[..components.len()].copy_from_slice(components);
    ImageSize {
        width,
        height,
        x_origin: 0,
        y_origin: 0,
        components: u16::try_from(components.len()).unwrap(),
        uniform_bit_depth: None,
        uniform_signed: None,
        tile_width: width,
        tile_height: height,
        tile_x_origin: 0,
        tile_y_origin: 0,
        tiles_across: 1,
        tiles_down: 1,
        component_info,
    }
}

fn reference_decoded_typed_samples(
    component: &DecodedComponent,
    maximum: u64,
) -> Result<TypedSamples, DecodeError> {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidImageGeometry,
    };
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let precision = component.info.precision;
    if precision == 0 || precision > 38 {
        return Err(invalid);
    }
    let bytes = component.samples.len() as u128 * 8;
    if bytes > u128::from(u64::MAX) {
        return Err(arithmetic);
    }
    if bytes > u128::from(maximum) {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: maximum,
            actual: u64::try_from(bytes).unwrap(),
        });
    }
    let signed_power = 1_i128 << (precision - 1);
    let unsigned_maximum = (1_i128 << precision) - 1;
    let mut signed = Vec::new();
    let mut unsigned = Vec::new();
    for &sample in &component.samples {
        let rounded = if component.fraction_bits == 0 {
            i128::from(sample)
        } else {
            if component.fraction_bits > 62 {
                return Err(invalid);
            }
            let biased = i128::from(sample) + (1_i128 << (component.fraction_bits - 1));
            if biased > i128::from(i64::MAX) || biased < i128::from(i64::MIN) {
                return Err(arithmetic);
            }
            biased >> component.fraction_bits
        };
        if component.info.signed {
            signed.push(i64::try_from(rounded.clamp(-signed_power, signed_power - 1)).unwrap());
        } else {
            let shifted = rounded + signed_power;
            if shifted > i128::from(i64::MAX) || shifted < i128::from(i64::MIN) {
                return Err(arithmetic);
            }
            unsigned.push(u64::try_from(shifted.clamp(0, unsigned_maximum)).unwrap());
        }
    }
    Ok(if component.info.signed {
        TypedSamples::Signed(signed)
    } else {
        TypedSamples::Unsigned(unsigned)
    })
}

fn reference_decoded_typed_image(
    image: &DecodedImage,
    maximum: u64,
) -> Result<TypedImage, DecodeError> {
    let mut bytes = 0_u128;
    let mut components = Vec::new();
    for component in &image.components {
        bytes += component.samples.len() as u128 * 8;
        if bytes > u128::from(u64::MAX) {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::ArithmeticOverflow,
            });
        }
        if bytes > u128::from(maximum) {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::DecodedBytes,
                limit: maximum,
                actual: u64::try_from(bytes).unwrap(),
            });
        }
        components.push(TypedComponent {
            width: component.width,
            height: component.height,
            info: component.info,
            samples: reference_decoded_typed_samples(component, maximum)?,
            channel_definitions: Vec::new(),
        });
    }
    Ok(TypedImage {
        width: image.width,
        height: image.height,
        x_origin: image.x_origin,
        y_origin: image.y_origin,
        components,
    })
}

#[test]
fn complete_decoded_typed_samples_match_independent_wide_reference_all_u8_parameters() {
    let payloads = [vec![], vec![i64::MIN, -65536, -1, 0, 1, i64::MAX]];
    let limits = [
        ResourceLimits::default(),
        ResourceLimits::default()
            .with_maximum_decoded_bytes(1)
            .unwrap(),
        ResourceLimits::default()
            .with_maximum_decoded_bytes(47)
            .unwrap(),
        ResourceLimits::default()
            .with_maximum_decoded_bytes(48)
            .unwrap(),
    ];
    for precision in 0..=u8::MAX {
        for fraction_bits in 0..=u8::MAX {
            for signed in [false, true] {
                for samples in &payloads {
                    let component = DecodedComponent {
                        width: u32::MAX,
                        height: 0,
                        info: ComponentInfo {
                            precision,
                            signed,
                            x_subsampling: 0,
                            y_subsampling: 255,
                            x_registration: u16::MAX,
                            y_registration: 32768,
                        },
                        fraction_bits,
                        samples: samples.clone(),
                    };
                    for limit in &limits {
                        assert_eq!(
                            component.typed_samples(limit),
                            reference_decoded_typed_samples(
                                &component,
                                limit.maximum_decoded_bytes()
                            ),
                            "precision={precision} fraction={fraction_bits} signed={signed} count={} maximum={}",
                            samples.len(),
                            limit.maximum_decoded_bytes()
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn complete_decoded_typed_images_match_all_metadata_and_error_order() {
    for precision in [0, 1, 8, 38, 39, 255] {
        for fraction_bits in [0, 1, 16, 62, 63, 255] {
            for signed in [false, true] {
                for maximum in [1, 8, 15, 16, 47, 48, 64, 128] {
                    let limits = ResourceLimits::default()
                        .with_maximum_decoded_bytes(maximum)
                        .unwrap();
                    let info = ComponentInfo {
                        precision,
                        signed,
                        x_subsampling: 0,
                        y_subsampling: 255,
                        x_registration: u16::MAX,
                        y_registration: 123,
                    };
                    let image = DecodedImage {
                        width: 0,
                        height: u32::MAX,
                        x_origin: u32::MAX,
                        y_origin: 7,
                        components: vec![
                            DecodedComponent {
                                width: 7,
                                height: 0,
                                info: ComponentInfo {
                                    precision: 8,
                                    ..info
                                },
                                fraction_bits: 0,
                                samples: vec![-1],
                            },
                            DecodedComponent {
                                width: u32::MAX,
                                height: 2,
                                info,
                                fraction_bits,
                                samples: vec![0, i64::MAX],
                            },
                            DecodedComponent {
                                width: 1,
                                height: 19,
                                info,
                                fraction_bits: 255,
                                samples: vec![],
                            },
                        ],
                    };
                    assert_eq!(
                        image.typed(&limits),
                        reference_decoded_typed_image(&image, maximum)
                    );
                }
            }
        }
    }
    let limits = ResourceLimits::default()
        .with_maximum_decoded_bytes(1)
        .unwrap();
    let info = ComponentInfo {
        precision: 0,
        ..ComponentInfo::default()
    };
    let component = DecodedComponent {
        width: 0,
        height: 0,
        info,
        fraction_bits: 255,
        samples: vec![i64::MAX],
    };
    assert_eq!(
        component.typed_samples(&limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidImageGeometry
        })
    );
    let image = DecodedImage {
        width: 0,
        height: 0,
        x_origin: 9,
        y_origin: 17,
        components: vec![component],
    };
    assert_eq!(
        image.typed(&limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: 1,
            actual: 8
        })
    );
    let empty = DecodedImage {
        width: u32::MAX,
        height: 0,
        x_origin: u32::MAX,
        y_origin: 1,
        components: vec![],
    };
    assert_eq!(
        empty.typed(&limits),
        reference_decoded_typed_image(&empty, 1)
    );
}

#[test]
fn decoded_byte_validation_matches_full_native_wide_products() {
    for samples in [0, 1, 8, usize::MAX / 8, usize::MAX / 8 + 1, usize::MAX] {
        for bytes_per_sample in [0, 1, 8, u64::MAX] {
            for maximum in [1, 8, 64] {
                let limits = ResourceLimits::default()
                    .with_maximum_decoded_bytes(maximum)
                    .unwrap();
                let bytes = samples as u128 * u128::from(bytes_per_sample);
                let expected = if bytes > u128::from(u64::MAX) {
                    Err(DecodeError::MalformedInput {
                        offset: 0,
                        kind: MalformedKind::ArithmeticOverflow,
                    })
                } else if bytes > u128::from(maximum) {
                    Err(DecodeError::LimitExceeded {
                        resource: Resource::DecodedBytes,
                        limit: maximum,
                        actual: u64::try_from(bytes).unwrap(),
                    })
                } else {
                    Ok(())
                };
                assert_eq!(validate_bytes(samples, bytes_per_sample, &limits), expected);
            }
        }
    }
}

fn reference_registered(value: u32, step: u32, registration: u16) -> u32 {
    u32::try_from(
        (u128::from(value) * 65536)
            .saturating_sub(u128::from(registration))
            .div_ceil(u128::from(step) * 65536),
    )
    .unwrap()
}

#[test]
fn complete_assembly_matches_independent_registered_coordinate_images() {
    let infos = [
        ComponentInfo {
            precision: 8,
            signed: false,
            x_subsampling: 1,
            y_subsampling: 1,
            x_registration: 0,
            y_registration: 0,
        },
        ComponentInfo {
            precision: 38,
            signed: true,
            x_subsampling: 2,
            y_subsampling: 3,
            x_registration: 65535,
            y_registration: 32768,
        },
        ComponentInfo {
            precision: 0,
            signed: true,
            x_subsampling: 3,
            y_subsampling: 2,
            x_registration: 12345,
            y_registration: 65535,
        },
    ];
    let limits = ResourceLimits::default();
    for origin in 0..=2 {
        for width in 1..=5 {
            for height in 1..=4 {
                let mut size = image_size(&infos, width, height);
                size.x_origin = origin;
                size.y_origin = 2 - origin;
                for discard in 0..=2 {
                    let scale = 1 << discard;
                    let mut owned = Vec::new();
                    for (component, info) in infos.iter().enumerate() {
                        let step_x = u32::from(info.x_subsampling) * scale;
                        let step_y = u32::from(info.y_subsampling) * scale;
                        let x0 = reference_registered(size.x_origin, step_x, info.x_registration);
                        let y0 = reference_registered(size.y_origin, step_y, info.y_registration);
                        let columns = reference_registered(
                            size.x_origin + width,
                            step_x,
                            info.x_registration,
                        ) - x0;
                        let rows = reference_registered(
                            size.y_origin + height,
                            step_y,
                            info.y_registration,
                        ) - y0;
                        for y in 0..rows {
                            for x in 0..columns {
                                owned.push((
                                    u16::try_from(component).unwrap(),
                                    x,
                                    y,
                                    [i64::try_from(component).unwrap() * 10000
                                        + i64::from(y) * 100
                                        + i64::from(x)
                                        - 1000],
                                ));
                            }
                        }
                    }
                    owned.reverse();
                    let tiles: Vec<_> = owned
                        .iter()
                        .map(|(component, x, y, samples)| TileComponent {
                            component: *component,
                            x: *x,
                            y: *y,
                            width: 1,
                            height: 1,
                            fraction_bits: [0, 16, 255][usize::from(*component)],
                            samples,
                        })
                        .collect();
                    for inset in 0..=1 {
                        let region = [
                            size.x_origin + inset.min(width - 1),
                            size.y_origin,
                            size.x_origin + width,
                            size.y_origin + height,
                        ];
                        let header = (
                            region[0].div_ceil(scale),
                            region[1].div_ceil(scale),
                            region[2].div_ceil(scale),
                            region[3].div_ceil(scale),
                        );
                        let mut expected = DecodedImage {
                            width: header.2 - header.0,
                            height: header.3 - header.1,
                            x_origin: header.0,
                            y_origin: header.1,
                            components: Vec::new(),
                        };
                        let mut error = if expected.width == 0 || expected.height == 0 {
                            Some(invalid_image())
                        } else {
                            None
                        };
                        for (component, info) in infos.iter().enumerate() {
                            if error.is_some() {
                                break;
                            }
                            let step_x = u32::from(info.x_subsampling) * scale;
                            let step_y = u32::from(info.y_subsampling) * scale;
                            let x0 = reference_registered(region[0], step_x, info.x_registration);
                            let y0 = reference_registered(region[1], step_y, info.y_registration);
                            let x1 = reference_registered(region[2], step_x, info.x_registration);
                            let y1 = reference_registered(region[3], step_y, info.y_registration);
                            if x0 == x1 || y0 == y1 {
                                error = Some(DecodeError::InvalidSelection {
                                    reason: crate::SelectionError::EmptyComponentIntersection,
                                });
                                break;
                            }
                            let full_x0 = reference_registered(
                                size.x_origin, // Full-canvas origin, not the crop's origin.
                                step_x,
                                info.x_registration,
                            );
                            let full_y0 = reference_registered(
                                size.y_origin, // Full-canvas origin, not the crop's origin.
                                step_y,
                                info.y_registration,
                            );
                            let samples = (y0..y1)
                                .flat_map(|y| {
                                    (x0..x1).map(move |x| {
                                        i64::try_from(component).unwrap() * 10000
                                            + i64::from(y - full_y0) * 100
                                            + i64::from(x - full_x0)
                                            - 1000
                                    })
                                })
                                .collect();
                            expected.components.push(DecodedComponent {
                                width: x1 - x0,
                                height: y1 - y0,
                                info: *info,
                                fraction_bits: [0, 16, 255][component],
                                samples,
                            });
                        }
                        let expected = error.map_or_else(|| Ok(expected), Err);
                        assert_eq!(
                            assemble_selected_image(&size, &tiles, region, discard, &limits),
                            expected
                        );
                    }
                    if discard == 0 {
                        let mut expected = DecodedImage {
                            width,
                            height,
                            x_origin: size.x_origin,
                            y_origin: size.y_origin,
                            components: Vec::new(),
                        };
                        let mut valid = true;
                        for (component, info) in infos.iter().enumerate() {
                            let x0 = reference_registered(
                                size.x_origin,
                                u32::from(info.x_subsampling),
                                info.x_registration,
                            );
                            let y0 = reference_registered(
                                size.y_origin,
                                u32::from(info.y_subsampling),
                                info.y_registration,
                            );
                            let columns = reference_registered(
                                size.x_origin + width,
                                u32::from(info.x_subsampling),
                                info.x_registration,
                            ) - x0;
                            let rows = reference_registered(
                                size.y_origin + height,
                                u32::from(info.y_subsampling),
                                info.y_registration,
                            ) - y0;
                            valid &= columns > 0 && rows > 0;
                            let samples = (0..rows)
                                .flat_map(|y| {
                                    (0..columns).map(move |x| {
                                        i64::try_from(component).unwrap() * 10000
                                            + i64::from(y) * 100
                                            + i64::from(x)
                                            - 1000
                                    })
                                })
                                .collect();
                            expected.components.push(DecodedComponent {
                                width: columns,
                                height: rows,
                                info: *info,
                                fraction_bits: [0, 16, 255][component],
                                samples,
                            });
                        }
                        assert_eq!(
                            assemble_image(&size, &tiles, &limits),
                            if valid {
                                Ok(expected)
                            } else {
                                Err(invalid_image())
                            }
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn assembly_preserves_error_order_and_selected_only_sample_coverage() {
    let info = ComponentInfo {
        precision: 8,
        signed: false,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let limits = ResourceLimits::default();
    let small = limits.with_maximum_decoded_bytes(1).unwrap();
    let size = image_size(&[info], 1, 1);
    let tile = TileComponent {
        component: 0,
        x: 0,
        y: 0,
        width: 1,
        height: 1,
        fraction_bits: 255,
        samples: &[42],
    };
    let budget = DecodeError::LimitExceeded {
        resource: Resource::DecodedBytes,
        limit: 1,
        actual: 8,
    };
    assert_eq!(
        assemble_image(&size, &[TileComponent { width: 0, ..tile }], &small),
        Err(budget)
    );
    let mut excessive_count = size;
    excessive_count.components = u16::MAX;
    assert_eq!(
        assemble_image(&excessive_count, &[tile], &small),
        Err(budget)
    );
    let mut shifted = size;
    shifted.x_origin = 1;
    assert_eq!(
        assemble_selected_image(&shifted, &[tile], [0, 0, 1, 1], 0, &small),
        Err(budget)
    );
    assert_eq!(
        assemble_selected_image(&shifted, &[tile], [0, 0, 1, 1], 0, &limits),
        Err(arithmetic_overflow())
    );
    let large_tile = TileComponent {
        width: 4,
        height: 4,
        fraction_bits: 16,
        ..tile
    };
    let selected = assemble_selected_image(
        &image_size(&[info], 4, 4),
        &[large_tile],
        [0, 0, 1, 1],
        0,
        &limits,
    )
    .unwrap();
    assert_eq!(
        selected,
        DecodedImage {
            width: 1,
            height: 1,
            x_origin: 0,
            y_origin: 0,
            components: vec![DecodedComponent {
                width: 1,
                height: 1,
                info,
                fraction_bits: 16,
                samples: vec![42]
            }]
        }
    );
    assert_eq!(
        assemble_image(&image_size(&[info], 4, 4), &[large_tile], &limits),
        Err(invalid_image())
    );
    let outside = TileComponent {
        x: 2,
        width: 0,
        height: 0,
        samples: &[],
        ..tile
    };
    assert_eq!(
        assemble_selected_image(&size, &[tile, outside], [0, 0, 1, 1], 0, &limits)
            .unwrap()
            .components[0]
            .samples,
        [42]
    );
    assert_eq!(
        assemble_selected_image(
            &size,
            &[
                tile,
                TileComponent {
                    fraction_bits: 0,
                    ..outside
                }
            ],
            [0, 0, 1, 1],
            0,
            &limits
        ),
        Err(invalid_image())
    );
    let overflowing = TileComponent {
        x: u32::MAX,
        width: 1,
        ..outside
    };
    assert_eq!(
        assemble_selected_image(&size, &[tile, overflowing], [0, 0, 1, 1], 0, &limits),
        Err(arithmetic_overflow())
    );
    assert!(
        assemble_selected_image(
            &size,
            &[
                tile,
                TileComponent {
                    component: 1,
                    ..overflowing
                }
            ],
            [0, 0, 1, 1],
            0,
            &limits
        )
        .is_ok()
    );
    assert_eq!(
        assemble_selected_image(&size, &[], [0, 0, 1, 1], 0, &limits),
        Err(DecodeError::InvalidSelection {
            reason: crate::SelectionError::RegionOutsideSelectedTiles
        })
    );
    assert_eq!(assemble_image(&size, &[], &limits), Err(invalid_image()));
    let empty = image_size(&[], 0, 0);
    assert_eq!(
        assemble_image(&empty, &[], &limits),
        Ok(DecodedImage {
            width: 0,
            height: 0,
            x_origin: 0,
            y_origin: 0,
            components: vec![]
        })
    );
    let mut overflow = empty;
    overflow.width = u32::MAX;
    overflow.x_origin = 1;
    assert_eq!(
        assemble_image(&overflow, &[], &limits),
        Err(arithmetic_overflow())
    );
    assert_eq!(
        assemble_selected_image(&size, &[tile], [0, 0, 1, 1], 32, &limits),
        Err(invalid_image())
    );
}

#[test]
fn assembly_byte_charge_matches_wide_integer_complete_counter_state() {
    for count in [0, 1, 7, 8, usize::MAX / 8, usize::MAX / 8 + 1, usize::MAX] {
        for before in [0, 1, u64::MAX - 8, u64::MAX - 7, u64::MAX] {
            for maximum in [0, 1, 8, u64::MAX - 1, u64::MAX] {
                let wide = count as u128 * 8 + u128::from(before);
                let expected =
                    if count as u128 * 8 > u128::from(u64::MAX) || wide > u128::from(u64::MAX) {
                        (Err(arithmetic_overflow()), before)
                    } else {
                        let next = u64::try_from(wide).unwrap();
                        (
                            if next > maximum {
                                Err(DecodeError::LimitExceeded {
                                    resource: Resource::DecodedBytes,
                                    limit: maximum,
                                    actual: next,
                                })
                            } else {
                                Ok(())
                            },
                            next,
                        )
                    };
                let mut actual = before;
                assert_eq!(
                    (charge_assembly_bytes(count, &mut actual, maximum), actual),
                    expected
                );
            }
        }
    }
}

fn reference_ratio(numerator: i128, denominator: i128) -> Result<i128, DecodeError> {
    if denominator <= 0 || numerator == i128::MIN {
        return Err(arithmetic_overflow());
    }
    let adjusted = numerator.unsigned_abs() + denominator as u128 / 2;
    if adjusted > i128::MAX as u128 {
        return Err(arithmetic_overflow());
    }
    let rounded = i128::try_from(adjusted / denominator as u128).unwrap();
    Ok(if numerator < 0 { -rounded } else { rounded })
}

fn reference_product(left: i128, right: i128) -> Result<i128, DecodeError> {
    let negative = (left < 0) != (right < 0);
    let magnitude = left
        .unsigned_abs()
        .checked_mul(right.unsigned_abs())
        .ok_or_else(arithmetic_overflow)?;
    if negative && magnitude == 1_u128 << 127 {
        Ok(i128::MIN)
    } else {
        let product = i128::try_from(magnitude).map_err(|_| arithmetic_overflow())?;
        Ok(if negative { -product } else { product })
    }
}

fn reference_nlt_mul(left: i128, right: i128) -> Result<i128, DecodeError> {
    reference_product(left, right).and_then(|product| reference_ratio(product, 1_i128 << 32))
}

fn reference_nlt_div(left: i128, right: i128) -> Result<i128, DecodeError> {
    if right <= 0 {
        return Err(invalid_transform());
    }
    reference_product(left, 1_i128 << 32).map(|product| product / right)
}

fn reference_nlt_normalize(value: i128) -> Result<(i128, i32), DecodeError> {
    if value <= 0 {
        return Err(arithmetic_overflow());
    }
    let scale = i32::try_from(127 - value.leading_zeros()).unwrap() - 32;
    let normalized = if scale >= 0 {
        value >> u32::try_from(scale).unwrap()
    } else {
        value << scale.unsigned_abs()
    };
    Ok((normalized, scale))
}

fn reference_nlt_ln_series(initial: i128, squared: i128, scale: i32) -> Result<i128, DecodeError> {
    let (sum, _) = (0_u32..20).try_fold((0_i128, initial), |(sum, term), iteration| {
        let sum = sum
            .checked_add(term / i128::from(2 * iteration + 1))
            .ok_or_else(arithmetic_overflow)?;
        let term = reference_nlt_mul(term, squared)?;
        Ok::<_, DecodeError>((sum, term))
    })?;
    let doubled = reference_product(sum, 2)?;
    let shifted = reference_product(i128::from(scale), 2_977_044_471)?;
    doubled.checked_add(shifted).ok_or_else(arithmetic_overflow)
}

fn reference_nlt_ln(value: i128) -> Result<i128, DecodeError> {
    let (value, scale) = reference_nlt_normalize(value)?;
    let one = 1_i128 << 32;
    let z = reference_nlt_div(value - one, value + one)?;
    reference_nlt_ln_series(z, reference_nlt_mul(z, z)?, scale)
}

fn reference_nlt_exp_series(remainder: i128) -> Result<i128, DecodeError> {
    let one = 1_i128 << 32;
    (1_u32..=24)
        .try_fold((one, one), |(sum, term), iteration| {
            let term = reference_nlt_mul(term, remainder)? / i128::from(iteration);
            let sum = sum.checked_add(term).ok_or_else(arithmetic_overflow)?;
            Ok::<_, DecodeError>((sum, term))
        })
        .map(|(sum, _)| sum)
}

fn reference_nlt_exp(value: i128) -> Result<i128, DecodeError> {
    let scale = value / 2_977_044_471;
    if !(-62..=62).contains(&scale) {
        return Err(invalid_transform());
    }
    let sum = reference_nlt_exp_series(value - scale * 2_977_044_471)?;
    if scale < 0 {
        Ok(sum >> u32::try_from(-scale).unwrap())
    } else {
        let shift = u32::try_from(scale).unwrap();
        if sum < 0 || sum > (i128::MAX >> shift) {
            Err(arithmetic_overflow())
        } else {
            Ok(sum << shift)
        }
    }
}

fn reference_nlt_reciprocal(base: i128, exponent: i128) -> Result<i128, DecodeError> {
    if base <= 0 || exponent <= 0 {
        return Err(invalid_transform());
    }
    reference_nlt_exp(reference_nlt_div(reference_nlt_ln(base)?, exponent)?)
}

fn reference_nlt_gamma_parameter(raw: u32) -> i128 {
    let integer = u128::from(raw / 65_536) * (1_u128 << 32);
    let fraction = u128::from(raw % 65_536) * (1_u128 << 32) / 65_535;
    i128::try_from(integer + fraction).unwrap()
}

fn reference_nlt_gamma_curve(
    normalized: i128,
    exponent: i128,
    slope: i128,
    threshold: i128,
    a: i128,
    b: i128,
) -> Result<i128, DecodeError> {
    let negative_threshold = threshold.checked_neg().ok_or_else(arithmetic_overflow)?;
    let side = if normalized < negative_threshold {
        -1
    } else if normalized <= threshold {
        0
    } else {
        1
    };
    if side == 0 {
        return reference_nlt_div(normalized, slope);
    }
    let magnitude = if side < 0 {
        normalized.checked_neg().ok_or_else(arithmetic_overflow)?
    } else {
        normalized
    };
    let base = reference_nlt_div(magnitude.checked_add(b).ok_or_else(arithmetic_overflow)?, a)?;
    let value = reference_nlt_reciprocal(base, exponent)?;
    if side < 0 {
        value.checked_neg().ok_or_else(arithmetic_overflow)
    } else {
        Ok(value)
    }
}

fn reference_nlt_gamma(
    source: i128,
    info: ComponentInfo,
    transform: &NonlinearPointTransform,
) -> Result<i128, DecodeError> {
    if info.precision == 0 || info.precision > 38 {
        return Err(invalid_image());
    }
    let [exponent, slope, threshold, a, b] = transform
        .gamma_parameters()
        .ok_or_else(invalid_transform)?
        .map(reference_nlt_gamma_parameter);
    if exponent <= 0 || slope <= 0 || a <= 0 {
        return Err(invalid_transform());
    }
    let source_exponent = info.precision - u8::from(info.signed);
    let source_scale = 2_i128.pow(u32::from(source_exponent)) - 1;
    if transform.precision() == 0 {
        return Err(invalid_transform());
    }
    let target_exponent = transform.precision() - u8::from(transform.signed());
    if target_exponent > 38 {
        return Err(arithmetic_overflow());
    }
    let target_scale = 2_i128.pow(u32::from(target_exponent)) - 1;
    if source_scale <= 0 || target_scale <= 0 {
        return Err(invalid_transform());
    }
    let normalized = reference_product(source, 1_i128 << 32)? / source_scale;
    let decoded = reference_nlt_gamma_curve(normalized, exponent, slope, threshold, a, b)?;
    reference_ratio(reference_product(decoded, target_scale)?, 1_i128 << 32)
}

fn reference_nlt_inverse(
    source: i128,
    info: ComponentInfo,
    transform: &NonlinearPointTransform,
) -> Result<i128, DecodeError> {
    let precision = transform.precision();
    if precision == 0 || precision > 38 {
        return Err(invalid_image());
    }
    let half = 2_i128.pow(u32::from(precision - 1));
    let (minimum, maximum) = if transform.signed() {
        (-half, half - 1)
    } else {
        (0, 2 * half - 1)
    };
    let value = match transform.transform_type() {
        0 | 3 => {
            if info.precision != precision || info.signed != transform.signed() {
                return Err(invalid_transform());
            }
            if transform.transform_type() == 3 && source < 0 {
                source
                    .checked_neg()
                    .and_then(|value| value.checked_sub(half + 1))
                    .ok_or_else(arithmetic_overflow)?
            } else {
                source
            }
        }
        1 => reference_nlt_gamma(source, info, transform)?,
        2 | 4 => inverse_nlt_lut_sample(source, info, transform)?,
        _ => return Err(invalid_transform()),
    };
    if !(minimum..=maximum).contains(&value) {
        Err(invalid_transform())
    } else {
        Ok(value)
    }
}

#[test]
fn actual_complete_nonlinear_samples_derive_parameters_gamma_dispatch_and_target_errors() {
    let mut parameter_cases = 0;
    for high in [0_u32, 1, 32_767, 32_768, 65_534, 65_535] {
        for low in 0..=u16::MAX {
            let raw = (high << 16) | u32::from(low);
            assert_eq!(
                nlt_gamma_parameter(raw),
                Ok(reference_nlt_gamma_parameter(raw))
            );
            parameter_cases += 1;
        }
    }
    assert_eq!(parameter_cases, 393_216);
    assert_eq!(nlt_gamma_parameter(0xffff), nlt_gamma_parameter(0x1_0000));
    let one = 1_u32 << 16;
    let parameters = [
        Some([one, one, one, one, 0]),
        Some([2 * one, one, 0, one, 0]),
        Some([one, 2 * one, 0x8000, one, 0xffff]),
        Some([0, one, one, one, 0]),
        Some([one, 0, one, one, 0]),
        Some([one, one, one, 0, 0]),
        Some([u32::MAX; 5]),
        None,
    ];
    let precisions = [0, 1, 2, 8, 38, 39, u8::MAX];
    let sources = [
        i128::MIN,
        -(1_i128 << 95),
        -(1_i128 << 38),
        -129,
        -128,
        -1,
        0,
        1,
        127,
        128,
        255,
        (1_i128 << 38) - 1,
        i128::MAX,
    ];
    let mut gamma_cases = 0;
    let mut scalar_cases = 0;
    for precision in precisions {
        for signed in [false, true] {
            for parameters in parameters {
                let transform = match parameters {
                    Some(parameters) => {
                        NonlinearPointTransform::gamma_for_test(precision, signed, parameters)
                    }
                    None => NonlinearPointTransform::for_test(
                        precision,
                        signed,
                        1,
                        None,
                        None,
                        vec![], // No explicit gamma parameters.
                    ),
                };
                for source_precision in precisions {
                    for source_signed in [false, true] {
                        let info = ComponentInfo {
                            precision: source_precision,
                            signed: source_signed,
                            x_subsampling: 0,
                            y_subsampling: u8::MAX,
                            x_registration: u16::MAX,
                            y_registration: 17,
                        };
                        for source in sources {
                            assert_eq!(
                                inverse_nlt_gamma_sample(source, info, &transform),
                                reference_nlt_gamma(source, info, &transform)
                            );
                            assert_eq!(
                                inverse_nlt_sample(source, info, &transform),
                                reference_nlt_inverse(source, info, &transform)
                            );
                            gamma_cases += 1;
                            scalar_cases += 1;
                        }
                    }
                }
            }
            for kind in [0, 2, 3, 4, u8::MAX] {
                for minimum in [None, Some(0)] {
                    let transform = NonlinearPointTransform::for_test(
                        precision,
                        signed,
                        kind,
                        minimum,
                        Some(u32::MAX),
                        vec![0, 128, 255],
                    );
                    for source_precision in precisions {
                        for source_signed in [false, true] {
                            let info = ComponentInfo {
                                precision: source_precision,
                                signed: source_signed,
                                x_subsampling: 0,
                                y_subsampling: u8::MAX,
                                x_registration: u16::MAX,
                                y_registration: 17,
                            };
                            for source in sources {
                                assert_eq!(
                                    inverse_nlt_sample(source, info, &transform),
                                    reference_nlt_inverse(source, info, &transform)
                                );
                                scalar_cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(gamma_cases, 20_384);
    assert_eq!(scalar_cases, 45_864);
    for normalized in [
        i128::MIN,
        -(1_i128 << 32),
        -1,
        0,
        1,
        1_i128 << 32,
        i128::MAX,
    ] {
        let one = 1_i128 << 32;
        for (exponent, slope, threshold, a, b) in [
            (one, one, one, one, 0),
            (one, one, 0, one, 0),
            (0, one, one, one, 0),
            (one, 0, one, one, 0),
            (one, one, i128::MIN, one, 0),
            (one, one, i128::MAX, i128::MIN, i128::MAX),
            (i128::MAX, i128::MAX, -1, 1, i128::MAX),
        ] {
            assert_eq!(
                nlt_gamma_curve(normalized, exponent, slope, threshold, a, b),
                reference_nlt_gamma_curve(normalized, exponent, slope, threshold, a, b)
            );
        }
    }
}

#[test]
fn actual_nonlinear_log_exp_preserve_normalization_bounded_series_and_raw_error_frontiers() {
    let mut normalizations = 0;
    for bit in 0..127 {
        let power = 1_i128 << bit;
        for positive in [power - 1, power, power + 1] {
            for value in [positive, -positive] {
                assert_eq!(nlt_ln_normalize(value), reference_nlt_normalize(value));
                assert_eq!(nlt_fixed_ln_q32(value), reference_nlt_ln(value));
                normalizations += 1;
            }
        }
    }
    assert_eq!(normalizations, 762);
    for value in [i128::MIN, i128::MIN + 1, i128::MAX - 1, i128::MAX] {
        assert_eq!(nlt_ln_normalize(value), reference_nlt_normalize(value));
        assert_eq!(nlt_fixed_ln_q32(value), reference_nlt_ln(value));
        assert_eq!(nlt_fixed_exp_q32(value), reference_nlt_exp(value));
    }
    let mut exponentials = 0;
    for scale in -64_i128..=64 {
        for offset in [-1, 0, 1, -(2_977_044_471_i128 / 2), 2_977_044_471_i128 / 2] {
            let value = scale * 2_977_044_471 + offset;
            assert_eq!(nlt_fixed_exp_q32(value), reference_nlt_exp(value));
            exponentials += 1;
        }
    }
    assert_eq!(exponentials, 645);
    let terms = [
        i128::MIN,
        i128::MIN + 1,
        -(1_i128 << 32),
        -1,
        0,
        1,
        1_i128 << 32,
        i128::MAX / 2,
        i128::MAX,
    ];
    let mut series = 0;
    for term in terms {
        assert_eq!(nlt_exp_series(term), reference_nlt_exp_series(term));
        for squared in terms {
            for scale in [i32::MIN, -1, 0, 1, i32::MAX] {
                assert_eq!(
                    nlt_ln_series(term, squared, scale),
                    reference_nlt_ln_series(term, squared, scale)
                );
                series += 1;
            }
        }
    }
    assert_eq!(series, 405);
    let bases = [
        -1,
        0,
        1,
        1_i128 << 30,
        1_i128 << 31,
        1_i128 << 32,
        1_i128 << 33,
        1_i128 << 38,
        i128::MIN,
        i128::MAX,
    ];
    let mut reciprocals = 0;
    for base in bases {
        for exponent in bases {
            assert_eq!(
                nlt_fixed_pow_reciprocal_q32(base, exponent),
                reference_nlt_reciprocal(base, exponent)
            );
            reciprocals += 1;
        }
    }
    assert_eq!(reciprocals, 100);
    assert_eq!(nlt_fixed_ln_q32(1_i128 << 32), Ok(0));
    assert_eq!(nlt_fixed_ln_q32(1_i128 << 33), Ok(2_977_044_471));
    assert_eq!(nlt_fixed_ln_q32(1_i128 << 31), Ok(-2_977_044_471));
    assert_eq!(nlt_fixed_exp_q32(0), Ok(1_i128 << 32));
    assert_eq!(nlt_fixed_exp_q32(2_977_044_471), Ok(1_i128 << 33));
    assert_eq!(nlt_fixed_exp_q32(-2_977_044_471), Ok(1_i128 << 31));
    assert_eq!(nlt_ln_normalize(0), Err(arithmetic_overflow()));
}

#[test]
fn actual_nonlinear_arithmetic_preserves_checked_i128_rounding_q32_and_power_boundaries() {
    let mut small_cases = 0;
    for numerator in -257..=257 {
        for denominator in -3..=65 {
            assert_eq!(
                nlt_round_ratio(numerator, denominator),
                reference_ratio(numerator, denominator)
            );
            small_cases += 1;
        }
    }
    assert_eq!(small_cases, 35_535);
    let values = [
        i128::MIN,
        i128::MIN + 1,
        i128::MIN / 2,
        i128::MIN / 2 + 1,
        -(1_i128 << 96),
        -(1_i128 << 64),
        -(1_i128 << 32) - 1,
        -(1_i128 << 32),
        -(1_i128 << 32) + 1,
        -65_536,
        -65,
        -2,
        -1,
        0,
        1,
        2,
        65,
        65_536,
        (1_i128 << 32) - 1,
        1_i128 << 32,
        (1_i128 << 32) + 1,
        1_i128 << 64,
        1_i128 << 96,
        i128::MAX / 2,
        i128::MAX / 2 + 1,
        i128::MAX - 1,
        i128::MAX,
    ];
    let mut edge_cases = 0;
    for left in values {
        for right in values {
            assert_eq!(nlt_round_ratio(left, right), reference_ratio(left, right));
            assert_eq!(
                nlt_fixed_mul_q32(left, right),
                reference_product(left, right)
                    .and_then(|product| reference_ratio(product, 1_i128 << 32))
            );
            let division = if right <= 0 {
                Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::InvalidTransform,
                })
            } else {
                reference_product(left, 1_i128 << 32).map(|product| product / right)
            };
            assert_eq!(nlt_fixed_div_q32(left, right), division);
            edge_cases += 1;
        }
    }
    assert_eq!(edge_cases, 729);
    for exponent in 0..=u8::MAX {
        let expected = if exponent <= 38 {
            Ok(2_i128.pow(u32::from(exponent)))
        } else {
            Err(arithmetic_overflow())
        };
        assert_eq!(nlt_power_of_two(exponent), expected);
    }
    assert_eq!(nlt_round_ratio(1, 2), Ok(1));
    assert_eq!(nlt_round_ratio(-1, 2), Ok(-1));
    assert_eq!(nlt_fixed_div_q32(-1, 3), Ok(-1_431_655_765));
    assert_eq!(
        nlt_fixed_mul_q32(i128::MAX, 1_i128 << 32),
        Err(arithmetic_overflow())
    );
}

#[test]
fn sarah_engineering_nlt_lut_reaches_both_unsigned_rank_endpoints() {
    let mut contexts = 0;
    for precision in [1_u8, 2, 4, 8] {
        let maximum = (1_i128 << precision) - 1;
        for source_signed in [false, true] {
            for target_signed in [false, true] {
                for descending in [false, true] {
                    let info = ComponentInfo {
                        precision,
                        signed: source_signed,
                        x_subsampling: 1,
                        y_subsampling: 1,
                        x_registration: 0,
                        y_registration: 0,
                    };
                    let points = if descending {
                        vec![255, 0]
                    } else {
                        vec![0, 255]
                    };
                    let transform = NonlinearPointTransform::for_test(
                        8,
                        target_signed,
                        2,
                        Some(0),
                        Some(u32::MAX),
                        points,
                    );
                    for rank in 0..=maximum {
                        let source = rank
                            - if source_signed {
                                1_i128 << (precision - 1)
                            } else {
                                0
                            };
                        let interpolated = (rank * 255 + maximum / 2) / maximum;
                        let raw = if descending {
                            255 - interpolated
                        } else {
                            interpolated
                        };
                        let expected = raw - if target_signed { 128 } else { 0 };
                        assert_eq!(
                            inverse_nlt_lut_sample(source, info, &transform),
                            Ok(expected),
                            "precision={precision} source_signed={source_signed} target_signed={target_signed} descending={descending} rank={rank}"
                        );
                        assert_eq!(inverse_nlt_sample(source, info, &transform), Ok(expected));
                        contexts += 1;
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 2_224);
}

#[test]
fn actual_nonlinear_lut_derives_checked_interpolation_and_raw_type4_samples() {
    fn reference(
        source: i128,
        info: ComponentInfo,
        transform: &NonlinearPointTransform,
    ) -> Result<i128, DecodeError> {
        let precision = transform.precision();
        if precision == 0 || precision > 38 {
            return Err(invalid_image());
        }
        let minimum = transform.d_min().ok_or_else(invalid_transform)?;
        let maximum = transform.d_max().ok_or_else(invalid_transform)?;
        let points = transform.points();
        if points.len() < 2 || minimum >= maximum {
            return Err(invalid_transform());
        }
        if info.precision == 0 || info.precision > 38 {
            return Err(invalid_image());
        }
        let scale = 1_u128 << info.precision;
        let offset = if info.signed {
            i128::try_from(scale / 2).unwrap()
        } else {
            0
        };
        let nominal = source.checked_add(offset).ok_or_else(arithmetic_overflow)?;
        if nominal < 0 || nominal as u128 >= scale {
            return Err(invalid_image());
        }
        let low = u128::from(minimum) * (scale - 1);
        let high = u128::from(maximum) * (scale - 1);
        let coordinate = (nominal as u128 * u128::from(u32::MAX)).clamp(low, high);
        let denominator = high - low;
        let position = (coordinate - low) * (points.len() - 1) as u128;
        let index = usize::try_from(position / denominator).unwrap();
        let remainder = position % denominator;
        let raw = if index >= points.len() - 1 {
            u128::from(*points.last().unwrap())
        } else {
            let weighted = u128::from(points[index]) * (denominator - remainder)
                + u128::from(points[index + 1]) * remainder;
            (weighted + denominator / 2) / denominator
        };
        let half = 1_i128 << (precision - 1);
        let value = i128::try_from(raw).unwrap() - if transform.signed() { half } else { 0 };
        Ok(if transform.transform_type() == 4 && value < 0 {
            -value - (half + 1)
        } else {
            value
        })
    }

    let tables = [
        vec![],
        vec![0],
        vec![0, 255],
        vec![255, 0],
        vec![0, u32::MAX],
        vec![0, 128, 255],
        vec![u32::MAX, 0, 17],
    ];
    let windows = [
        (None, None),
        (Some(0), None),
        (None, Some(u32::MAX)),
        (Some(0), Some(0)),
        (Some(u32::MAX), Some(0)),
        (Some(0), Some(u32::MAX)),
        (Some(1), Some(2)),
        (Some(0x8000_0000), Some(u32::MAX)),
    ];
    let sources = [
        i128::MIN,
        -(1_i128 << 38),
        -129,
        -128,
        -1,
        0,
        1,
        127,
        128,
        255,
        256,
        (1_i128 << 38) - 1,
        i128::MAX,
    ];
    let mut cases = 0;
    let mut successes = 0;
    for kind in [2, 4, u8::MAX] {
        for precision in [0, 1, 8, 38, 39, u8::MAX] {
            for signed in [false, true] {
                for (minimum, maximum) in windows {
                    for points in &tables {
                        let transform = NonlinearPointTransform::for_test(
                            precision,
                            signed,
                            kind,
                            minimum,
                            maximum,
                            points.clone(),
                        );
                        for source_precision in [0, 1, 8, 38, 39, u8::MAX] {
                            for source_signed in [false, true] {
                                let info = ComponentInfo {
                                    precision: source_precision,
                                    signed: source_signed,
                                    x_subsampling: 0,
                                    y_subsampling: u8::MAX,
                                    x_registration: u16::MAX,
                                    y_registration: 17,
                                };
                                for source in sources {
                                    let expected = reference(source, info, &transform);
                                    assert_eq!(
                                        inverse_nlt_lut_sample(source, info, &transform),
                                        expected
                                    );
                                    successes += usize::from(expected.is_ok());
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 314_496);
    assert!(successes > 1_000);
    assert_eq!(nlt_lut_position(&[], 1, 0, 0, 1), Err(invalid_image()));
    assert_eq!(nlt_lut_position(&[17], 256, 255, 0, u32::MAX), Ok(17));
    assert_eq!(
        nlt_lut_position(&[0, 1], i128::MAX, i128::MAX, 0, 1),
        Err(arithmetic_overflow())
    );
    assert_eq!(
        nlt_lut_position(&[0, 1], 0, 0, 0, 1),
        Err(arithmetic_overflow())
    );
    assert_eq!(nlt_lut_position(&[0, 1], -1, 0, 0, 1), Ok(1));
    assert_eq!(
        nlt_lut_coordinates(1_i128 << 64, (1_i128 << 64) - 1, 0, u32::MAX, usize::MAX),
        Err(arithmetic_overflow())
    );
    if usize::BITS >= 64 {
        assert_eq!(
            nlt_lut_coordinates(1_i128 << 38, (1_i128 << 38) - 1, 0, u32::MAX, usize::MAX),
            Err(arithmetic_overflow())
        );
    }
    for numerator in [i128::MIN, -i128::MAX, -17, -1, 0, 1, 17, i128::MAX] {
        for denominator in [-1, 0, 1, 3, -3, i128::MAX, i128::MIN] {
            let expected = if denominator == 0 || (numerator == i128::MIN && denominator == -1) {
                Err(arithmetic_overflow())
            } else {
                Ok(numerator % denominator)
            };
            assert_eq!(nlt_checked_rem(numerator, denominator), expected);
        }
    }
    for (left, right, denominator, remainder, expected) in [
        (0, 255, 3, 1, Ok(85)),
        (255, 0, 3, 2, Ok(85)),
        (1, 0, 2, 1, Ok(1)),
        (-1, 0, 2, 1, Ok(-1)),
        (i128::MAX, i128::MAX, 1, 0, Ok(i128::MAX)),
        (i128::MIN, i128::MIN, 1, 0, Err(arithmetic_overflow())),
        (i128::MAX, i128::MAX, 2, 0, Err(arithmetic_overflow())),
        (i128::MAX, i128::MIN, 0, 0, Err(arithmetic_overflow())),
        (0, i128::MAX, 1, 2, Err(arithmetic_overflow())),
        (1, 2, -1, 0, Err(arithmetic_overflow())),
    ] {
        assert_eq!(
            nlt_lut_interpolate_values(left, right, denominator, remainder),
            expected
        );
    }
}

#[test]
fn applies_binary_complement_nlt_inverse() {
    let info = ComponentInfo {
        precision: 8,
        signed: true,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let component =
        TypedComponent::from_parts(4, 1, info, TypedSamples::Signed(vec![-128, -64, -1, 7]));
    let mut image =
        TypedImage::from_components(4, 1, vec![component], &ResourceLimits::default()).unwrap();
    let transform = NonlinearPointTransform::for_test(8, true, 3, None, None, Vec::new());
    let extensions = Part2Extensions::with_nonlinear_transform_for_test(transform);
    image
        .apply_nonlinear_transforms(&extensions, &ResourceLimits::default())
        .unwrap();
    assert_eq!(
        image.component(0).unwrap().samples(),
        &TypedSamples::Signed(vec![-1, -65, -128, 7])
    );
}

#[test]
fn applies_lut_nlt_inverse_with_integer_interpolation() {
    let info = ComponentInfo {
        precision: 2,
        signed: false,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let component =
        TypedComponent::from_parts(4, 1, info, TypedSamples::Unsigned(vec![0, 1, 2, 3]));
    let mut image =
        TypedImage::from_components(4, 1, vec![component], &ResourceLimits::default()).unwrap();
    let transform =
        NonlinearPointTransform::for_test(4, false, 2, Some(0), Some(u32::MAX), vec![0, 15]);
    let extensions = Part2Extensions::with_nonlinear_transform_for_test(transform);
    image
        .apply_nonlinear_transforms(&extensions, &ResourceLimits::default())
        .unwrap();
    assert_eq!(
        image.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(vec![0, 5, 10, 15])
    );
    assert_eq!(image.component(0).unwrap().info().precision, 4);
}

#[test]
fn applies_gamma_nlt_inverse_with_fixed_point_parameters() {
    let info = ComponentInfo {
        precision: 8,
        signed: false,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let component =
        TypedComponent::from_parts(3, 1, info, TypedSamples::Unsigned(vec![0, 64, 255]));
    let mut image =
        TypedImage::from_components(3, 1, vec![component], &ResourceLimits::default()).unwrap();
    let one = 1_u32 << 16;
    let transform = NonlinearPointTransform::gamma_for_test(8, false, [one, one, one, one, 0]);
    let extensions = Part2Extensions::with_nonlinear_transform_for_test(transform);
    image
        .apply_nonlinear_transforms(&extensions, &ResourceLimits::default())
        .unwrap();
    assert_eq!(
        image.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(vec![0, 64, 255])
    );
}

#[test]
fn actual_nonlinear_image_mutation_preserves_every_owner_field_and_failure_prefix() {
    use std::collections::{BTreeMap, btree_map::Entry};

    fn source(case: usize) -> TypedImage {
        let count = match case {
            0 => 0,
            1 | 4 | 7 => 1,
            3 => 3,
            _ => 2,
        };
        let (width, height) = match case {
            5 => (0, 2),
            6 => (3, 1),
            _ => (2, 2),
        };
        let components = (0..count)
            .map(|index| {
                let info = ComponentInfo {
                    precision: if case == 7 {
                        0
                    } else if case == 11 {
                        38
                    } else {
                        8
                    },
                    signed: (index % 2 != 0) != (case == 9),
                    x_subsampling: 0,
                    y_subsampling: u8::MAX,
                    x_registration: u16::MAX,
                    y_registration: 17,
                };
                let samples = if case == 4 {
                    TypedSamples::Signed(vec![])
                } else if case == 8 {
                    TypedSamples::Unsigned(vec![u64::MAX; 4])
                } else if case == 6 {
                    TypedSamples::Unsigned(vec![0, 128, 255])
                } else if index % 2 == 0 {
                    TypedSamples::Unsigned(vec![0, 1, 127, 255])
                } else {
                    TypedSamples::Signed(vec![-128, -1, 0, 127])
                };
                let mut component = TypedComponent::from_parts(width, height, info, samples);
                component.add_channel_definition(ChannelDefinition::new(
                    ChannelType::Opacity,
                    ChannelAssociation::Color(u16::MAX),
                ));
                component
            })
            .collect();
        TypedImage::for_test(if case == 10 { 0 } else { 4 }, 2, u32::MAX, 17, components)
    }

    fn reference(
        image: &mut TypedImage,
        regions: &[NonlinearRegion<'_>],
        limits: &ResourceLimits,
    ) -> Result<(), DecodeError> {
        let mut work = 0_u64;
        for (number, component) in image.components.iter_mut().enumerate() {
            let number = u16::try_from(number).map_err(|_| arithmetic_overflow())?;
            let count = match &component.samples {
                TypedSamples::Signed(values) => values.len(),
                TypedSamples::Unsigned(values) => values.len(),
            };
            let mut values = BTreeMap::new();
            let mut target = None;
            for region in regions.iter().filter(|region| region.component == number) {
                if region.x0 >= region.x1
                    || region.y0 >= region.y1
                    || region.x1 > component.width
                    || region.y1 > component.height
                {
                    return Err(invalid_image());
                }
                let descriptor = (region.transform.precision(), region.transform.signed());
                if target.is_some_and(|previous| previous != descriptor) {
                    return Err(invalid_transform());
                }
                target = Some(descriptor);
                for (y, x) in
                    (region.y0..region.y1).flat_map(|y| (region.x0..region.x1).map(move |x| (y, x)))
                {
                    let offset = u64::from(y) * u64::from(component.width) + u64::from(x);
                    let offset = usize::try_from(offset).map_err(|_| arithmetic_overflow())?;
                    if offset >= count {
                        return Err(invalid_image());
                    }
                    let entry = match values.entry(offset) {
                        Entry::Occupied(_) => return Err(invalid_transform()),
                        Entry::Vacant(entry) => entry,
                    };
                    let source = match &component.samples {
                        TypedSamples::Signed(values) => i128::from(values[offset]),
                        TypedSamples::Unsigned(values) => i128::from(values[offset]),
                    };
                    entry.insert(reference_nlt_inverse(
                        source,
                        component.info,
                        region.transform,
                    )?);
                    let next = u128::from(work) + 1;
                    if next > u128::from(u64::MAX) {
                        return Err(arithmetic_overflow());
                    }
                    work = next as u64;
                    if work > limits.maximum_work_units() {
                        return Err(DecodeError::LimitExceeded {
                            resource: Resource::WorkUnits,
                            limit: limits.maximum_work_units(),
                            actual: work,
                        });
                    }
                }
            }
            if let Some((precision, signed)) = target {
                let bytes = count as u128 * 8;
                if bytes > u128::from(u64::MAX) {
                    return Err(arithmetic_overflow());
                }
                if bytes > u128::from(limits.maximum_decoded_bytes()) {
                    return Err(DecodeError::LimitExceeded {
                        resource: Resource::DecodedBytes,
                        limit: limits.maximum_decoded_bytes(),
                        actual: bytes as u64,
                    });
                }
                component.samples = if signed {
                    let samples = (0..count)
                        .map(|position| {
                            let value = *values.get(&position).ok_or_else(invalid_image)?;
                            if value < i128::from(i64::MIN) || value > i128::from(i64::MAX) {
                                return Err(invalid_image());
                            }
                            Ok(value as i64)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    TypedSamples::Signed(samples)
                } else {
                    let samples = (0..count)
                        .map(|position| {
                            let value = *values.get(&position).ok_or_else(invalid_image)?;
                            if value < 0 || value > i128::from(u64::MAX) {
                                return Err(invalid_image());
                            }
                            Ok(value as u64)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    TypedSamples::Unsigned(samples)
                };
                component.info.precision = precision;
                component.info.signed = signed;
            }
        }
        Ok(())
    }

    fn region(
        component: u16,
        bounds: [u32; 4],
        transform: &NonlinearPointTransform,
    ) -> NonlinearRegion<'_> {
        NonlinearRegion {
            component,
            x0: bounds[0],
            y0: bounds[1],
            x1: bounds[2],
            y1: bounds[3],
            transform,
        }
    }

    let one = 1_u32 << 16;
    let transforms = [
        NonlinearPointTransform::for_test(8, false, 0, None, None, vec![]),
        NonlinearPointTransform::for_test(8, true, 3, None, None, vec![]),
        NonlinearPointTransform::for_test(
            8,
            false,
            2,
            Some(0),
            Some(u32::MAX),
            vec![0, 128, 255], // Three interpolation knots span the full output range.
        ),
        NonlinearPointTransform::gamma_for_test(8, false, [one, one, one, one, 0]),
        NonlinearPointTransform::for_test(0, false, 0, None, None, vec![]),
        NonlinearPointTransform::for_test(7, false, 0, None, None, vec![]),
        NonlinearPointTransform::for_test(8, false, u8::MAX, None, None, vec![]),
    ];
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(8)
            .unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(24)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(3).unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(5).unwrap(),
    ];
    let mut cases = 0;
    let mut successes = 0;
    let mut failure_prefixes = 0;
    for (transform_index, transform) in transforms.iter().enumerate() {
        let alternate = &transforms[(transform_index + 1) % transforms.len()];
        for pattern in 0..12 {
            let regions = match pattern {
                0 => vec![],
                1 => vec![region(0, [0, 0, 2, 2], transform)],
                2 => vec![
                    region(0, [0, 0, 1, 2], transform),
                    region(0, [1, 0, 2, 2], transform),
                ],
                3 => vec![
                    region(0, [0, 0, 2, 2], transform),
                    region(0, [0, 0, 2, 2], transform),
                ],
                4 => vec![region(0, [0, 0, 1, 1], transform)],
                5 => vec![region(0, [0, 0, 3, 2], transform)],
                6 => vec![region(0, [0, 0, 0, 2], transform)],
                7 => vec![region(u16::MAX, [u32::MAX, 0, 0, 0], transform)],
                8 => vec![
                    region(0, [0, 0, 2, 2], transform),
                    region(1, [0, 0, 2, 2], alternate),
                ],
                9 => vec![
                    region(0, [0, 0, 1, 2], transform),
                    region(0, [1, 0, 2, 2], alternate),
                ],
                10 => vec![region(1, [0, 0, 2, 2], transform)],
                _ => vec![
                    region(0, [0, 0, 2, 1], transform),
                    region(0, [0, 1, 2, 2], transform),
                ],
            };
            for case in 0..12 {
                for limit in &limits {
                    let mut actual = source(case);
                    let mut expected = source(case);
                    let result = actual.apply_nonlinear_regions(&regions, limit);
                    let expected_result = reference(&mut expected, &regions, limit);
                    assert_eq!(result, expected_result);
                    assert_eq!(actual, expected);
                    successes += usize::from(result.is_ok());
                    failure_prefixes += usize::from(result.is_err() && actual != source(case));
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 7_056);
    assert!(successes > 100);
    assert!(failure_prefixes > 0);

    let full = [region(0, [0, 0, 2, 2], &transforms[0])];
    let mut component = source(1).components.remove(0);
    let unchanged = source(1).components.remove(0);
    assert_eq!(
        component.apply_nonlinear_regions(0, &full, u64::MAX, &ResourceLimits::HARDENED),
        Err(arithmetic_overflow())
    );
    assert_eq!(component, unchanged);
    let mut large = TypedImage::for_test(
        0,
        0,
        17,
        u32::MAX,
        (0..65_537)
            .map(|_| {
                // Empty components isolate the component-count admission boundary.
                TypedComponent::from_parts(0, 0, unchanged.info, TypedSamples::Signed(vec![]))
            })
            .collect(),
    );
    assert_eq!(
        large.apply_nonlinear_regions(&[], &ResourceLimits::HARDENED),
        Err(arithmetic_overflow())
    );
    assert!(large.components.iter().all(|component| component.samples
        == TypedSamples::Signed(vec![])
        && component.info == unchanged.info
        && component.width == 0
        && component.height == 0
        && component.channel_definitions.is_empty()));
}

#[test]
fn applies_tile_specific_nlt_regions_once() {
    let info = ComponentInfo {
        precision: 8,
        signed: true,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let component =
        TypedComponent::from_parts(4, 1, info, TypedSamples::Signed(vec![-128, -1, -128, -1]));
    let mut image =
        TypedImage::from_components(4, 1, vec![component], &ResourceLimits::default()).unwrap();
    let complement = NonlinearPointTransform::for_test(8, true, 3, None, None, Vec::new());
    let identity = NonlinearPointTransform::for_test(8, true, 0, None, None, Vec::new());
    image
        .apply_nonlinear_regions(
            &[
                NonlinearRegion {
                    component: 0,
                    x0: 0,
                    y0: 0,
                    x1: 2,
                    y1: 1,
                    transform: &complement,
                },
                NonlinearRegion {
                    component: 0,
                    x0: 2,
                    y0: 0,
                    x1: 4,
                    y1: 1,
                    transform: &identity,
                },
            ],
            &ResourceLimits::default(),
        )
        .unwrap();
    assert_eq!(
        image.component(0).unwrap().samples(),
        &TypedSamples::Signed(vec![-1, -128, -128, -1])
    );
}

#[test]
fn assembles_subsampled_component_tiles() {
    let info = ComponentInfo {
        precision: 8,
        signed: false,
        x_subsampling: 2,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let left = [1];
    let right = [2];
    let image = assemble_image(
        &image_size(&[info], 4, 1),
        &[
            TileComponent {
                component: 0,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &left,
            },
            TileComponent {
                component: 0,
                x: 1,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &right,
            },
        ],
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(image.component(0).unwrap().samples(), [1, 2]);
    assert_eq!(
        image
            .component(0)
            .unwrap()
            .typed_samples(&ResourceLimits::default())
            .unwrap(),
        TypedSamples::Unsigned(vec![129, 130])
    );
}

#[test]
fn applies_reversible_component_transform() {
    let info = ComponentInfo {
        precision: 8,
        signed: true,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let y = [10, 20];
    let cb = [1, 2];
    let cr = [3, 4];
    let size = image_size(&[info; 3], 2, 1);
    let mut image = assemble_image(
        &size,
        &[
            TileComponent {
                component: 0,
                x: 0,
                y: 0,
                width: 2,
                height: 1,
                fraction_bits: 0,
                samples: &y,
            },
            TileComponent {
                component: 1,
                x: 0,
                y: 0,
                width: 2,
                height: 1,
                fraction_bits: 0,
                samples: &cb,
            },
            TileComponent {
                component: 2,
                x: 0,
                y: 0,
                width: 2,
                height: 1,
                fraction_bits: 0,
                samples: &cr,
            },
        ],
        &ResourceLimits::default(),
    )
    .unwrap();
    apply_reversible_component_transform(&mut image).unwrap();
    assert_eq!(image.component(0).unwrap().samples(), [12, 23]);
    assert_eq!(image.component(1).unwrap().samples(), [9, 19]);
    assert_eq!(image.component(2).unwrap().samples(), [10, 21]);
}

#[test]
fn applies_deterministic_fixed_point_multiple_component_transform() {
    let info = ComponentInfo {
        precision: 8,
        signed: true,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let first = [65_536];
    let second = [131_072];
    let size = image_size(&[info; 2], 1, 1);
    let mut image = assemble_image(
        &size,
        &[
            TileComponent {
                component: 0,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: FIXED_BITS,
                samples: &first,
            },
            TileComponent {
                component: 1,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: FIXED_BITS,
                samples: &second,
            },
        ],
        &ResourceLimits::default(),
    )
    .unwrap();
    let matrix = MctArray::from_values(
        1,
        MctArrayKind::Decorrelation,
        MctNumericFormat::Float32,
        FIXED_BITS,
        vec![98_304, 32_768, -65_536, 131_072],
    );
    let offsets = MctArray::from_values(
        2,
        MctArrayKind::Offset,
        MctNumericFormat::Float32,
        FIXED_BITS,
        vec![16_384, -32_768],
    );
    let transform = MultipleComponentTransform::from_arrays(false, 2, matrix, Some(offsets));
    apply_multiple_component_transform(&mut image, &transform, &ResourceLimits::default()).unwrap();
    assert_eq!(image.component(0).unwrap().samples(), &[11_811_160_064]);
    assert_eq!(image.component(1).unwrap().samples(), &[10_737_418_240]);
    assert_eq!(image.component(0).unwrap().fraction_bits(), MCT_FIXED_BITS);
}

#[test]
fn applies_ordered_subset_dependency_stages_in_reverse() {
    let info = ComponentInfo {
        precision: 8,
        signed: true,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let first = [10];
    let second = [20];
    let third = [5];
    let mut image = assemble_image(
        &image_size(&[info; 3], 1, 1),
        &[
            TileComponent {
                component: 0,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &first,
            },
            TileComponent {
                component: 1,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &second,
            },
            TileComponent {
                component: 2,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &third,
            },
        ],
        &ResourceLimits::default(),
    )
    .unwrap();
    let identity = |index| {
        MctArray::from_values(
            index,
            MctArrayKind::Decorrelation,
            MctNumericFormat::Int16,
            0,
            vec![1, 1],
        )
    };
    let offset = |index, value| {
        MctArray::from_values(
            index,
            MctArrayKind::Offset,
            MctNumericFormat::Int16,
            0,
            vec![value],
        )
    };
    let transform = MultipleComponentTransform::from_stages(vec![
        MctStage::from_collections(
            1,
            vec![MctCollection::from_arrays(
                true,
                vec![0],
                vec![1],
                identity(1),
                Some(offset(2, 2)),
            )],
        ),
        MctStage::from_collections(
            2,
            vec![MctCollection::from_arrays(
                true,
                vec![1],
                vec![2],
                identity(3),
                Some(offset(4, 1)),
            )],
        ),
    ]);
    apply_multiple_component_transform(&mut image, &transform, &ResourceLimits::default()).unwrap();
    assert_eq!(image.component(0).unwrap().samples(), &[8]);
    assert_eq!(image.component(1).unwrap().samples(), &[6]);
    assert_eq!(image.component(2).unwrap().samples(), &[5]);
}

#[test]
fn applies_reversible_and_irreversible_dependency_collections() {
    let info = ComponentInfo {
        precision: 8,
        signed: true,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let make_image = |first: &[i64], second: &[i64]| {
        assemble_image(
            &image_size(&[info; 2], 1, 1),
            &[
                TileComponent {
                    component: 0,
                    x: 0,
                    y: 0,
                    width: 1,
                    height: 1,
                    fraction_bits: 0,
                    samples: first,
                },
                TileComponent {
                    component: 1,
                    x: 0,
                    y: 0,
                    width: 1,
                    height: 1,
                    fraction_bits: 0,
                    samples: second,
                },
            ],
            &ResourceLimits::default(),
        )
        .unwrap()
    };
    let reversible_coefficients = MctArray::from_values(
        1,
        MctArrayKind::Dependency,
        MctNumericFormat::Int16,
        0,
        vec![1, 2],
    );
    let reversible = MultipleComponentTransform::from_stages(vec![MctStage::from_collections(
        1,
        vec![MctCollection::from_dependency(
            true,
            vec![0, 1],
            Some(reversible_coefficients),
            None,
        )],
    )]);
    let mut image = make_image(&[10], &[15]);
    apply_multiple_component_transform(&mut image, &reversible, &ResourceLimits::default())
        .unwrap();
    assert_eq!(image.component(0).unwrap().samples(), &[10]);
    assert_eq!(image.component(1).unwrap().samples(), &[20]);

    let irreversible_coefficients = MctArray::from_values(
        1,
        MctArrayKind::Dependency,
        MctNumericFormat::Int16,
        0,
        vec![1],
    );
    let irreversible = MultipleComponentTransform::from_stages(vec![MctStage::from_collections(
        1,
        vec![MctCollection::from_dependency(
            false,
            vec![0, 1],
            Some(irreversible_coefficients),
            None,
        )],
    )]);
    let mut image = make_image(&[2], &[3]);
    apply_multiple_component_transform(&mut image, &irreversible, &ResourceLimits::default())
        .unwrap();
    assert_eq!(
        image.component(0).unwrap().samples(),
        &[2_i64 << MCT_FIXED_BITS]
    );
    assert_eq!(
        image.component(1).unwrap().samples(),
        &[5_i64 << MCT_FIXED_BITS]
    );
}

#[test]
fn synthesizes_reversible_component_wavelet_with_canvas_parity() {
    let info = ComponentInfo {
        precision: 8,
        signed: true,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let low0 = [3];
    let low1 = [7];
    let high = [2];
    let mut image = assemble_image(
        &image_size(&[info; 3], 1, 1),
        &[
            TileComponent {
                component: 0,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &low0,
            },
            TileComponent {
                component: 1,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &low1,
            },
            TileComponent {
                component: 2,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &high,
            },
        ],
        &ResourceLimits::default(),
    )
    .unwrap();
    let transform = MultipleComponentTransform::from_stages(vec![MctStage::from_collections(
        1,
        vec![MctCollection::from_wavelet(
            vec![0, 1, 2],
            vec![0, 1, 2],
            MctWaveletType::Reversible5x3,
            1,
            0,
        )],
    )]);
    apply_multiple_component_transform(&mut image, &transform, &ResourceLimits::default()).unwrap();
    assert_eq!(image.component(0).unwrap().samples(), &[2]);
    assert_eq!(image.component(1).unwrap().samples(), &[6]);
    assert_eq!(image.component(2).unwrap().samples(), &[6]);
}

#[test]
fn synthesizes_irreversible_component_wavelet_in_q32() {
    let info = ComponentInfo {
        precision: 8,
        signed: true,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let low0 = [3];
    let low1 = [7];
    let high = [2];
    let mut image = assemble_image(
        &image_size(&[info; 3], 1, 1),
        &[
            TileComponent {
                component: 0,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &low0,
            },
            TileComponent {
                component: 1,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &low1,
            },
            TileComponent {
                component: 2,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &high,
            },
        ],
        &ResourceLimits::default(),
    )
    .unwrap();
    let transform = MultipleComponentTransform::from_stages(vec![MctStage::from_collections(
        1,
        vec![MctCollection::from_wavelet(
            vec![0, 1, 2],
            vec![0, 1, 2],
            MctWaveletType::Irreversible9x7,
            1,
            0,
        )],
    )]);
    let expected = inverse_9_7(
        &[3_i64 << MCT_FIXED_BITS, 7_i64 << MCT_FIXED_BITS],
        &[2_i64 << MCT_FIXED_BITS],
        true,
    )
    .unwrap();
    apply_multiple_component_transform(&mut image, &transform, &ResourceLimits::default()).unwrap();
    assert_eq!(image.component(0).unwrap().samples(), &expected[0..1]);
    assert_eq!(image.component(1).unwrap().samples(), &expected[1..2]);
    assert_eq!(image.component(2).unwrap().samples(), &expected[2..3]);
    assert_eq!(image.component(0).unwrap().fraction_bits(), MCT_FIXED_BITS);
}

#[test]
fn rejects_overlapping_or_incomplete_tiles() {
    let info = ComponentInfo {
        precision: 8,
        signed: true,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let samples = [1];
    assert!(
        assemble_image(
            &image_size(&[info], 2, 1),
            &[TileComponent {
                component: 0,
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                fraction_bits: 0,
                samples: &samples,
            }],
            &ResourceLimits::default(),
        )
        .is_err()
    );
}
