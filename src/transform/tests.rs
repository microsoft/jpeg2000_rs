use super::*;

#[test]
fn arbitrary_q32_unit_scaling_and_signed_rounding_are_exact() {
    for value in [i64::MIN, i64::MIN + 1, -65_536, -1, 0, 1, 65_536, i64::MAX] {
        assert_eq!(fixed_mul_q32(value, 1_i64 << 32), Ok(value));
    }
    for (value, expected) in [
        (-(1_i128 << 32), -1),
        (-(1_i128 << 31) - 1, -1),
        (-(1_i128 << 31), -1),
        (-(1_i128 << 31) + 1, 0),
        (-1, 0),
        (0, 0),
        (1, 0),
        ((1_i128 << 31) - 1, 0),
        (1_i128 << 31, 1),
        ((1_i128 << 31) + 1, 1),
        (1_i128 << 32, 1),
    ] {
        assert_eq!(round_shift_i128(value, 32), Ok(expected));
    }
}

#[test]
fn arbitrary_q32_arithmetic_preserves_full_signed_edges_and_errors() {
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let values = [
        i64::MIN,
        i64::MIN + 1,
        -0x1_0000_0001,
        -0x1_0000_0000,
        -0x8000_0000,
        -3,
        -2,
        -1,
        0,
        1,
        2,
        3,
        0x8000_0000,
        0x1_0000_0000,
        0x1_0000_0001,
        i64::MAX - 1,
        i64::MAX,
    ];
    for value in values {
        for factor in values {
            let product = i128::from(value) * i128::from(factor);
            let magnitude = (product.unsigned_abs() + 0x8000_0000_u128) >> 32;
            let rounded = i128::try_from(magnitude).unwrap();
            let signed = if product < 0 { -rounded } else { rounded };
            let expected = i64::try_from(signed).map_err(|_| overflow);
            assert_eq!(fixed_mul_q32(value, factor), expected);
            let expected = if factor == 0 {
                Err(overflow)
            } else {
                i64::try_from((i128::from(value) * 0x1_0000_0000_i128) / i128::from(factor))
                    .map_err(|_| overflow)
            };
            assert_eq!(fixed_div_q32(value, factor), expected);
        }
    }
    assert_eq!(fixed_mul_q32(-1, 0x1_0000_0000), Ok(-1));
    assert_eq!(fixed_div_q32(-1, 3), Ok(-1_431_655_765));
    assert_eq!(fixed_div_q32(1, -3), Ok(-1_431_655_765));
    assert_eq!(round_shift_i128(i128::MIN, 1), Ok(i128::MIN / 2));
    assert_eq!(round_shift_i128(i128::MAX, 1), Err(overflow));
    for shift in [0, 128, 129, u32::MAX] {
        assert_eq!(round_shift_i128(0, shift), Err(overflow));
    }
    for shift in [1, 2, 31, 32, 63, 64, 127] {
        assert_eq!(round_shift_i128(0, shift), Ok(0));
        assert_eq!(
            round_shift_i128(-1, shift),
            Ok(if shift == 1 { -1 } else { 0 })
        );
    }
}

#[test]
fn arbitrary_binary_coefficients_match_integer_rational_rounding_and_raw_format_edges() {
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let reference = |negative: bool, significand: u128, exponent: i32| {
        let shift = i64::from(exponent) + 32;
        if shift > i64::from(i32::MAX) {
            return Err(overflow);
        }
        let magnitude = if shift >= 0 {
            if shift >= 128 {
                return Err(overflow);
            }
            significand
                .checked_mul(2_u128.pow(shift as u32))
                .ok_or(overflow)?
        } else if -shift >= 128 {
            0
        } else {
            let denominator = 2_u128.pow((-shift) as u32);
            let quotient = significand / denominator;
            let twice_remainder = 2 * (significand % denominator);
            quotient
                + u128::from(
                    twice_remainder > denominator
                        || (twice_remainder == denominator && quotient % 2 == 1),
                )
        };
        if magnitude > i128::MAX as u128 {
            return Err(overflow);
        }
        let signed = if negative {
            -(magnitude as i128)
        } else {
            magnitude as i128
        };
        i64::try_from(signed).map_err(|_| overflow)
    };
    let mut contexts = 0;
    for negative in [false, true] {
        for significand in [
            0,
            1,
            3,
            5,
            7,
            1_u128 << 63,
            u128::from(u64::MAX),
            (1_u128 << 113) - 1,
            u128::MAX,
        ] {
            for exponent in [
                i32::MIN,
                -200,
                -160,
                -159,
                -128,
                -64,
                -33,
                -32,
                -31,
                0,
                31,
                63,
                96,
                127,
                i32::MAX - 32,
                i32::MAX,
            ] {
                assert_eq!(
                    fixed_from_binary_q32(negative, significand, exponent),
                    reference(negative, significand, exponent),
                    "negative={negative} significand={significand} exponent={exponent}",
                );
                contexts += 1;
            }
        }
    }
    assert_eq!(contexts, 288);
    assert_eq!(fixed_from_binary_q32(false, 3, -33), Ok(2));
    assert_eq!(fixed_from_binary_q32(false, 5, -33), Ok(2));
    assert_eq!(fixed_from_binary_q32(true, 7, -33), Ok(-4));
    assert_eq!(fixed_from_binary_q32(true, 1_u128 << 63, -32), Ok(i64::MIN));
    assert_eq!(
        fixed_from_binary_q32(false, 1_u128 << 63, -32),
        Err(overflow)
    );
    assert_eq!(fixed_from_binary_q32(false, u128::MAX, -160), Ok(0));
    for (bits, expected) in [
        (0_f32.to_bits(), Ok(0)),
        ((-0_f32).to_bits(), Ok(0)),
        (1_f32.to_bits(), Ok(1_i64 << 32)),
        ((-1_f32).to_bits(), Ok(-(1_i64 << 32))),
        (0.5_f32.to_bits(), Ok(1_i64 << 31)),
        (f32::INFINITY.to_bits(), Err(invalid)),
        (f32::NAN.to_bits(), Err(invalid)),
        (1_u32, Ok(0)),
    ] {
        assert_eq!(binary_to_fixed(u128::from(bits), 32, 8, 23, 127), expected);
    }
    for (bits, expected) in [
        (0_f64.to_bits(), Ok(0)),
        ((-0_f64).to_bits(), Ok(0)),
        (1_f64.to_bits(), Ok(1_i64 << 32)),
        ((-1_f64).to_bits(), Ok(-(1_i64 << 32))),
        (0.5_f64.to_bits(), Ok(1_i64 << 31)),
        (f64::INFINITY.to_bits(), Err(invalid)),
        (f64::NAN.to_bits(), Err(invalid)),
        (1_u64, Ok(0)),
    ] {
        assert_eq!(
            binary_to_fixed(u128::from(bits), 64, 11, 52, 1023),
            expected
        );
    }
    for (bits, expected) in [
        (0, Ok(0)),
        (1_u128 << 127, Ok(0)),
        (16383_u128 << 112, Ok(1_i64 << 32)),
        ((1_u128 << 127) | (16383_u128 << 112), Ok(-(1_i64 << 32))),
        (16382_u128 << 112, Ok(1_i64 << 31)),
        (32767_u128 << 112, Err(invalid)),
        ((32767_u128 << 112) | 1, Err(invalid)),
        (1, Ok(0)),
    ] {
        assert_eq!(binary_to_fixed(bits, 128, 15, 112, 16383), expected);
    }
    for (total, exponent, fraction) in [
        (0, 8, 23),
        (129, 8, 23),
        (32, 0, 23),
        (32, 128, 23),
        (32, 8, 128),
    ] {
        assert_eq!(
            binary_to_fixed(0, total, exponent, fraction, 127),
            Err(invalid)
        );
    }
    assert_eq!(binary_to_fixed(0, 128, 15, 112, i32::MIN), Ok(0));
    assert_eq!(binary_to_fixed(1, 1, 2, 0, i32::MIN), Err(overflow));
    assert_eq!(
        binary_to_fixed((1_u128 << 64) | u128::from(1_f32.to_bits()), 32, 8, 23, 127),
        Ok(-(1_i64 << 32))
    );
}

#[test]
fn arbitrary_sequences_preserve_all_raw_kinds_width_hints_flags_and_scaling_order() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let mut contexts = 0;
    for kind in 0..=u8::MAX {
        for width in [0, 1, 16, u8::MAX] {
            let bits = match kind {
                2 => u128::from(2_f32.to_bits()),
                3 => u128::from(2_f64.to_bits()),
                4 => 16384_u128 << 112,
                _ => 2,
            };
            for flags in 0..8 {
                for first in [false, true] {
                    for reversible in [false, true] {
                        let kernel = ArbitraryKernel::for_test(
                            reversible,
                            kind,
                            flags & 1 != 0,
                            flags & 2 != 0,
                            flags & 4 != 0,
                            Some(KernelCoefficient::for_test(bits, width)),
                            vec![],
                        );
                        let (low, high): (&[i64], &[i64]) = if first {
                            (&[2, 6], &[4])
                        } else {
                            (&[4], &[2, 6])
                        };
                        let expected = if reversible {
                            Ok(vec![2, 4, 6])
                        } else if kind > 4 {
                            Err(invalid)
                        } else if first {
                            Ok(vec![4, 2, 12])
                        } else {
                            Ok(vec![1, 8, 3])
                        };
                        assert_eq!(inverse_arbitrary(low, high, first, &kernel), expected);
                        assert_eq!(inverse_arbitrary(&[7], &[], true, &kernel), Ok(vec![7]));
                        assert_eq!(inverse_arbitrary(&[], &[-3], false, &kernel), Ok(vec![-1]));
                        contexts += 1;
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 32_768);
    let missing = ArbitraryKernel::for_test(false, 0, false, false, false, None, vec![]);
    assert_eq!(inverse_arbitrary(&[], &[], true, &missing), Err(invalid));
    assert_eq!(inverse_arbitrary(&[7], &[], true, &missing), Ok(vec![7]));
    let zero = ArbitraryKernel::for_test(
        false,
        0,
        false,
        false,
        false,
        Some(KernelCoefficient::for_test(0, 255)),
        vec![],
    );
    assert_eq!(inverse_arbitrary(&[], &[], true, &zero), Err(invalid));
    let huge = ArbitraryKernel::for_test(
        false,
        0,
        false,
        false,
        false,
        Some(KernelCoefficient::for_test(i128::MAX as u128, 0)),
        vec![],
    );
    assert_eq!(inverse_arbitrary(&[1, 2], &[], true, &huge), Err(invalid));
    assert_eq!(inverse_arbitrary(&[], &[], true, &huge), Err(overflow));
    let unit = ArbitraryKernel::for_test(
        false,
        0,
        false,
        false,
        false,
        Some(KernelCoefficient::for_test(1, 0)),
        vec![],
    );
    assert_eq!(
        inverse_arbitrary(&[-2, -6], &[-4], true, &unit),
        Ok(vec![-2, -4, -6])
    );
}

#[test]
fn sarah_dev_404e919a62_half_filter_uses_absolute_band_index() {
    fn kernel(reversible: bool, odd: bool, whole: bool, offset: i8, alpha: i8) -> ArbitraryKernel {
        let coefficient = if reversible {
            KernelCoefficient::for_test(i128::from(alpha) as u128, 1)
        } else {
            KernelCoefficient::for_test(u128::from(f32::from(alpha).to_bits()), 4)
        };
        ArbitraryKernel::for_test(
            reversible,
            if reversible { 0 } else { 2 },
            whole,
            odd,
            false,
            (!reversible).then(|| KernelCoefficient::for_test(u128::from(1_f32.to_bits()), 4)),
            vec![KernelLiftingStep::for_test(
                offset,
                0,
                reversible.then(|| KernelCoefficient::for_test(0, 1)),
                vec![coefficient],
            )],
        )
    }

    assert_eq!(
        inverse_arbitrary(&[10], &[2, 7], false, &kernel(true, false, false, 0, 1)),
        Ok(vec![2, 3, 7]),
    );
    let mut cases = 0;
    for length in 2_usize..=9 {
        for first in [false, true] {
            for odd in [false, true] {
                for reversible in [false, true] {
                    for whole in [false, true] {
                        for offset in [-2_i8, 0, 2] {
                            for alpha in [-1_i8, 1] {
                                let scale = if reversible { 1 } else { 65_536 };
                                let input: Vec<_> = (0..length)
                                    .map(|i| (i64::try_from(i).unwrap() * 7 - 19) * scale)
                                    .collect();
                                let low: Vec<_> = input
                                    .iter()
                                    .enumerate()
                                    .filter_map(|(i, value)| {
                                        ((i % 2 == 0) == first).then_some(*value)
                                    })
                                    .collect();
                                let high: Vec<_> = input
                                    .iter()
                                    .enumerate()
                                    .filter_map(|(i, value)| {
                                        ((i % 2 == 0) != first).then_some(*value)
                                    })
                                    .collect();
                                let origin = i64::from(!first);
                                let end = origin + i64::try_from(length).unwrap() - 1;
                                let parity = i64::from(odd);
                                let first_source = origin + i64::from(origin % 2 == parity);
                                let last_source = end - i64::from(end % 2 == parity);
                                let sample = |coordinate: i64| {
                                    input[usize::try_from(
                                        coordinate.clamp(first_source, last_source) - origin,
                                    )
                                    .unwrap()]
                                };
                                let mut expected = input.clone();
                                for (i, value) in expected.iter_mut().enumerate() {
                                    let coordinate = origin + i64::try_from(i).unwrap();
                                    if coordinate % 2 != parity {
                                        continue;
                                    }
                                    let contribution = if whole {
                                        sample(coordinate - 1) + sample(coordinate + 1)
                                    } else {
                                        let band_index = (coordinate - parity) / 2;
                                        sample(2 * (band_index + i64::from(offset)) + 1 - parity)
                                    };
                                    *value -= i64::from(alpha) * contribution;
                                }
                                assert_eq!(
                                    inverse_arbitrary(
                                        &low,
                                        &high,
                                        first,
                                        &kernel(reversible, odd, whole, offset, alpha)
                                    ),
                                    Ok(expected),
                                    "length={length} first={first} odd={odd} reversible={reversible} whole={whole} offset={offset} alpha={alpha}",
                                );
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 768);
}

#[test]
fn arbitrary_lifting_runs_reverse_step_parity_and_preserves_late_partial_errors() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let residue = |value| Some(KernelCoefficient::for_test(value, u8::MAX));
    for first in [false, true] {
        for odd in [false, true] {
            let kernel = ArbitraryKernel::for_test(
                true,
                0,
                true,
                odd,
                false,
                None,
                vec![
                    KernelLiftingStep::for_test(i8::MIN, 0, residue(1), vec![]),
                    KernelLiftingStep::for_test(i8::MAX, 0, residue(2), vec![]),
                ],
            );
            let (low, high): (&[i64], &[i64]) = if first {
                (&[2, 6], &[4])
            } else {
                (&[4], &[2, 6])
            };
            let expected = if first == odd {
                vec![1, 2, 5]
            } else {
                vec![0, 3, 4]
            };
            assert_eq!(inverse_arbitrary(low, high, first, &kernel), Ok(expected));
        }
    }
    let missing = ArbitraryKernel::for_test(
        true,
        0,
        false,
        false,
        false,
        None,
        vec![KernelLiftingStep::for_test(0, 0, None, vec![])],
    );
    assert_eq!(
        inverse_arbitrary(&[2, 6], &[4], true, &missing),
        Err(invalid)
    );
    assert_eq!(inverse_arbitrary(&[], &[], true, &missing), Ok(vec![]));
    for exponent in [0, 126, 127, 128, u8::MAX] {
        let kernel = ArbitraryKernel::for_test(
            true,
            0,
            false,
            false,
            false,
            None,
            vec![KernelLiftingStep::for_test(0, exponent, residue(0), vec![])],
        );
        let expected = if exponent >= 127 {
            Err(invalid)
        } else {
            Ok(vec![2, 4, 6])
        };
        assert_eq!(inverse_arbitrary(&[2, 6], &[4], true, &kernel), expected);
    }
    let late = ArbitraryKernel::for_test(
        true,
        0,
        false,
        false,
        false,
        None,
        vec![KernelLiftingStep::for_test(0, 0, residue(1), vec![])],
    );
    let mut samples = vec![10, 20, i64::MIN];
    assert_eq!(
        apply_arbitrary_steps(&mut samples, true, &late),
        Err(overflow)
    );
    assert_eq!(samples, vec![9, 20, i64::MIN]);
    let ignored = ArbitraryKernel::for_test(
        false,
        0,
        false,
        true,
        false,
        residue(1),
        vec![KernelLiftingStep::for_test(i8::MIN, u8::MAX, None, vec![])],
    );
    assert_eq!(
        inverse_arbitrary(&[2, 6], &[4], true, &ignored),
        Ok(vec![2, 4, 6])
    );
    assert_eq!(inverse_arbitrary(&[], &[], true, &ignored), Err(overflow));
}

pub(crate) fn reference_reconstruction(
    input: &[([u64; 6], bool)],
    step: QuantizationStep,
    range: u8,
    reversible: bool,
    shift: u8,
    maximum: u64,
) -> Result<(u32, u32, u8, Vec<i64>), DecodeError> {
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    if !(1..=38).contains(&range) || step.exponent > 31 || step.mantissa > 2047 {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidTransform,
        });
    }
    let bytes = (input.len() as u64).checked_mul(8).ok_or(overflow)?;
    if bytes > maximum {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: maximum,
            actual: bytes,
        });
    }
    let numerator = u128::from(2048 + step.mantissa) * 32;
    let step_q16 = if reversible {
        1
    } else if range >= step.exponent {
        numerator * 2_u128.pow(u32::from(range - step.exponent))
    } else {
        numerator / 2_u128.pow(u32::from(step.exponent - range))
    };
    if step_q16 > i64::MAX as u128 {
        return Err(overflow);
    }
    let mut output = Vec::new();
    for (limbs, negative) in input {
        let bits: Vec<bool> = (0..384)
            .map(|bit| !(limbs[bit / 64] / 2_u64.pow((bit % 64) as u32)).is_multiple_of(2))
            .collect();
        let is_roi = bits[usize::from(shift)..].iter().any(|bit| *bit);
        let start = if is_roi { usize::from(shift) } else { 0 };
        if bits[start + 63..].iter().any(|bit| *bit) {
            return Err(overflow);
        }
        let magnitude: u128 = bits[start..start + 63]
            .iter()
            .enumerate()
            .map(|(bit, set)| if *set { 2_u128.pow(bit as u32) } else { 0 })
            .sum();
        let sample = if reversible || magnitude == 0 {
            magnitude
        } else {
            ((magnitude * 2 + 1) * step_q16) / 2
        };
        if sample > i64::MAX as u128 {
            return Err(overflow);
        }
        output.push(if *negative {
            -(sample as i64)
        } else {
            sample as i64
        });
    }
    Ok((
        input.len() as u32,
        1,
        if reversible { 0 } else { 16 },
        output,
    ))
}

fn observed_reconstruction(
    result: Result<ReconstructedPlane, DecodeError>,
) -> Result<(u32, u32, u8, Vec<i64>), DecodeError> {
    result.map(|plane| {
        (
            plane.width(),
            plane.height(),
            plane.fraction_bits(),
            plane.samples().to_vec(),
        )
    })
}

fn reference_lift(
    input: &[i64],
    even: bool,
    kind: u8,
    factor: i64,
) -> (Result<(), DecodeError>, Vec<i64>) {
    let mut result = input.to_vec();
    let checked = |value: i128| i64::try_from(value).map(i128::from);
    for index in 0..input.len() {
        if index.is_multiple_of(2) != even || input.len() <= 1 {
            continue;
        }
        let left = i128::from(input[if index == 0 { 1 } else { index - 1 }]);
        let right = i128::from(
            input[if index + 1 < input.len() {
                index + 1
            } else {
                index - 1
            }],
        );
        let sample = (|| {
            let sum = checked(left + right)?;
            let delta = if kind == 0 {
                checked(sum + 2)?.div_euclid(4)
            } else if kind == 1 {
                sum.div_euclid(2)
            } else {
                checked(checked(sum * i128::from(factor))? + 32768)?.div_euclid(65536)
            };
            i64::try_from(i128::from(input[index]) + if kind == 1 { delta } else { -delta })
        })();
        match sample {
            Ok(value) => result[index] = value,
            Err(_) => return (Err(arithmetic_overflow()), result),
        }
    }
    (Ok(()), result)
}

fn reference_five_three(
    low: &[i64],
    high: &[i64],
    low_first: bool,
) -> Result<Vec<i64>, DecodeError> {
    let length = low.len() + high.len();
    let low_count = length / 2 + usize::from(low_first) * (length % 2);
    if low.len() != low_count || high.len() != length - low_count {
        return Err(invalid_transform());
    }
    let samples: Vec<_> = (0..length)
        .map(|index| {
            if index.is_multiple_of(2) == low_first {
                low[index / 2]
            } else {
                high[index / 2]
            }
        })
        .collect();
    if length == 1 && !low_first {
        return Ok(vec![samples[0].div_euclid(2)]);
    }
    let (status, updated) = reference_lift(&samples, low_first, 0, 0);
    status?;
    let (status, predicted) = reference_lift(&updated, !low_first, 1, 0);
    status?;
    Ok(predicted)
}

fn reference_scale(input: &[i64], even: bool, factor: i64) -> (Result<(), DecodeError>, Vec<i64>) {
    let mut output = input.to_vec();
    for (index, value) in input.iter().enumerate() {
        if index.is_multiple_of(2) != even {
            continue;
        }
        let rounded = (|| {
            let product = i64::try_from(i128::from(*value) * i128::from(factor))?;
            let biased = i64::try_from(i128::from(product) + 32768)?;
            i64::try_from(i128::from(biased).div_euclid(65536))
        })();
        match rounded {
            Ok(value) => output[index] = value,
            Err(_) => return (Err(arithmetic_overflow()), output),
        }
    }
    (Ok(()), output)
}

fn reference_nine_seven_lifts(
    input: &[i64],
    low_first: bool,
) -> (Result<(), DecodeError>, Vec<i64>) {
    let mut output = input.to_vec();
    for (stage, factor) in [29066, 57862, -3472, -103949].into_iter().enumerate() {
        let (status, next) = reference_lift(
            &output,
            if stage.is_multiple_of(2) {
                low_first
            } else {
                !low_first
            },
            2,
            factor,
        );
        output = next;
        if status.is_err() {
            return (status, output);
        }
    }
    (Ok(()), output)
}

fn reference_sequence(
    low: &[i64],
    high: &[i64],
    low_first: bool,
    irreversible: bool,
) -> Result<Vec<i64>, DecodeError> {
    if !irreversible {
        return reference_five_three(low, high, low_first);
    }
    let length = low.len() + high.len();
    let low_count = length / 2 + usize::from(low_first) * (length % 2);
    if low.len() != low_count || high.len() != length - low_count {
        return Err(invalid_transform());
    }
    let samples: Vec<_> = (0..length)
        .map(|index| {
            if index.is_multiple_of(2) == low_first {
                low[index / 2]
            } else {
                high[index / 2]
            }
        })
        .collect();
    if length <= 1 {
        return Ok(samples);
    }
    let (status, low_scaled) = reference_scale(&samples, low_first, 80621);
    status?;
    let (status, high_scaled) = reference_scale(&low_scaled, !low_first, 53274);
    status?;
    let (status, lifted) = reference_nine_seven_lifts(&high_scaled, low_first);
    status?;
    Ok(lifted)
}

fn reference_area(width: u32, height: u32) -> Result<usize, DecodeError> {
    let count = u128::from(width) * u128::from(height);
    if u128::from(width) > usize::MAX as u128
        || u128::from(height) > usize::MAX as u128
        || count > usize::MAX as u128
    {
        return Err(arithmetic_overflow());
    }
    Ok(count as usize)
}

fn reference_plane_budget(width: u32, height: u32, maximum: u64) -> Result<usize, DecodeError> {
    let count = reference_area(width, height)?;
    let bytes = (count as u128) * 8;
    if bytes > u128::from(u64::MAX) {
        return Err(arithmetic_overflow());
    }
    if bytes > u128::from(maximum) {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: maximum,
            actual: bytes as u64,
        });
    }
    Ok(count)
}

fn reference_band_row(band: WaveletBand<'_>, y: u32) -> Result<&[i64], DecodeError> {
    if y >= band.height {
        return Err(invalid_transform());
    }
    let start = u128::from(y) * u128::from(band.width);
    let end = start + u128::from(band.width);
    if u128::from(y) > usize::MAX as u128
        || u128::from(band.width) > usize::MAX as u128
        || end > usize::MAX as u128
    {
        return Err(arithmetic_overflow());
    }
    band.samples
        .get(start as usize..end as usize)
        .ok_or_else(invalid_transform)
}

fn reference_column(band: WaveletBand<'_>, x: u32) -> Result<Vec<i64>, DecodeError> {
    if x >= band.width {
        return Err(invalid_transform());
    }
    if u128::from(band.height) > usize::MAX as u128 {
        return Err(arithmetic_overflow());
    }
    let mut output = Vec::new();
    for y in 0..band.height {
        let index = u128::from(y) * u128::from(band.width) + u128::from(x);
        if u128::from(y) > usize::MAX as u128
            || u128::from(band.width) > usize::MAX as u128
            || u128::from(x) > usize::MAX as u128
            || index > usize::MAX as u128
        {
            return Err(arithmetic_overflow());
        }
        output.push(
            *band
                .samples
                .get(index as usize)
                .ok_or_else(invalid_transform)?,
        );
    }
    Ok(output)
}

pub(crate) fn reference_horizontal(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    width: u32,
    low_first: bool,
    irreversible: bool,
    maximum: u64,
) -> Result<(u32, u32, u8, Vec<i64>), DecodeError> {
    let low_width = ((u64::from(width) + u64::from(low_first)) / 2) as u32;
    if low.height == 0
        || low.height != high.height
        || low.width != low_width
        || high.width != width - low_width
    {
        return Err(invalid_transform());
    }
    reference_plane_budget(width, low.height, maximum)?;
    let mut output = Vec::new();
    for y in 0..low.height {
        let low_row = reference_band_row(low, y)?;
        let high_row = reference_band_row(high, y)?;
        output.extend(reference_sequence(
            low_row,
            high_row,
            low_first,
            irreversible,
        )?);
    }
    Ok((width, low.height, if irreversible { 16 } else { 0 }, output))
}

pub(crate) fn reference_vertical(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    height: u32,
    low_first: bool,
    irreversible: bool,
    maximum: u64,
) -> Result<(u32, u32, u8, Vec<i64>), DecodeError> {
    let low_height = ((u64::from(height) + u64::from(low_first)) / 2) as u32;
    if low.width == 0
        || low.width != high.width
        || low.height != low_height
        || high.height != height - low_height
    {
        return Err(invalid_transform());
    }
    let length = reference_plane_budget(low.width, height, maximum)?;
    let mut output = vec![0; length];
    for x in 0..low.width {
        let low_column = reference_column(low, x)?;
        let high_column = reference_column(high, x)?;
        let column = reference_sequence(&low_column, &high_column, low_first, irreversible)?;
        for y in 0..height {
            let destination = u128::from(y) * u128::from(low.width) + u128::from(x);
            if destination > usize::MAX as u128 {
                return Err(arithmetic_overflow());
            }
            *output
                .get_mut(destination as usize)
                .ok_or_else(invalid_transform)? =
                *column.get(y as usize).ok_or_else(invalid_transform)?;
        }
    }
    Ok((low.width, height, if irreversible { 16 } else { 0 }, output))
}

pub(crate) fn reference_level(
    level: WaveletLevel<'_>,
    irreversible: bool,
    maximum: u64,
) -> Result<(u32, u32, u8, Vec<i64>), DecodeError> {
    if level.output_width == 0 || level.output_height == 0 {
        return Err(invalid_transform());
    }
    let low_width =
        ((u64::from(level.output_width) + u64::from(level.low_pass_first_x)) / 2) as u32;
    let low_height =
        ((u64::from(level.output_height) + u64::from(level.low_pass_first_y)) / 2) as u32;
    for (band, width, height) in [
        (level.ll, low_width, low_height),
        (level.hl, level.output_width - low_width, low_height),
        (level.lh, low_width, level.output_height - low_height),
        (
            level.hh,
            level.output_width - low_width,
            level.output_height - low_height,
        ),
    ] {
        if band.width != width || band.height != height {
            return Err(invalid_transform());
        }
        if band.samples.len() != reference_area(width, height)? {
            return Err(invalid_transform());
        }
    }
    reference_plane_budget(level.output_width, level.output_height, maximum)?;
    let mut low_rows = Vec::new();
    let mut high_rows = Vec::new();
    for (low, high, rows) in [
        (level.ll, level.hl, &mut low_rows),
        (level.lh, level.hh, &mut high_rows),
    ] {
        reference_area(level.output_width, low.height)?;
        for y in 0..low.height {
            let low_row = reference_band_row(low, y)?;
            let high_row = reference_band_row(high, y)?;
            rows.extend(reference_sequence(
                low_row,
                high_row,
                level.low_pass_first_x,
                irreversible,
            )?);
        }
    }
    reference_vertical(
        WaveletBand {
            width: level.output_width,
            height: level.ll.height,
            samples: &low_rows,
        },
        WaveletBand {
            width: level.output_width,
            height: level.lh.height,
            samples: &high_rows,
        },
        level.output_height,
        level.low_pass_first_y,
        irreversible,
        maximum,
    )
}

#[test]
fn complete_nine_seven_sequences_match_independent_wide_reference() {
    for length in 0..=6_u32 {
        for encoding in 0..5_usize.pow(length) {
            let mut encoding = encoding;
            let samples: Vec<_> = (0..length)
                .map(|_| {
                    let value = [-65537, -32768, 0, 32768, 65537][encoding % 5];
                    encoding /= 5;
                    value
                })
                .collect();
            for low_first in [false, true] {
                let low: Vec<_> = samples
                    .iter()
                    .enumerate()
                    .filter_map(|(i, value)| {
                        // Preserve the reference's explicit parity-selection block.
                        (i.is_multiple_of(2) == low_first).then_some(*value)
                    })
                    .collect();
                let high: Vec<_> = samples
                    .iter()
                    .enumerate()
                    .filter_map(|(i, value)| {
                        // Preserve the reference's explicit parity-selection block.
                        (i.is_multiple_of(2) != low_first).then_some(*value)
                    })
                    .collect();
                assert_eq!(
                    inverse_9_7(&low, &high, low_first),
                    reference_sequence(&low, &high, low_first, true)
                );
            }
        }
    }
    for low in [
        vec![],
        vec![i64::MIN],
        vec![i64::MAX],
        vec![0, i64::MAX],
        vec![1, -1, 2],
    ] {
        for high in [
            vec![],
            vec![i64::MIN],
            vec![i64::MAX],
            vec![i64::MIN, i64::MAX],
            vec![-2, 0, 2],
        ] {
            for low_first in [false, true] {
                assert_eq!(
                    inverse_9_7(&low, &high, low_first),
                    reference_sequence(&low, &high, low_first, true)
                );
            }
        }
    }
}

#[test]
fn complete_standard_planes_match_independent_reference_for_all_small_geometries() {
    for width in 0..=7_u32 {
        for height in 0..=6_u32 {
            for low_x in [false, true] {
                for low_y in [false, true] {
                    for irreversible in [false, true] {
                        let low_width = ((u64::from(width) + u64::from(low_x)) / 2) as u32;
                        let low_height = ((u64::from(height) + u64::from(low_y)) / 2) as u32;
                        let generated = |w: u32, h: u32, seed: i64| {
                            (0..w * h)
                                .map(|i| {
                                    ((i64::from(i) * 7 + seed) % 17 - 8)
                                        * if irreversible { 65536 } else { 1 }
                                })
                                .collect::<Vec<_>>()
                        };
                        let horizontal_low = generated(low_width, height, 3);
                        let horizontal_high = generated(width - low_width, height, 5);
                        let vertical_low = generated(width, low_height, 7);
                        let vertical_high = generated(width, height - low_height, 11);
                        let ll = generated(low_width, low_height, 2);
                        let hl = generated(width - low_width, low_height, 4);
                        let lh = generated(low_width, height - low_height, 6);
                        let hh = generated(width - low_width, height - low_height, 8);
                        let h_low = WaveletBand {
                            width: low_width,
                            height,
                            samples: &horizontal_low,
                        };
                        let h_high = WaveletBand {
                            width: width - low_width,
                            height,
                            samples: &horizontal_high,
                        };
                        let v_low = WaveletBand {
                            width,
                            height: low_height,
                            samples: &vertical_low,
                        };
                        let v_high = WaveletBand {
                            width,
                            height: height - low_height,
                            samples: &vertical_high,
                        };
                        let level = WaveletLevel {
                            ll: WaveletBand {
                                width: low_width,
                                height: low_height,
                                samples: &ll,
                            },
                            hl: WaveletBand {
                                width: width - low_width,
                                height: low_height,
                                samples: &hl,
                            },
                            lh: WaveletBand {
                                width: low_width,
                                height: height - low_height,
                                samples: &lh,
                            },
                            hh: WaveletBand {
                                width: width - low_width,
                                height: height - low_height,
                                samples: &hh,
                            },
                            output_width: width,
                            output_height: height,
                            low_pass_first_x: low_x,
                            low_pass_first_y: low_y,
                        };
                        for limits in [
                            ResourceLimits::default(),
                            ResourceLimits::default()
                                .with_maximum_decoded_bytes(8)
                                .unwrap(),
                        ] {
                            let horizontal = if irreversible {
                                inverse_horizontal_9_7(h_low, h_high, width, low_x, &limits)
                            } else {
                                inverse_horizontal_5_3(h_low, h_high, width, low_x, &limits)
                            };
                            assert_eq!(
                                observed_reconstruction(horizontal),
                                reference_horizontal(
                                    h_low,
                                    h_high,
                                    width,
                                    low_x,
                                    irreversible,
                                    limits.maximum_decoded_bytes(),
                                )
                            );
                            let vertical = if irreversible {
                                inverse_vertical_9_7(v_low, v_high, height, low_y, &limits)
                            } else {
                                inverse_vertical_5_3(v_low, v_high, height, low_y, &limits)
                            };
                            assert_eq!(
                                observed_reconstruction(vertical),
                                reference_vertical(
                                    v_low,
                                    v_high,
                                    height,
                                    low_y,
                                    irreversible,
                                    limits.maximum_decoded_bytes(),
                                )
                            );
                            let reconstructed = if irreversible {
                                inverse_level_9_7(level, &limits)
                            } else {
                                inverse_level_5_3(level, &limits)
                            };
                            assert_eq!(
                                observed_reconstruction(reconstructed),
                                reference_level(
                                    level,
                                    irreversible,
                                    limits.maximum_decoded_bytes()
                                )
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn complete_plane_rejections_preserve_late_band_checks_and_resource_order() {
    let low = WaveletBand {
        width: 2,
        height: 2,
        samples: &[65536, -65536, 32768],
    };
    let high = WaveletBand {
        width: 2,
        height: 2,
        samples: &[0, 0, 0, 0],
    };
    for limits in [
        ResourceLimits::default(),
        ResourceLimits::default()
            .with_maximum_decoded_bytes(8)
            .unwrap(),
    ] {
        for irreversible in [false, true] {
            let horizontal = if irreversible {
                inverse_horizontal_9_7(low, high, 4, true, &limits)
            } else {
                inverse_horizontal_5_3(low, high, 4, true, &limits)
            };
            assert_eq!(
                observed_reconstruction(horizontal),
                reference_horizontal(
                    low,
                    high,
                    4,
                    true,
                    irreversible,
                    limits.maximum_decoded_bytes()
                )
            );
            let vertical = if irreversible {
                inverse_vertical_9_7(low, high, 4, true, &limits)
            } else {
                inverse_vertical_5_3(low, high, 4, true, &limits)
            };
            assert_eq!(
                observed_reconstruction(vertical),
                reference_vertical(
                    low,
                    high,
                    4,
                    true,
                    irreversible,
                    limits.maximum_decoded_bytes()
                )
            );
        }
        let band = WaveletBand {
            width: 1,
            height: 1,
            samples: &[0],
        };
        let level = WaveletLevel {
            ll: WaveletBand {
                samples: &[0, 1],
                ..band
            },
            hl: band,
            lh: band,
            hh: band,
            output_width: 2,
            output_height: 2,
            low_pass_first_x: true,
            low_pass_first_y: true,
        };
        assert_eq!(
            observed_reconstruction(inverse_level_5_3(level, &limits)),
            reference_level(level, false, limits.maximum_decoded_bytes())
        );
        assert_eq!(
            observed_reconstruction(inverse_level_9_7(level, &limits)),
            reference_level(level, true, limits.maximum_decoded_bytes())
        );
    }
    let trailing_low = WaveletBand {
        width: 1,
        height: 1,
        samples: &[0, 9],
    };
    let trailing_high = WaveletBand {
        width: 1,
        height: 1,
        samples: &[0, 8],
    };
    let limits = ResourceLimits::default();
    assert_eq!(
        observed_reconstruction(inverse_horizontal_5_3(
            trailing_low,
            trailing_high,
            2,
            true,
            &limits
        )),
        Ok((2, 1, 0, vec![0, 0]))
    );
    assert_eq!(
        observed_reconstruction(inverse_vertical_5_3(
            trailing_low,
            trailing_high,
            2,
            true,
            &limits
        )),
        Ok((1, 2, 0, vec![0, 0]))
    );
    let first_overflow = WaveletBand {
        width: 2,
        height: 2,
        samples: &[0, 0],
    };
    let later_missing = WaveletBand {
        width: 1,
        height: 2,
        samples: &[i64::MAX, 0],
    };
    assert_eq!(
        observed_reconstruction(inverse_horizontal_5_3(
            first_overflow,
            later_missing,
            3,
            true,
            &limits
        )),
        Err(arithmetic_overflow())
    );
    let huge_low = WaveletBand {
        width: u32::MAX / 2 + 1,
        height: u32::MAX,
        samples: &[],
    };
    let huge_high = WaveletBand {
        width: u32::MAX / 2,
        ..huge_low
    };
    assert_eq!(
        observed_reconstruction(inverse_horizontal_5_3(
            huge_low,
            huge_high,
            u32::MAX,
            true,
            &limits
        )),
        Err(arithmetic_overflow())
    );
    let huge_low = WaveletBand {
        width: u32::MAX,
        height: u32::MAX / 2 + 1,
        samples: &[],
    };
    let huge_high = WaveletBand {
        height: u32::MAX / 2,
        ..huge_low
    };
    assert_eq!(
        observed_reconstruction(inverse_vertical_9_7(
            huge_low,
            huge_high,
            u32::MAX,
            true,
            &limits
        )),
        Err(arithmetic_overflow())
    );
}

#[test]
fn complete_scaling_lifting_and_column_store_states_match_independent_arithmetic() {
    for input in [
        vec![],
        vec![i64::MIN],
        vec![65536, 0, i64::MAX],
        vec![-65537, 32768, 0, -32768, 65537],
    ] {
        for low_first in [false, true] {
            let expected = reference_nine_seven_lifts(&input, low_first);
            let mut actual = input.clone();
            let status = inverse_nine_seven_lifts(&mut actual, low_first);
            assert_eq!((status, actual), expected);
            for factor in [80621, 53274, -1, i64::MAX] {
                let expected = reference_scale(&input, low_first, factor);
                let mut actual = input.clone();
                let status = scale_parity(&mut actual, low_first, factor);
                assert_eq!((status, actual), expected);
            }
        }
    }
    for (initial, width, height, x, column) in [
        (vec![9; 6], 2_u32, 3_u32, 1_u32, vec![2, 3]),
        (vec![9; 3], 2, 3, 1, vec![2, 3, 4]),
        (vec![], 0, 0, u32::MAX, vec![]),
        (vec![9], 0, 2, 0, vec![2, 3]),
        (vec![9], 1, 1, 2, vec![7]),
    ] {
        let mut expected = initial.clone();
        let mut expected_status = Ok(());
        for y in 0..height {
            let destination = u128::from(y) * u128::from(width) + u128::from(x);
            if destination > usize::MAX as u128 {
                expected_status = Err(arithmetic_overflow());
                break;
            }
            if y as usize >= column.len() || destination as usize >= expected.len() {
                expected_status = Err(invalid_transform());
                break;
            }
            expected[destination as usize] = column[y as usize];
        }
        let mut actual = initial;
        let status = store_column(&mut actual, width, height, x, &column);
        assert_eq!((status, actual), (expected_status, expected));
    }
}

fn reference_converted_samples(
    plane: &ReconstructedPlane,
    precision: u8,
    signed: bool,
    maximum_bytes: u64,
) -> Result<Vec<i64>, DecodeError> {
    if !(1..=38).contains(&precision) || plane.fraction_bits > 62 {
        return Err(invalid_transform());
    }
    let bytes = plane.samples.len() as u128 * 8;
    if bytes > u128::from(u64::MAX) {
        return Err(arithmetic_overflow());
    }
    if bytes > u128::from(maximum_bytes) {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: maximum_bytes,
            actual: bytes as u64,
        });
    }
    let midpoint = 2_i128.pow(u32::from(precision - 1));
    let minimum = if signed { -midpoint } else { 0 };
    let maximum = if signed {
        midpoint - 1
    } else {
        2 * midpoint - 1
    };
    let shift = if signed { 0 } else { midpoint };
    let mut output = Vec::new();
    for value in &plane.samples {
        let rounded = if plane.fraction_bits == 0 {
            i128::from(*value)
        } else {
            let biased = i64::try_from(
                // Preserve the reference conversion's explicit argument boundary.
                i128::from(*value) + 2_i128.pow(u32::from(plane.fraction_bits - 1)),
            )
            .map_err(|_| arithmetic_overflow())?;
            i128::from(biased).div_euclid(2_i128.pow(u32::from(plane.fraction_bits)))
        };
        let shifted = i64::try_from(rounded + shift).map_err(|_| arithmetic_overflow())?;
        output.push(i128::from(shifted).clamp(minimum, maximum) as i64);
    }
    Ok(output)
}

#[test]
fn complete_sample_conversion_matches_wide_reference_and_error_boundaries() {
    for samples in [
        vec![],
        vec![-32769, -32768, -1, 0, 32767, 32768, 32769],
        vec![i64::MIN],
        vec![i64::MAX],
        vec![i64::MAX, i64::MIN],
        vec![0, 1, -1],
    ] {
        for fraction_bits in [0, 1, 16, 62, 63, 255] {
            for precision in [0, 1, 8, 16, 38, 39, 63, 255] {
                for signed in [false, true] {
                    for (width, height) in [(0, 7), (100, 0)] {
                        let plane = ReconstructedPlane {
                            width,
                            height,
                            fraction_bits,
                            samples: samples.clone(),
                        };
                        for limits in [
                            ResourceLimits::default(),
                            ResourceLimits::default()
                                .with_maximum_decoded_bytes(8)
                                .unwrap(),
                        ] {
                            assert_eq!(
                                convert_samples(&plane, precision, signed, &limits),
                                reference_converted_samples(
                                    &plane,
                                    precision,
                                    signed,
                                    limits.maximum_decoded_bytes()
                                ),
                                "fraction={fraction_bits} precision={precision} signed={signed}"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn full_five_three_sequences_and_rejections_match_wide_reference() {
    for length in 0..=6_u32 {
        for encoding in 0..5_usize.pow(length) {
            let mut encoding = encoding;
            let samples: Vec<_> = (0..length)
                .map(|_| {
                    let value = [-3, -1, 0, 1, 4][encoding % 5];
                    encoding /= 5;
                    value
                })
                .collect();
            for low_first in [false, true] {
                let low: Vec<_> = samples
                    .iter()
                    .enumerate()
                    .filter_map(|(i, value)| {
                        // Preserve the reference's explicit parity-selection block.
                        (i.is_multiple_of(2) == low_first).then_some(*value)
                    })
                    .collect();
                let high: Vec<_> = samples
                    .iter()
                    .enumerate()
                    .filter_map(|(i, value)| {
                        // Preserve the reference's explicit parity-selection block.
                        (i.is_multiple_of(2) != low_first).then_some(*value)
                    })
                    .collect();
                assert_eq!(
                    inverse_5_3(&low, &high, low_first),
                    reference_five_three(&low, &high, low_first)
                );
            }
        }
    }
    for low in [
        vec![],
        vec![i64::MIN],
        vec![i64::MAX],
        vec![0, i64::MAX],
        vec![1, -1, 2],
    ] {
        for high in [
            vec![],
            vec![i64::MIN],
            vec![i64::MAX],
            vec![i64::MIN, i64::MAX],
            vec![-2, 0, 2],
        ] {
            for low_first in [false, true] {
                assert_eq!(
                    inverse_5_3(&low, &high, low_first),
                    reference_five_three(&low, &high, low_first)
                );
            }
        }
    }
}

#[test]
fn complete_lifting_buffers_preserve_first_error_state_and_opposite_parity() {
    for input in [
        vec![],
        vec![i64::MIN],
        vec![0, 1, 0, i64::MAX, 0],
        vec![0, i64::MAX, 0],
        vec![i64::MIN, 0, i64::MAX],
        vec![-7, 4, 3, -2, 0, 8, -1, 5],
    ] {
        for even in [false, true] {
            for (kind, factor, step) in [
                (0, 0, InverseLiftingStep::ReversibleUpdate),
                (1, 0, InverseLiftingStep::ReversiblePredict),
                (2, 29066, InverseLiftingStep::Fixed(29066)),
                (2, -103949, InverseLiftingStep::Fixed(-103949)),
            ] {
                let expected = reference_lift(&input, even, kind, factor);
                let mut actual = input.clone();
                let status = inverse_lift(&mut actual, even, step);
                assert_eq!((status, actual), expected);
            }
        }
    }
}

#[test]
fn complete_quantization_planes_match_independent_bit_and_rational_reference() {
    let inputs = [
        vec![],
        vec![
            ([0; 6], true),
            ([1, 0, 0, 0, 0, 0], false),
            ([2, 0, 0, 0, 0, 0], true),
        ],
        vec![([i64::MAX as u64, 0, 0, 0, 0, 0], true)],
        vec![([1_u64 << 63, 0, 0, 0, 0, 0], true)],
        vec![([u64::MAX, 0, 0, 0, 0, 0], false)],
        vec![([1, 1, 0, 0, 0, 0], true)],
        vec![([0, 0, 0, 0, 1 << 35, 0], true)],
        vec![([u64::MAX; 6], false)],
    ];
    for input in inputs {
        let coefficients: Vec<_> = input
            .iter()
            .map(|(limbs, negative)| SignedMagnitude {
                magnitude: Magnitude::from_limbs(*limbs),
                negative: *negative,
            })
            .collect();
        for range in [1, 8, 16, 31, 38] {
            for exponent in [0, 8, 31] {
                for mantissa in [0, 1, 2047] {
                    for reversible in [false, true] {
                        for shift in [0, 1, 31, 63, 64, 65, 127, 128, 191, 192, 254, 255] {
                            let step = QuantizationStep { exponent, mantissa };
                            let expected = reference_reconstruction(
                                &input,
                                step,
                                range,
                                reversible,
                                shift,
                                u64::MAX,
                            );
                            assert_eq!(
                                observed_reconstruction(inverse_quantize_plane(
                                    &coefficients,
                                    step,
                                    range,
                                    reversible,
                                    shift,
                                    u64::MAX,
                                )),
                                expected,
                                "range={range} step={step:?} reversible={reversible} shift={shift}"
                            );
                            assert_eq!(
                                observed_reconstruction(inverse_quantize_magnitudes(
                                    &coefficients,
                                    step,
                                    range,
                                    reversible,
                                    shift,
                                    &ResourceLimits::default(),
                                )),
                                expected,
                                "configured budget adapter range={range} step={step:?} reversible={reversible} shift={shift}"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn quantization_rejects_in_production_order_and_preserves_public_adapters() {
    let step = QuantizationStep {
        exponent: 8,
        mantissa: 17,
    };
    let limits = ResourceLimits::default()
        .with_maximum_decoded_bytes(8)
        .unwrap();
    for values in [
        &[][..],
        &[0][..],
        &[1, -2, 3][..],
        &[i64::MAX][..],
        &[i64::MIN][..],
    ] {
        for reversible in [true, false] {
            let raw: Vec<_> = values
                .iter()
                .map(|value| ([value.unsigned_abs(), 0, 0, 0, 0, 0], *value < 0))
                .collect();
            let expected = if values.contains(&i64::MIN) {
                Err(arithmetic_overflow())
            } else {
                reference_reconstruction(
                    &raw,
                    step,
                    8,
                    reversible,
                    2,
                    limits.maximum_decoded_bytes(),
                )
            };
            assert_eq!(
                observed_reconstruction(inverse_quantize(values, step, 8, reversible, 2, &limits)),
                expected
            );
        }
    }
    let bad_step = QuantizationStep {
        exponent: 32,
        mantissa: 2048,
    };
    assert_eq!(
        observed_reconstruction(inverse_quantize(
            &[0, i64::MIN],
            bad_step,
            0,
            false,
            255,
            &limits,
        )),
        Err(arithmetic_overflow())
    );
    let wide = [SignedMagnitude {
        magnitude: Magnitude::from_limbs([u64::MAX; 6]),
        negative: false,
    }; 2];
    assert_eq!(
        observed_reconstruction(inverse_quantize_magnitudes(
            &wide, bad_step, 0, false, 255, &limits,
        )),
        Err(invalid_transform())
    );
    assert_eq!(
        observed_reconstruction(inverse_quantize_magnitudes(
            &wide, step, 8, false, 0, &limits,
        )),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: 8,
            actual: 16
        })
    );
    #[cfg(target_pointer_width = "64")]
    {
        assert_eq!(
            validate_quantization_size((u64::MAX / 8) as usize, u64::MAX),
            Ok(())
        );
        assert_eq!(
            validate_quantization_size((u64::MAX / 8 + 1) as usize, u64::MAX),
            Err(arithmetic_overflow())
        );
    }
}

#[test]
fn inverse_horizontal_stage_matches_row_synthesis() {
    let low = [2, 4, 6, 8];
    let high = [1, 3, 5, 7];
    let plane = inverse_horizontal_5_3(
        WaveletBand {
            width: 2,
            height: 2,
            samples: &low,
        },
        WaveletBand {
            width: 2,
            height: 2,
            samples: &high,
        },
        4,
        true,
        &ResourceLimits::default(),
    )
    .unwrap();
    let mut expected = inverse_5_3(&low[..2], &high[..2], true).unwrap();
    expected.extend(inverse_5_3(&low[2..], &high[2..], true).unwrap());
    assert_eq!(plane.samples(), expected);
    assert_eq!((plane.width(), plane.height()), (4, 2));
}

#[test]
fn inverse_vertical_stage_matches_column_synthesis() {
    let low = [2, 6, 4, 8];
    let high = [1, 5, 3, 7];
    let plane = inverse_vertical_5_3(
        WaveletBand {
            width: 2,
            height: 2,
            samples: &low,
        },
        WaveletBand {
            width: 2,
            height: 2,
            samples: &high,
        },
        4,
        true,
        &ResourceLimits::default(),
    )
    .unwrap();
    let first = inverse_5_3(&[2, 4], &[1, 3], true).unwrap();
    let second = inverse_5_3(&[6, 8], &[5, 7], true).unwrap();
    let mut expected = Vec::new();
    let mut y = 0_usize;
    while y < 4 {
        expected.push(first[y]);
        expected.push(second[y]);
        y += 1;
    }
    assert_eq!(plane.samples(), expected);
    assert_eq!((plane.width(), plane.height()), (2, 4));
}

#[test]
fn reverses_five_three_lifting_for_known_samples() {
    assert_eq!(inverse_5_3(&[3, 7], &[2], true).unwrap(), [2, 6, 6]);
    assert_eq!(inverse_5_3(&[3], &[], true).unwrap(), [3]);
}

#[test]
fn reconstructs_two_dimensional_reversible_level() {
    let ll = [5];
    let hl = [0];
    let lh = [0];
    let hh = [0];
    let plane = inverse_level_5_3(
        WaveletLevel {
            ll: WaveletBand {
                width: 1,
                height: 1,
                samples: &ll,
            },
            hl: WaveletBand {
                width: 1,
                height: 1,
                samples: &hl,
            },
            lh: WaveletBand {
                width: 1,
                height: 1,
                samples: &lh,
            },
            hh: WaveletBand {
                width: 1,
                height: 1,
                samples: &hh,
            },
            output_width: 2,
            output_height: 2,
            low_pass_first_x: true,
            low_pass_first_y: true,
        },
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(plane.samples(), [5, 5, 5, 5]);
}

#[test]
fn applies_quantization_roi_and_output_conversion() {
    assert_eq!(undo_maxshift(32, 3).unwrap(), 4);
    assert_eq!(undo_maxshift(-32, 3).unwrap(), -4);
    assert_eq!(undo_maxshift(3, 3).unwrap(), 3);

    let plane = inverse_quantize(
        &[0, 2, -2],
        QuantizationStep {
            exponent: 8,
            mantissa: 0,
        },
        8,
        false,
        0,
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(plane.fraction_bits(), FIXED_BITS);
    assert_eq!(
        convert_samples(&plane, 8, true, &ResourceLimits::default()).unwrap(),
        [0, 3, -2]
    );
}

#[test]
fn undoes_maximum_maxshift_before_narrowing_and_quantization() {
    let limits = ResourceLimits::default();
    let shifted = SignedMagnitude {
        magnitude: Magnitude::single_bit(291).unwrap(),
        negative: true,
    };
    assert_eq!(
        undo_maxshift_magnitude(shifted, u8::MAX).unwrap(),
        -(1_i64 << 36)
    );
    let plane = inverse_quantize_magnitudes(
        &[shifted],
        QuantizationStep {
            exponent: 0,
            mantissa: 0,
        },
        38,
        true,
        u8::MAX,
        &limits,
    )
    .unwrap();
    assert_eq!(plane.samples(), &[-(1_i64 << 36)]);
    assert_eq!(undo_maxshift(17, u8::MAX).unwrap(), 17);
}

#[test]
fn bounds_output_and_rejects_bad_band_geometry() {
    let limits = ResourceLimits::default()
        .with_maximum_decoded_bytes(8)
        .unwrap();
    assert!(
        inverse_quantize(
            &[1, 2],
            QuantizationStep {
                exponent: 0,
                mantissa: 0,
            },
            8,
            true,
            0,
            &limits,
        )
        .is_err()
    );
}
#[test]
fn inverse_lifting_separates_sample_parity_from_predict_update_roles() {
    assert_eq!(inverse_5_3(&[2], &[-1, 1], false).unwrap(), vec![1, 2, 3]);
    assert_eq!(inverse_5_3(&[], &[18], false).unwrap(), vec![9]);
    assert_eq!(inverse_5_3(&[], &[-18], false).unwrap(), vec![-9]);
}

#[test]
fn inverse_nine_seven_preserves_constant_and_singleton_samples() {
    let constant = 72 * FIXED_ONE;
    let restored = inverse_9_7(&[constant, constant], &[0, 0], true).unwrap();
    assert!(
        restored
            .iter()
            .all(|sample| (*sample - constant).abs() < 256)
    );
    assert_eq!(inverse_9_7(&[constant], &[], true).unwrap(), vec![constant]);
}
