use super::*;
use crate::tier1::{ExtractionTestCoefficient, SubbandOrientation, extraction_test_plane};
use crate::transform::QuantizationStep;

fn geometry(
    width: u32,
    height: u32,
    step: QuantizationStep,
    range: u8,
    roi_shift: u8,
) -> SubbandGeometry {
    SubbandGeometry {
        resolution: 0,
        orientation: SubbandOrientation::Ll,
        x0: 0,
        y0: 0,
        width,
        height,
        resolution_width: width,
        resolution_height: height,
        quantization_index: 0,
        quantization_step: step,
        dynamic_range: range,
        significant_bitplanes: 361,
        roi_shift,
        low_pass_first_x: true,
        low_pass_first_y: true,
    }
}

fn destination(width: u32, height: u32, reversible: bool) -> WorkingSubband {
    WorkingSubband {
        width,
        height,
        fraction_bits: if reversible { 0 } else { 16 },
        samples: vec![97; (width * height) as usize],
        visited: vec![false; (width * height) as usize],
    }
}

fn snapshot(value: &WorkingSubband) -> (u32, u32, u8, Vec<i64>, Vec<bool>) {
    (
        value.width,
        value.height,
        value.fraction_bits,
        value.samples.clone(),
        value.visited.clone(),
    )
}

fn legacy_place(
    plane: &CodeBlockPlane,
    destination: &mut WorkingSubband,
    geometry: SubbandGeometry,
    x: u32,
    y: u32,
    reversible: bool,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    let width = u32::from(plane.width());
    let height = u32::from(plane.height());
    if x.checked_add(width).ok_or_else(arithmetic_overflow)? > geometry.width
        || y.checked_add(height).ok_or_else(arithmetic_overflow)? > geometry.height
    {
        return Err(invalid_decode());
    }
    let coefficients = collect_prepare_coefficients(plane)?;
    let quantized = inverse_quantize_magnitudes(
        &coefficients,
        geometry.quantization_step,
        geometry.dynamic_range,
        reversible,
        geometry.roi_shift,
        limits,
    )?;
    write_quantized_block(destination, quantized.samples(), width, height, x, y)
}

#[test]
fn fused_direct_placement_matches_independent_midpoint_roi_and_quantization_reference_without_allocating()
 {
    let raw: Vec<ExtractionTestCoefficient> = vec![
        (u64::MAX, [u64::MAX; 5], true, false, Some(u16::MAX)),
        (3, [0; 5], false, true, Some(0)),
        (7, [0; 5], true, true, Some(1)),
        (15, [0; 5], false, true, Some(4)),
        (0, [0; 5], true, true, Some(31)),
        (0, [0; 5], false, true, Some(64)),
        (511, [0; 5], true, true, None),
        (512, [0; 5], false, true, None),
    ];
    let plane = extraction_test_plane(4, 2, &raw);
    let source = format!("{plane:?}");
    let coefficients = collect_prepare_coefficients(&plane).unwrap();
    let input: Vec<_> = coefficients
        .iter()
        .map(|value| {
            let mut limbs = [0; 6];
            for (i, limb) in limbs.iter_mut().enumerate() {
                *limb = value.magnitude.limb(i).unwrap();
            }
            (limbs, value.negative)
        })
        .collect();
    let limits = ResourceLimits::default();
    let mut admitted = 0;
    for reversible in [false, true] {
        for (step, range) in [
            (
                QuantizationStep {
                    exponent: 8,
                    mantissa: 0,
                },
                8,
            ),
            (
                QuantizationStep {
                    exponent: 11,
                    mantissa: 137,
                },
                8,
            ),
            (
                QuantizationStep {
                    exponent: 31,
                    mantissa: 0,
                },
                1,
            ),
            (
                QuantizationStep {
                    exponent: 31,
                    mantissa: 0,
                },
                38,
            ),
        ] {
            for shift in [0, 1, 5, 31, 63, 64, 255] {
                let shape = geometry(6, 4, step, range, shift);
                let mut actual = destination(6, 4, reversible);
                let mut expected = destination(6, 4, reversible);
                let reference = crate::transform::tests::reference_reconstruction(
                    &input,
                    step,
                    range,
                    reversible,
                    shift,
                    limits.maximum_decoded_bytes(),
                )
                .and_then(|(_, _, _, samples)| {
                    write_quantized_block(&mut expected, &samples, 4, 2, 1, 1)
                });
                let eligible = preflight(&plane, &actual, shape, 1, 1, reversible, &limits)
                    .unwrap()
                    .is_some();
                if eligible {
                    admitted += 1;
                    crate::allocation::with_refusal(0, || {
                        assert_eq!(
                            place(&plane, &mut actual, shape, 1, 1, reversible, &limits),
                            reference
                        );
                        assert_eq!(
                            crate::allocation::copy_i64_values(&[1]),
                            Err(DecodeError::AllocationFailed)
                        );
                    });
                } else {
                    assert_eq!(
                        place(&plane, &mut actual, shape, 1, 1, reversible, &limits),
                        reference
                    );
                }
                assert_eq!(snapshot(&actual), snapshot(&expected));
                assert_eq!(format!("{plane:?}"), source);
            }
        }
    }
    assert!(admitted > 0);
    // ROI restoration is not monotone across the threshold.
    let roi = extraction_test_plane(
        2,
        1,
        &[
            (511, [0; 5], false, true, None),
            (512, [0; 5], false, true, None),
        ],
    );
    let shape = geometry(
        2,
        1,
        QuantizationStep {
            exponent: 0,
            mantissa: 0,
        },
        38,
        9,
    );
    assert!(
        preflight(&roi, &destination(2, 1, false), shape, 0, 0, false, &limits)
            .unwrap()
            .is_none()
    );
    let mut actual = destination(2, 1, false);
    let mut expected = destination(2, 1, false);
    assert_eq!(
        place(&roi, &mut actual, shape, 0, 0, false, &limits),
        legacy_place(&roi, &mut expected, shape, 0, 0, false, &limits)
    );
    assert_eq!(snapshot(&actual), snapshot(&expected));
}

#[test]
fn fused_fallback_preserves_real_staging_refusals_numeric_priority_and_partial_placement() {
    let limits = ResourceLimits::default();
    let normal = extraction_test_plane(2, 2, &[(7, [0; 5], false, true, None); 4]);
    let short = extraction_test_plane(2, 2, &[(7, [0; 5], false, true, None); 3]);
    let bad = extraction_test_plane(2, 2, &[(7, [0; 5], true, true, Some(u16::MAX)); 4]);
    let wide = extraction_test_plane(2, 2, &[(0, [1, 0, 0, 0, 0], true, true, None); 4]);
    let step = QuantizationStep {
        exponent: 8,
        mantissa: 0,
    };
    for (plane, mut shape, maximum, overlap) in [
        (&normal, geometry(3, 2, step, 8, 0), u64::MAX, true),
        (&short, geometry(3, 2, step, 8, 0), u64::MAX, false),
        (&bad, geometry(3, 2, step, 8, 0), u64::MAX, true),
        (&wide, geometry(3, 2, step, 8, 64), u64::MAX, false),
        (&normal, geometry(3, 2, step, 0, 0), u64::MAX, true),
        (&normal, geometry(3, 2, step, 8, 0), 8, true),
    ] {
        let capped = if maximum == u64::MAX {
            ResourceLimits::default()
        } else {
            limits.with_maximum_decoded_bytes(maximum).unwrap()
        };
        for after in 0..=2 {
            let mut actual = destination(3, 2, true);
            let mut expected = destination(3, 2, true);
            if overlap {
                actual.visited[5] = true;
                expected.visited[5] = true;
            }
            assert!(
                preflight(plane, &actual, shape, 1, 0, true, &capped)
                    .unwrap()
                    .is_none()
            );
            let a = crate::allocation::with_refusal(after, || {
                place(plane, &mut actual, shape, 1, 0, true, &capped)
            });
            let b = crate::allocation::with_refusal(after, || {
                legacy_place(plane, &mut expected, shape, 1, 0, true, &capped)
            });
            assert_eq!(a, b);
            assert_eq!(snapshot(&actual), snapshot(&expected));
        }
        shape.width = 0;
        assert_eq!(
            place(
                plane,
                &mut destination(3, 2, true),
                shape,
                1,
                0,
                true,
                &limits
            ),
            Err(invalid_decode())
        );
    }
    let mut actual = destination(3, 2, true);
    actual.visited[5] = true;
    assert_eq!(
        place(
            &normal,
            &mut actual,
            geometry(3, 2, step, 8, 0),
            1,
            0,
            true,
            &limits
        ),
        Err(invalid_decode())
    );
    assert_eq!(actual.samples, [97, 7, 7, 97, 7, 97]);
}

#[cfg(feature = "cooperative-deadlines")]
#[test]
fn fused_deadline_preflight_rejects_without_mutation_and_restores() {
    use std::time::{Duration, Instant};
    let plane = extraction_test_plane(2, 1, &[(7, [0; 5], false, true, None); 2]);
    let shape = geometry(
        2,
        1,
        QuantizationStep {
            exponent: 8,
            mantissa: 0,
        },
        8,
        0,
    );
    let limits = ResourceLimits::default();
    let mut actual = destination(2, 1, true);
    let before = snapshot(&actual);
    assert_eq!(
        crate::deadline::with_decode_deadline(Instant::now() + Duration::from_millis(5), || {
            std::thread::sleep(Duration::from_millis(15));
            assert_eq!(
                place(&plane, &mut actual, shape, 0, 0, true, &limits),
                Err(DecodeError::DeadlineExceeded)
            );
            Ok(())
        }),
        Err(DecodeError::DeadlineExceeded)
    );
    assert_eq!(snapshot(&actual), before);
    assert_eq!(
        place(&plane, &mut actual, shape, 0, 0, true, &limits),
        Ok(())
    );
}
