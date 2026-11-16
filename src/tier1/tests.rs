use super::*;

#[test]
fn ht_cleanup_scratch_storage_raw_metadata_rows_first_later_and_exact_output_restore() {
    let limits = ResourceLimits::default();
    let mut plane = CodeBlockPlane::new(1, 2).unwrap();
    plane.coefficients[0] = CoefficientState {
        magnitude: 17,
        magnitude_high: [1, 2, 3, 4, 5],
        significant: true,
        ..CoefficientState::default()
    };
    let before = plane.clone();
    let cleanup = parse_ht_block_segments(&[0xfa, 2, 0], None, &limits)
        .unwrap()
        .cleanup();
    let metadata = plane_metadata(1, 2, vec![plane_quad(0, 0, 3, 2)]);
    let expected = reconstruct_ht_cleanup_plane(&plane, cleanup, &metadata, 2, 3, &limits).unwrap();
    for after in [1, 2] {
        assert_eq!(
            crate::allocation::with_refusal(after, || reconstruct_ht_cleanup_plane(
                &plane, cleanup, &metadata, 2, 3, &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(plane, before);
        assert_eq!(
            reconstruct_ht_cleanup_plane(&plane, cleanup, &metadata, 2, 3, &limits).unwrap(),
            expected
        );
    }
    let malformed = plane_metadata(3, 0, Vec::new());
    let ordinary = reconstruct_ht_cleanup_plane(&plane, cleanup, &malformed, 255, 0, &limits);
    assert_ne!(ordinary, Err(DecodeError::AllocationFailed));
    for after in [1, 2] {
        assert_eq!(
            crate::allocation::with_refusal(after, || reconstruct_ht_cleanup_plane(
                &plane, cleanup, &malformed, 255, 0, &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(
            reconstruct_ht_cleanup_plane(&plane, cleanup, &malformed, 255, 0, &limits),
            ordinary
        );
    }
}

#[test]
fn ht_cleanup_scratch_storage_original_width_plane_admission_and_empty_quad_order() {
    let limits = ResourceLimits::default();
    let plane = CodeBlockPlane::new(1, 1).unwrap();
    let cleanup = parse_ht_block_segments(&[0, 0x63, 0], None, &limits)
        .unwrap()
        .cleanup();
    let empty = plane_metadata(1, 1, Vec::new());
    let expected = reconstruct_ht_cleanup_plane(&plane, cleanup, &empty, 255, 0, &limits);
    assert_ne!(expected, Err(DecodeError::AllocationFailed));
    for after in [1, 2] {
        assert_eq!(
            crate::allocation::with_refusal(after, || reconstruct_ht_cleanup_plane(
                &plane, cleanup, &empty, 255, 0, &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(
            reconstruct_ht_cleanup_plane(&plane, cleanup, &empty, 255, 0, &limits),
            expected
        );
    }
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            reconstruct_ht_cleanup_plane(
                &plane,
                cleanup,
                &plane_metadata(0, 1, Vec::new()),
                0,
                0,
                &limits
            ),
            Err(invalid_code_block())
        );
        let raw = CodeBlockPlane {
            width: 0,
            height: 1,
            coefficients: Vec::new(),
        };
        assert_eq!(
            reconstruct_ht_cleanup_plane(&raw, cleanup, &empty, 0, 0, &limits),
            Err(invalid_code_block())
        );
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn ht_cleanup_scratch_storage_real_decoder_refusal_keeps_prior_refinement_before_clear() {
    let limits = ResourceLimits::default();
    let mut base = tier1_plane_storage_ht_decoder();
    base.ht_refinement_data = vec![7];
    base.ht_refinement_passes = 1;
    let before = format!("{base:?}");
    let mut expected = base.clone();
    let result = expected
        .decode_high_throughput_segments(&[0, 0x63, 0], 1, Some(&[0]), 1, &limits)
        .unwrap();
    for after in [4, 5] {
        let mut decoder = base.clone();
        assert_eq!(
            crate::allocation::with_refusal(after, || decoder.decode_high_throughput_segments(
                &[0, 0x63, 0],
                1,
                Some(&[0]),
                1,
                &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(format!("{decoder:?}"), before);
        assert_eq!(
            decoder
                .decode_high_throughput_segments(&[0, 0x63, 0], 1, Some(&[0]), 1, &limits)
                .unwrap(),
            result
        );
        assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
    }
}

#[test]
fn bitplane_initial_storage_raw_values_first_later_restore_empty_and_original_admission() {
    let mut plane = CodeBlockPlane {
        width: 0,
        height: u16::MAX,
        coefficients: vec![
            CoefficientState {
                significant: true,
                negative: true,
                magnitude: 17,
                ..CoefficientState::default()
            },
            CoefficientState::default(),
            CoefficientState {
                significant: true,
                magnitude_high: [1, 2, 3, 4, 5],
                ..CoefficientState::default()
            },
        ],
    };
    let before = plane.clone();
    for bitplane in [0, MAX_TIER1_BITPLANES - 1] {
        for after in [0, 1] {
            assert_eq!(
                crate::allocation::with_refusal(after, || Tier1BitplaneState::new_at_bitplane(
                    &plane, bitplane
                )),
                Err(DecodeError::AllocationFailed)
            );
            assert_eq!(plane, before);
            let restored = Tier1BitplaneState::new_at_bitplane(&plane, bitplane).unwrap();
            assert_eq!(
                (restored.width, restored.height, restored.bitplane),
                (0, u16::MAX, bitplane)
            );
            assert_eq!(restored.significant_before, &[true, false, true]);
            assert_eq!(restored.significance_visited, &[false, false, false]);
            assert!(
                !restored.significance_propagation_complete
                    && !restored.magnitude_refinement_complete
                    && !restored.cleanup_complete
            );
        }
    }
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            Tier1BitplaneState::new_at_bitplane(&plane, MAX_TIER1_BITPLANES),
            Err(invalid_code_block())
        );
        assert_eq!(
            Tier1BitplaneState::new(&plane, 0),
            Err(invalid_code_block())
        );
        assert_eq!(
            Tier1BitplaneState::new(&plane, 3),
            Err(invalid_code_block())
        );
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
    plane.coefficients.clear();
    crate::allocation::with_refusal(0, || {
        assert!(
            Tier1BitplaneState::new_at_bitplane(&plane, MAX_TIER1_BITPLANES - 1)
                .unwrap()
                .significant_before
                .is_empty()
        );
        assert!(
            Tier1BitplaneState::new(&plane, 4)
                .unwrap()
                .significance_visited
                .is_empty()
        );
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn bitplane_initial_storage_real_mq_setup_refusal_keeps_prior_reset_and_present_state_skips_requests()
 {
    let mut source =
        Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, Tier1CodingStyle::default())
            .unwrap();
    source.reset_contexts_before_mq = true;
    let mut reset = source.clone();
    reset.reset_contexts_before_mq = false;
    let limits = ResourceLimits::default();
    let mut expected = source.clone();
    let decoded = expected.decode_segment(&[0xff], 1, &limits).unwrap();
    for after in [0, 1] {
        let mut current = source.clone();
        assert_eq!(
            crate::allocation::with_refusal(after, || current.decode_segment(&[0xff], 1, &limits)),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(format!("{current:?}"), format!("{reset:?}"));
        assert_eq!(
            current.decode_segment(&[0xff], 1, &limits).unwrap(),
            decoded
        );
        assert_eq!(format!("{current:?}"), format!("{expected:?}"));
    }
    let limited = ResourceLimits::default()
        .with_maximum_input_bytes(0)
        .unwrap();
    crate::allocation::with_refusal(0, || {
        let mut current = source.clone();
        assert!(matches!(
            current.decode_segment(&[0xff], 1, &limited),
            Err(DecodeError::LimitExceeded {
                resource: Resource::InputBytes,
                ..
            })
        ));
        assert_eq!(format!("{current:?}"), format!("{source:?}"));
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
    source.bitplane_state =
        Some(Tier1BitplaneState::new_at_bitplane(&source.plane, source.bitplane).unwrap());
    let work = ResourceLimits::default()
        .with_maximum_work_units(0)
        .unwrap();
    let mut normal = source.clone();
    let expected_error = normal.decode_segment(&[0xff], 1, &work);
    assert!(matches!(
        expected_error,
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            ..
        })
    ));
    crate::allocation::with_refusal(0, || {
        let mut current = source.clone();
        assert_eq!(current.decode_segment(&[0xff], 1, &work), expected_error);
        assert_eq!(format!("{current:?}"), format!("{normal:?}"));
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn legacy_snapshot_storage_raw_snapshot_first_later_empty_and_exact_source_restore() {
    let mut source = retained_refinement_decoder();
    source.plane.width = 0;
    source.bitplane_state = Some(nested_copy_raw_flags());
    let before = format!("{source:?}");
    let expected = format!("{:?}", source.legacy_segment_snapshot().unwrap());
    for after in [0, 1, 2] {
        assert!(matches!(
            crate::allocation::with_refusal(after, || source.legacy_segment_snapshot()),
            Err(DecodeError::AllocationFailed)
        ));
        assert_eq!(format!("{source:?}"), before);
        let copied = source.legacy_segment_snapshot().unwrap();
        assert_eq!(format!("{copied:?}"), expected);
        assert_eq!(copied.plane, source.plane);
        assert_eq!(copied.bitplane_state, source.bitplane_state);
        assert!(copied.input.is_empty());
        assert_eq!(copied.passes, 0);
    }
    source.plane.coefficients.clear();
    let flags = source.bitplane_state.as_mut().unwrap();
    flags.significant_before.clear();
    flags.significance_visited.clear();
    crate::allocation::with_refusal(0, || {
        assert!(source.legacy_segment_snapshot().unwrap().input.is_empty());
        source.bitplane_state = None;
        assert!(
            source
                .legacy_segment_snapshot()
                .unwrap()
                .bitplane_state
                .is_none()
        );
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn legacy_snapshot_storage_restore_refusal_exposes_exact_partial_fields_without_consuming_source() {
    let mut original = retained_refinement_decoder();
    original.plane.width = 0;
    original.bitplane_state = Some(nested_copy_raw_flags());
    let mut source = original.legacy_segment_snapshot().unwrap();
    source.next_pass = u32::MAX;
    source.bitplane = u16::MAX;
    source.input = vec![7, 8];
    source.passes = 19;
    let source_before = format!("{source:?}");
    let mut target = legacy_raw_pair_decoder(1);
    target.next_pass = 3;
    target.bitplane = 1;
    target.decoded_segments = 29;
    target.decoded_bytes = 31;
    target.reset_contexts_before_mq = !source.reset_contexts_before_mq;
    let before = format!("{target:?}");
    let mut partial = target.clone();
    partial.plane = source.plane.clone();
    partial.next_pass = source.next_pass;
    partial.bitplane = source.bitplane;
    let mut complete = target.clone();
    complete.restore_legacy_segment(&source).unwrap();
    for after in [0, 1, 2] {
        let mut current = target.clone();
        assert_eq!(
            crate::allocation::with_refusal(after, || current.restore_legacy_segment(&source)),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(
            format!("{current:?}"),
            if after == 0 {
                before.clone()
            } else {
                format!("{partial:?}")
            }
        );
        assert_eq!(format!("{source:?}"), source_before);
        current.restore_legacy_segment(&source).unwrap();
        assert_eq!(format!("{current:?}"), format!("{complete:?}"));
    }
    source.plane.coefficients.clear();
    let flags = source.bitplane_state.as_mut().unwrap();
    flags.significant_before.clear();
    flags.significance_visited.clear();
    crate::allocation::with_refusal(0, || {
        target.restore_legacy_segment(&source).unwrap();
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
    assert_eq!(source.input, &[7, 8]);
}

#[test]
fn legacy_snapshot_storage_real_replay_refusal_retains_admission_and_partial_restore_frames() {
    let limits = ResourceLimits::default();
    let mut source = legacy_raw_pair_decoder(1);
    source.bitplane_state = Some(legacy_bitplane_from_plane(&source.plane, 2).unwrap());
    let mut admitted = source.clone();
    admitted.legacy_decode_work = 2;
    for after in [0, 1, 2, 3, 4, 5] {
        let mut current = source.clone();
        assert_eq!(
            crate::allocation::with_refusal(after, || current.decode_legacy_contribution(
                &[0xaa],
                1,
                &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(format!("{current:?}"), format!("{admitted:?}"));
    }
    source
        .decode_legacy_contribution(&[0xaa], 1, &limits)
        .unwrap();
    let retained = source.legacy_segment.as_ref().unwrap().clone();
    let mut cleared = source.clone();
    cleared.legacy_decode_work = 5;
    cleared.legacy_segment = None;
    let mut partial = cleared.clone();
    partial.plane = retained.plane.clone();
    partial.next_pass = retained.next_pass;
    partial.bitplane = retained.bitplane;
    for after in [0, 1, 2] {
        let mut current = source.clone();
        assert_eq!(
            crate::allocation::with_refusal(after, || current.decode_legacy_contribution(
                &[],
                1,
                &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(
            format!("{current:?}"),
            if after == 0 {
                format!("{cleared:?}")
            } else {
                format!("{partial:?}")
            }
        );
    }
    let mut recovered = source.clone();
    recovered
        .decode_legacy_contribution(&[], 1, &limits)
        .unwrap();
    let mut whole = legacy_raw_pair_decoder(1);
    whole.bitplane_state = Some(legacy_bitplane_from_plane(&whole.plane, 2).unwrap());
    whole
        .decode_legacy_contribution(&[0xaa], 2, &limits)
        .unwrap();
    assert_eq!(recovered.plane, whole.plane);
    assert_eq!(recovered.next_pass, whole.next_pass);
}

fn nested_copy_raw_flags() -> Tier1BitplaneState {
    Tier1BitplaneState {
        width: 0,
        height: u16::MAX,
        bitplane: u16::MAX,
        significant_before: vec![true, false, true],
        significance_visited: vec![false],
        significance_propagation_complete: true,
        magnitude_refinement_complete: false,
        cleanup_complete: true,
    }
}

#[test]
fn decoder_nested_storage_raw_flags_first_later_empty_and_clone_preserve_every_field() {
    let mut source = nested_copy_raw_flags();
    let before = source.clone();
    for role in [
        HtRefinementCopyRole::HtStaging,
        HtRefinementCopyRole::PacketStaging,
    ] {
        for legacy in [false, true] {
            for after in [0, 1] {
                assert_eq!(
                    crate::allocation::with_refusal(after, || source.try_duplicate(role, legacy)),
                    Err(DecodeError::AllocationFailed)
                );
                assert_eq!(source, before);
                assert_eq!(source.try_duplicate(role, legacy).unwrap(), before);
            }
        }
    }
    source.significant_before.clear();
    assert_eq!(
        crate::allocation::with_refusal(0, || source
            .try_duplicate(HtRefinementCopyRole::PacketStaging, true)),
        Err(DecodeError::AllocationFailed)
    );
    source.significance_visited.clear();
    crate::allocation::with_refusal(0, || {
        assert_eq!(source.clone(), source);
        assert_eq!(
            source
                .try_duplicate(HtRefinementCopyRole::HtStaging, false)
                .unwrap(),
            source
        );
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn decoder_nested_storage_primary_flags_legacy_plane_flags_input_cleanup_byte_order_restore() {
    let mut source = retained_refinement_decoder();
    source.bitplane_state = Some(nested_copy_raw_flags());
    let legacy = source.legacy_segment.as_mut().unwrap();
    legacy.plane.width = 0;
    legacy.plane.height = u16::MAX;
    legacy.bitplane_state = Some(nested_copy_raw_flags());
    source.ht_refinement_data = vec![7];
    let before = format!("{source:?}");
    for role in [
        HtRefinementCopyRole::HtStaging,
        HtRefinementCopyRole::PacketStaging,
    ] {
        for after in [0, 1, 2, 3, 4, 5, 6, 7, 8] {
            assert!(matches!(
                crate::allocation::with_refusal(after, || source.try_duplicate(role)),
                Err(DecodeError::AllocationFailed)
            ));
            assert_eq!(format!("{source:?}"), before);
            assert_eq!(format!("{:?}", source.try_duplicate(role).unwrap()), before);
        }
    }
    source.plane.coefficients.clear();
    source
        .ht_cleanup_plane
        .as_mut()
        .unwrap()
        .coefficients
        .clear();
    source.ht_refinement_data.clear();
    for flags in [
        &mut source.bitplane_state,
        &mut source.legacy_segment.as_mut().unwrap().bitplane_state,
    ] {
        let flags = flags.as_mut().unwrap();
        flags.significant_before.clear();
        flags.significance_visited.clear();
    }
    let legacy = source.legacy_segment.as_mut().unwrap();
    legacy.plane.coefficients.clear();
    legacy.input.clear();
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            format!(
                "{:?}",
                source
                    .try_duplicate(HtRefinementCopyRole::PacketStaging)
                    .unwrap()
            ),
            format!("{source:?}")
        );
        source.bitplane_state = None;
        source.legacy_segment = None;
        assert_eq!(
            format!(
                "{:?}",
                source
                    .try_duplicate(HtRefinementCopyRole::HtStaging)
                    .unwrap()
            ),
            format!("{source:?}")
        );
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn decoder_plane_storage_raw_sources_copy_without_dimension_admission_or_false_empty_event() {
    let source = CodeBlockPlane {
        width: 0,
        height: u16::MAX,
        coefficients: vec![CoefficientState {
            magnitude: 17,
            magnitude_high: [1, 2, 3, 4, 5],
            negative: true,
            significant: false,
            refined: true,
            legacy_bitplane: Some(u16::MAX),
        }],
    };
    let before = source.clone();
    for cleanup in [false, true] {
        assert_eq!(
            crate::allocation::with_refusal(0, || source.try_duplicate_raw(
                HtRefinementCopyRole::PacketStaging,
                cleanup,
                false
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(source, before);
        assert_eq!(
            source
                .try_duplicate_raw(HtRefinementCopyRole::PacketStaging, cleanup, false)
                .unwrap(),
            before
        );
    }
    let empty = CodeBlockPlane {
        width: u16::MAX,
        height: 0,
        coefficients: Vec::new(),
    };
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            empty
                .try_duplicate_raw(HtRefinementCopyRole::HtStaging, false, false)
                .unwrap(),
            empty
        );
        assert_eq!(source.clone(), before);
        assert_eq!(
            source.try_duplicate_raw(HtRefinementCopyRole::HtStaging, false, false),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn decoder_plane_storage_primary_optional_cleanup_and_byte_order_restore_all_fields() {
    let mut source = retained_refinement_decoder();
    source.plane.width = 0;
    source.ht_cleanup_plane.as_mut().unwrap().height = 0;
    source.ht_refinement_data = vec![7];
    let before = format!("{source:?}");
    for role in [
        HtRefinementCopyRole::HtStaging,
        HtRefinementCopyRole::PacketStaging,
    ] {
        for after in [0, 3, 4] {
            assert!(matches!(
                crate::allocation::with_refusal(after, || source.try_duplicate(role)),
                Err(DecodeError::AllocationFailed)
            ));
            assert_eq!(format!("{source:?}"), before);
            assert_eq!(format!("{:?}", source.try_duplicate(role).unwrap()), before);
        }
    }
    source.plane.coefficients.clear();
    source
        .ht_cleanup_plane
        .as_mut()
        .unwrap()
        .coefficients
        .clear();
    source.ht_refinement_data.clear();
    crate::allocation::with_refusal(4, || {
        assert_eq!(
            format!(
                "{:?}",
                source
                    .try_duplicate(HtRefinementCopyRole::PacketStaging)
                    .unwrap()
            ),
            format!("{source:?}")
        );
        source.ht_cleanup_plane = None;
        assert_eq!(
            format!(
                "{:?}",
                source
                    .try_duplicate(HtRefinementCopyRole::HtStaging)
                    .unwrap()
            ),
            format!("{source:?}")
        );
        assert_eq!(
            crate::allocation::copy_values(&[1_u8]),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn ht_refinement_storage_checked_staging_copy_keeps_clone_fields_and_empty_frontier() {
    let mut source = retained_refinement_decoder();
    source.ht_refinement_data = vec![1, 7, 0xff];
    let before = format!("{source:?}");
    for role in [
        HtRefinementCopyRole::HtStaging,
        HtRefinementCopyRole::PacketStaging,
    ] {
        assert!(matches!(
            crate::allocation::with_refusal(4, || source.try_duplicate(role)),
            Err(DecodeError::AllocationFailed)
        ));
        assert_eq!(format!("{source:?}"), before);
        assert_eq!(format!("{:?}", source.try_duplicate(role).unwrap()), before);
    }
    crate::allocation::with_refusal(4, || {
        assert_eq!(format!("{:?}", source.clone()), before);
        assert!(matches!(
            source.try_duplicate(HtRefinementCopyRole::HtStaging),
            Err(DecodeError::AllocationFailed)
        ));
    });
    source.ht_refinement_data.clear();
    crate::allocation::with_refusal(4, || {
        assert_eq!(
            format!(
                "{:?}",
                source
                    .try_duplicate(HtRefinementCopyRole::PacketStaging)
                    .unwrap()
            ),
            format!("{source:?}")
        );
        assert_eq!(
            super::ht_refinement::copy_ht_refinement_bytes(
                &[],
                HtRefinementCopyRole::CleanupRetention
            ),
            Ok(Vec::new())
        );
        assert_eq!(
            super::ht_refinement::copy_ht_refinement_bytes(
                &[1],
                HtRefinementCopyRole::CleanupRetention
            ),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn ht_refinement_storage_replay_copy_preserves_earlier_limits_later_length_and_state() {
    let limits = ResourceLimits::default();
    let mut base = retained_refinement_decoder();
    base.next_pass = 2;
    base.ht_refinement_passes = 1;
    base.ht_refinement_data = vec![1];
    let before = format!("{base:?}");
    let mut expected = base.clone();
    let expected_result = expected
        .decode_high_throughput_refinement(&[1], 1, &limits)
        .unwrap();
    for after in [0, 1, 5] {
        let mut actual = base.clone();
        assert_eq!(
            crate::allocation::with_refusal(after, || actual.decode_high_throughput_refinement(
                &[1],
                1,
                &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(format!("{actual:?}"), before);
        assert_eq!(
            actual
                .decode_high_throughput_refinement(&[1], 1, &limits)
                .unwrap(),
            expected_result
        );
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }
    let oversized = vec![0; MAX_HT_REFINEMENT_BYTES];
    let mut actual = base.clone();
    assert_eq!(
        crate::allocation::with_refusal(0, || actual
            .decode_high_throughput_refinement(&oversized, 1, &limits)),
        Err(DecodeError::AllocationFailed)
    );
    assert_eq!(
        actual.decode_high_throughput_refinement(&oversized, 1, &limits),
        Err(invalid_code_block())
    );
    assert_eq!(format!("{actual:?}"), before);
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            actual.decode_high_throughput_refinement(&[1], 0, &limits),
            Err(invalid_code_block())
        );
        assert_eq!(
            actual.decode_high_throughput_refinement(&[1], 1, &limits),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn ht_refinement_storage_retention_refusal_keeps_cleared_state_and_staging_rolls_back() {
    let limits = ResourceLimits::default();
    let mut actual = tier1_plane_storage_ht_decoder();
    actual.ht_refinement_data = vec![9];
    actual.ht_refinement_passes = 1;
    let mut cleared = actual.clone();
    cleared.ht_refinement_data.clear();
    cleared.ht_refinement_passes = 0;
    assert_eq!(
        crate::allocation::with_refusal(7, || actual.decode_high_throughput_segments(
            &[0, 0x63, 0],
            1,
            Some(&[0]),
            1,
            &limits
        )),
        Err(DecodeError::AllocationFailed)
    );
    assert_eq!(format!("{actual:?}"), format!("{cleared:?}"));
    assert!(
        actual
            .decode_high_throughput_segments(&[0, 0x63, 0], 1, Some(&[0]), 1, &limits)
            .is_ok()
    );
    let mut staged = tier1_plane_storage_ht_decoder();
    staged.ht_refinement_data = vec![9];
    let before = format!("{staged:?}");
    assert_eq!(
        crate::allocation::with_refusal(1, || staged.decode_ht_staged_group(
            &[0, 0x63, 0],
            1,
            &limits
        )),
        Err(DecodeError::AllocationFailed)
    );
    assert_eq!(format!("{staged:?}"), before);
    assert!(
        staged
            .decode_ht_staged_group(&[0, 0x63, 0], 1, &limits)
            .is_ok()
    );
}

#[test]
fn tier1_plane_storage_standalone_duplicate_frontiers_and_exact_restore() {
    let mut source = CodeBlockPlane::new(1, 1).unwrap();
    source.coefficients[0] = CoefficientState {
        magnitude: 17,
        negative: true,
        significant: true,
        ..CoefficientState::default()
    };
    let before = source.coefficients.clone();
    crate::allocation::with_refusal(0, || {
        assert_eq!(CodeBlockPlane::new(0, 1), Err(invalid_code_block()));
        assert_eq!(CodeBlockPlane::new(65, 64), Err(invalid_code_block()));
        assert_eq!(
            CodeBlockPlane::new(1, 1),
            Err(DecodeError::AllocationFailed)
        );
    });
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            source.duplicate(CoefficientStorageRole::Duplicate),
            Err(DecodeError::AllocationFailed)
        )
    });
    let malformed = CodeBlockPlane {
        width: 1,
        height: 1,
        coefficients: Vec::new(),
    };
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            malformed.duplicate(CoefficientStorageRole::Duplicate),
            Err(DecodeError::AllocationFailed)
        )
    });
    crate::allocation::with_refusal(1, || {
        assert_eq!(
            malformed.duplicate(CoefficientStorageRole::Duplicate),
            Err(invalid_code_block())
        );
        assert_eq!(
            crate::allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
    assert_eq!(source.coefficients, before);
    assert_eq!(
        source
            .duplicate(CoefficientStorageRole::Duplicate)
            .unwrap()
            .coefficients,
        before
    );
}

fn tier1_plane_storage_ht_decoder() -> Tier1CodeBlockDecoder {
    Tier1CodeBlockDecoder::new(
        1,
        1,
        2,
        SubbandOrientation::Hh,
        Tier1CodingStyle::from_code_block_style(0x40).unwrap(),
    )
    .unwrap()
}

#[test]
fn tier1_plane_storage_cleanup_output_copy_refusals_restore_state_and_output() {
    let limits = ResourceLimits::default();
    let base = tier1_plane_storage_ht_decoder();
    let mut expected = base.clone();
    let result = expected
        .decode_high_throughput_segments(&[0, 0x63, 0], 1, None, 0, &limits)
        .unwrap();
    for after in [3, 6] {
        let mut actual = base.clone();
        let before = format!("{actual:?}");
        assert_eq!(
            crate::allocation::with_refusal(after, || actual.decode_high_throughput_segments(
                &[0, 0x63, 0],
                1,
                None,
                0,
                &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(format!("{actual:?}"), before);
        assert_eq!(
            actual
                .decode_high_throughput_segments(&[0, 0x63, 0], 1, None, 0, &limits)
                .unwrap(),
            result
        );
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }
    let mut actual = base.clone();
    let ordinary = actual
        .decode_high_throughput_segments(&[0], 1, None, 0, &limits)
        .err()
        .unwrap();
    assert_ne!(ordinary, DecodeError::AllocationFailed);
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            base.clone()
                .decode_high_throughput_segments(&[0], 1, None, 0, &limits)
                .err(),
            Some(ordinary)
        )
    });
}

#[test]
fn tier1_plane_storage_refinement_roles_preserve_rollback_and_cleared_partial_state() {
    let limits = ResourceLimits::default();
    let mut base = tier1_plane_storage_ht_decoder();
    base.decode_high_throughput_segments(&[0, 0x63, 0], 1, None, 0, &limits)
        .unwrap();
    let mut expected = base.clone();
    expected
        .decode_high_throughput_refinement(&[0], 1, &limits)
        .unwrap();
    for after in [0, 4] {
        let mut actual = base.clone();
        let before = format!("{actual:?}");
        assert_eq!(
            crate::allocation::with_refusal(after, || actual.decode_high_throughput_refinement(
                &[0],
                1,
                &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(format!("{actual:?}"), before);
        actual
            .decode_high_throughput_refinement(&[0], 1, &limits)
            .unwrap();
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }
    for after in [7, 11] {
        let mut actual = tier1_plane_storage_ht_decoder();
        actual.ht_refinement_data = vec![7];
        actual.ht_refinement_passes = 1;
        let mut cleared = actual.clone();
        cleared.ht_refinement_data.clear();
        cleared.ht_refinement_passes = 0;
        assert_eq!(
            crate::allocation::with_refusal(after, || actual.decode_high_throughput_segments(
                &[0, 0x63, 0],
                1,
                Some(&[0]),
                1,
                &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(format!("{actual:?}"), format!("{cleared:?}"));
    }
}

#[test]
fn tier1_initial_storage_admission_refusal_and_late_policy_order() {
    let style = Tier1CodingStyle::default();
    crate::allocation::with_refusal(0, || {
        for (width, height, bits) in [
            (0, 1, 1),
            (1, 0, 1),
            (1, 1, 0),
            (1, 1, u16::MAX),
            (65, 64, 1),
            (u16::MAX, u16::MAX, 1),
        ] {
            assert_eq!(
                tier1_configured_decoder(
                    width,
                    height,
                    bits,
                    SubbandOrientation::Ll,
                    style,
                    false,
                    74
                )
                .err(),
                Some(invalid_code_block())
            );
        }
        assert_eq!(
            tier1_configured_decoder(1, 1, 1, SubbandOrientation::Ll, style, true, 0).err(),
            Some(DecodeError::AllocationFailed)
        );
    });
    crate::allocation::with_refusal(1, || {
        assert_eq!(
            tier1_configured_decoder(1, 1, 1, SubbandOrientation::Ll, style, true, 0).err(),
            Some(invalid_code_block())
        );
        assert_eq!(
            crate::allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
    let actual =
        tier1_configured_decoder(1, 1, 1, SubbandOrientation::Ll, style, true, 73).unwrap();
    assert!(actual.allow_multiple_ht_sets);
    assert_eq!(actual.ht_magnitude_bound, 73);
}

#[test]
fn tier1_initial_storage_first_later_exact_coefficients_restore_and_separate_later_role() {
    let style = Tier1CodingStyle::default();
    let expected = tier1_decoder_from_dimensions(2, 2, 7, SubbandOrientation::Hh, style).unwrap();
    crate::allocation::with_refusal(1, || {
        let first = tier1_decoder_from_dimensions(2, 2, 7, SubbandOrientation::Hh, style).unwrap();
        assert_eq!(format!("{first:?}"), format!("{expected:?}"));
        assert_eq!(
            tier1_decoder_from_dimensions(1, 1, 1, SubbandOrientation::Ll, style).err(),
            Some(DecodeError::AllocationFailed)
        );
    });
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            CodeBlockPlane::new(1, 1),
            Err(DecodeError::AllocationFailed)
        );
    });
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            tier1_decoder_from_dimensions(1, 1, 1, SubbandOrientation::Ll, style).err(),
            Some(DecodeError::AllocationFailed)
        );
    });
    let restored = tier1_decoder_from_dimensions(2, 2, 7, SubbandOrientation::Hh, style).unwrap();
    assert_eq!(format!("{restored:?}"), format!("{expected:?}"));
    assert_eq!(
        restored.plane.coefficients,
        vec![CoefficientState::default(); 4]
    );
}

#[test]
fn configured_decoder_derives_initial_state_and_preserves_bound_admission_order() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    };
    let mut cases = 0;
    for (width, height) in [(0, 0), (1, 1), (64, 64), (65, 64), (u16::MAX, 1)] {
        for bits in [0, 1, 2, 74, 75, u16::MAX] {
            for allowed in [false, true] {
                for bound in [0, 1, 73, 74, 75, u8::MAX] {
                    for orientation in [
                        SubbandOrientation::Ll,
                        SubbandOrientation::Hl,
                        SubbandOrientation::Lh,
                        SubbandOrientation::Hh,
                    ] {
                        for seed in [0, 1, 0x7f, 0xff] {
                            let style = raw_initialization_style(seed);
                            let success = width != 0
                                && height != 0
                                && u64::from(width) * u64::from(height) <= 4096
                                && bits != 0
                                && bits <= MAX_TIER1_BITPLANES
                                && bound != 0
                                && bound <= MAX_HT_MAGNITUDE_BITS;
                            match tier1_configured_decoder(
                                width,
                                height,
                                bits,
                                orientation,
                                style,
                                allowed,
                                bound,
                            ) {
                                Err(error) => {
                                    assert!(!success);
                                    assert_eq!(error, invalid);
                                }
                                Ok(mut decoder) => {
                                    assert!(success);
                                    assert_eq!(decoder.allow_multiple_ht_sets, allowed);
                                    assert_eq!(decoder.ht_magnitude_bound, bound);
                                    decoder.allow_multiple_ht_sets = false;
                                    decoder.ht_magnitude_bound = MAX_HT_MAGNITUDE_BITS;
                                    check_initial_decoder(
                                        &decoder,
                                        width,
                                        height,
                                        bits,
                                        orientation,
                                        style,
                                    );
                                }
                            }
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 5760);
    for bound in 0..=u8::MAX {
        for bits in [0, 1, 74, 75] {
            for allowed in [false, true] {
                for seed in [0, 1, 0x7f, 0xff] {
                    let style = raw_initialization_style(seed);
                    let result = tier1_configured_decoder(
                        1,
                        1,
                        bits,
                        SubbandOrientation::Ll,
                        style,
                        allowed,
                        bound,
                    );
                    let success = bits != 0
                        && bits <= MAX_TIER1_BITPLANES
                        && bound != 0
                        && bound <= MAX_HT_MAGNITUDE_BITS;
                    match result {
                        Err(error) => {
                            assert!(!success);
                            assert_eq!(error, invalid);
                        }
                        Ok(mut decoder) => {
                            assert!(success);
                            assert_eq!(decoder.allow_multiple_ht_sets, allowed);
                            assert_eq!(decoder.ht_magnitude_bound, bound);
                            decoder.allow_multiple_ht_sets = false;
                            decoder.ht_magnitude_bound = MAX_HT_MAGNITUDE_BITS;
                            check_initial_decoder(
                                &decoder,
                                1,
                                1,
                                bits,
                                SubbandOrientation::Ll,
                                style,
                            );
                        }
                    }
                }
            }
        }
    }
}

fn raw_initialization_style(seed: u8) -> Tier1CodingStyle {
    Tier1CodingStyle {
        block_coding: match seed % 3 {
            0 => Tier1BlockCoding::Legacy,
            1 => Tier1BlockCoding::HighThroughput,
            _ => Tier1BlockCoding::Mixed,
        },
        force_high_throughput: seed & 1 != 0,
        selective_arithmetic_coding_bypass: seed & 2 != 0,
        reset_contexts: seed & 4 != 0,
        terminate_all_passes: seed & 8 != 0,
        vertical_causal_context: seed & 16 != 0,
        predictable_termination: seed & 32 != 0,
        segmentation_symbols: seed & 64 != 0,
    }
}

fn check_initial_decoder(
    decoder: &Tier1CodeBlockDecoder,
    width: u16,
    height: u16,
    bits: u16,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
) {
    assert_eq!((decoder.plane.width, decoder.plane.height), (width, height));
    assert_eq!(
        decoder.plane.coefficients.len(),
        usize::from(width) * usize::from(height)
    );
    assert!(decoder.plane.coefficients.iter().all(|coefficient| {
        coefficient.magnitude == 0
            && coefficient.magnitude_high == [0; 5]
            && coefficient.legacy_bitplane.is_none()
            && !coefficient.negative
            && !coefficient.significant
            && !coefficient.refined
    }));
    assert_eq!(decoder.orientation, orientation);
    assert_eq!(decoder.style, style);
    assert_eq!(decoder.maximum_passes, u32::from(bits) * 3 - 2);
    assert_eq!(decoder.next_pass, 0);
    assert_eq!(decoder.bitplane, bits - 1);
    assert!(decoder.zero_bitplanes.is_none());
    assert!(decoder.bitplane_state.is_none());
    assert!(decoder.mq_context_state.is_none());
    assert!(!decoder.reset_contexts_before_mq);
    assert_eq!(decoder.decoded_segments, 0);
    assert_eq!(decoder.decoded_bytes, 0);
    assert!(decoder.legacy_segment.is_none());
    assert_eq!(decoder.legacy_decode_work, 0);
    assert!(decoder.ht_cleanup_plane.is_none());
    assert!(decoder.ht_refinement_data.is_empty());
    assert_eq!(decoder.ht_refinement_passes, 0);
    assert_eq!(decoder.ht_decoded_bitplanes, 0);
    assert!(!decoder.ht_current_set_has_cleanup);
    assert_eq!(decoder.ht_sets_seen, 0);
    assert!(!decoder.allow_multiple_ht_sets);
    assert_eq!(decoder.ht_magnitude_bound, MAX_HT_MAGNITUDE_BITS);
}

#[test]
fn actual_decoder_initialization_derives_every_field_from_raw_dimensions_bits_and_style() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    };
    let mut cases = 0;
    for width in [0, 1, 2, 63, 64, 65, u16::MAX] {
        for height in [0, 1, 2, 63, 64, 65, u16::MAX] {
            for bits in [0, 1, 2, 73, 74, 75, u16::MAX] {
                for orientation in [
                    SubbandOrientation::Ll,
                    SubbandOrientation::Hl,
                    SubbandOrientation::Lh,
                    SubbandOrientation::Hh,
                ] {
                    for seed in [0, 1, 2, 3, 0x35, 0x7f, 0x80, 0xff] {
                        let style = raw_initialization_style(seed);
                        let success = bits != 0
                            && bits <= MAX_TIER1_BITPLANES
                            && width != 0
                            && height != 0
                            && u64::from(width) * u64::from(height) <= 4096;
                        for result in [
                            tier1_decoder_from_dimensions(width, height, bits, orientation, style),
                            Tier1CodeBlockDecoder::new(width, height, bits, orientation, style),
                        ] {
                            match result {
                                Ok(decoder) => {
                                    assert!(success);
                                    check_initial_decoder(
                                        &decoder,
                                        width,
                                        height,
                                        bits,
                                        orientation,
                                        style,
                                    );
                                }
                                Err(error) => {
                                    assert!(!success);
                                    assert_eq!(error, invalid);
                                }
                            }
                        }
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 10_976);
    for bits in 0..=u16::MAX {
        let style = raw_initialization_style(0xff);
        match tier1_decoder_from_dimensions(1, 1, bits, SubbandOrientation::Ll, style) {
            Ok(decoder) => {
                check_initial_decoder(&decoder, 1, 1, bits, SubbandOrientation::Ll, style)
            }
            Err(error) => {
                assert!(bits == 0 || bits > MAX_TIER1_BITPLANES);
                assert_eq!(error, invalid);
            }
        }
    }
}

#[test]
fn initialization_policy_setters_preserve_all_unrelated_raw_state_and_error_snapshots() {
    for coding in [
        Tier1BlockCoding::Legacy,
        Tier1BlockCoding::HighThroughput,
        Tier1BlockCoding::Mixed,
    ] {
        for seed in 0..=u8::MAX {
            for required in [false, true] {
                let mut style = raw_initialization_style(seed);
                style.block_coding = coding;
                let expected = Tier1CodingStyle {
                    force_high_throughput: required,
                    ..style
                };
                style.set_force_high_throughput(required);
                assert_eq!(style, expected);
            }
        }
    }
    let mut decoder = tier1_decoder_from_dimensions(
        2,
        2,
        8,
        SubbandOrientation::Hh,
        raw_initialization_style(0xa5),
    )
    .unwrap();
    decoder.plane.coefficients[0].magnitude = u64::MAX;
    decoder.plane.coefficients[0].magnitude_high = [u64::MAX; 5];
    decoder.plane.coefficients[0].negative = true;
    decoder.plane.coefficients[0].significant = true;
    decoder.plane.coefficients[0].refined = true;
    decoder.maximum_passes = u32::MAX;
    decoder.next_pass = u32::MAX;
    decoder.bitplane = u16::MAX;
    decoder.zero_bitplanes = Some(u16::MAX);
    decoder.reset_contexts_before_mq = true;
    decoder.decoded_segments = u32::MAX;
    decoder.decoded_bytes = u64::MAX;
    decoder.legacy_decode_work = u64::MAX;
    decoder.ht_cleanup_plane = Some(decoder.plane.clone());
    decoder.ht_refinement_data = vec![0xff, 0, 0xfe, 0x7f];
    decoder.ht_refinement_passes = u8::MAX;
    decoder.ht_decoded_bitplanes = u16::MAX;
    decoder.ht_current_set_has_cleanup = true;
    decoder.ht_sets_seen = u16::MAX;
    decoder.legacy_segment = Some(decoder.legacy_segment_snapshot().unwrap());
    for allowed in [false, true] {
        let mut expected = decoder.clone();
        expected.allow_multiple_ht_sets = allowed;
        decoder.set_multiple_ht_sets_allowed(allowed);
        assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
        for bound in 0..=u8::MAX {
            let mut actual = decoder.clone();
            let mut expected = decoder.clone();
            let success = bound != 0 && bound <= MAX_HT_MAGNITUDE_BITS;
            if success {
                expected.ht_magnitude_bound = bound;
            }
            let result = actual.set_ht_magnitude_bound(bound);
            assert_eq!(
                result,
                if success {
                    Ok(())
                } else {
                    Err(DecodeError::MalformedInput {
                        offset: 0,
                        kind: MalformedKind::InvalidCodeBlock,
                    })
                }
            );
            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }
    }
}

#[test]
fn complete_style_byte_parser_matches_all_native_bytes_and_flags() {
    let mut admitted = 0;
    for value in 0..=u8::MAX {
        let family = value / 64;
        let invalid = family == 2
            || (family == 1 && (value % 8 != 0 || (value / 16) % 4 != 0))
            || (family == 3 && (value % 2 != 0 || (value / 4) % 2 != 0));
        let expected = if invalid {
            Err(invalid_code_block())
        } else {
            admitted += 1;
            Ok(Tier1CodingStyle {
                block_coding: match family {
                    0 => Tier1BlockCoding::Legacy,
                    1 => Tier1BlockCoding::HighThroughput,
                    _ => Tier1BlockCoding::Mixed,
                },
                force_high_throughput: family == 1,
                selective_arithmetic_coding_bypass: value % 2 != 0,
                reset_contexts: (value / 2) % 2 != 0,
                terminate_all_passes: (value / 4) % 2 != 0,
                vertical_causal_context: (value / 8) % 2 != 0,
                predictable_termination: (value / 16) % 2 != 0,
                segmentation_symbols: (value / 32) % 2 != 0,
            })
        };
        assert_eq!(Tier1CodingStyle::from_code_block_style(value), expected);
        assert_eq!(tier1_coding_style_from_code_block_style(value), expected);
        assert_eq!(
            Tier1BlockCoding::from_code_block_style(value),
            expected.map(|style| style.block_coding),
        );
    }
    assert_eq!(admitted, 82);
}

fn legacy_raw_pair_decoder(width: u16) -> Tier1CodeBlockDecoder {
    let mut decoder = Tier1CodeBlockDecoder::new(
        width,
        1,
        7,
        SubbandOrientation::Hh,
        Tier1CodingStyle {
            selective_arithmetic_coding_bypass: true,
            ..Tier1CodingStyle::default()
        },
    )
    .unwrap();
    decoder.next_pass = 10;
    decoder.bitplane = 2;
    for x in 0..width {
        decoder
            .plane
            .mark_significant_at_bitplane(x, 0, 3, x % 2 != 0)
            .unwrap();
    }
    let mut mq = MqDecoder::new(&[], &ResourceLimits::default()).unwrap();
    for index in 0..19 {
        mq.set_context(index, (index * 2) as u8, index % 2 == 0)
            .unwrap();
    }
    decoder.mq_context_state = Some(mq.context_state());
    decoder.zero_bitplanes = Some(u16::MAX);
    decoder.ht_refinement_data = vec![0xff, 0x90, 0x27];
    decoder.ht_refinement_passes = u8::MAX;
    decoder.ht_decoded_bitplanes = u16::MAX;
    decoder.ht_current_set_has_cleanup = true;
    decoder.ht_sets_seen = u16::MAX;
    decoder.allow_multiple_ht_sets = true;
    decoder.ht_magnitude_bound = u8::MAX;
    decoder
}

fn expected_legacy_raw_pair(decoder: &Tier1CodeBlockDecoder, reset: bool) -> Tier1CodeBlockDecoder {
    let mut expected = decoder.clone();
    expected.plane.coefficients[0].magnitude = 12;
    expected.plane.coefficients[0].legacy_bitplane = Some(2);
    expected.plane.coefficients[0].refined = true;
    let mut state = legacy_bitplane_from_plane(&decoder.plane, 2).unwrap();
    state.significance_propagation_complete = true;
    state.magnitude_refinement_complete = true;
    expected.bitplane_state = Some(state);
    expected.next_pass = 12;
    expected.decoded_segments = 1;
    expected.decoded_bytes = 1;
    expected.reset_contexts_before_mq = reset;
    expected
}

#[test]
fn legacy_contribution_work_phase_matches_wide_native_extrema_and_error_priority() {
    let words = [0, 1, 255, 65_535, u64::MAX - 1, u64::MAX];
    for samples in [0, 1, 2, 3, usize::MAX] {
        for replay in [0, 1, 2, 3, u32::MAX] {
            for bytes in words {
                for previous in words {
                    for maximum in words {
                        let wide = samples as u128 * u128::from(replay)
                            + u128::from(bytes)
                            + u128::from(previous);
                        let expected = if wide > u128::from(u64::MAX) {
                            Err(DecodeError::MalformedInput {
                                offset: 0,
                                kind: MalformedKind::ArithmeticOverflow,
                            })
                        } else if wide > u128::from(maximum) {
                            Err(DecodeError::LimitExceeded {
                                resource: Resource::WorkUnits,
                                limit: maximum,
                                actual: wide as u64,
                            })
                        } else {
                            Ok(wide as u64)
                        };
                        assert_eq!(
                            legacy_contribution_work(samples, replay, bytes, previous, maximum),
                            expected
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn legacy_segment_pair_has_independent_complete_state_and_predictable_error_effects() {
    for reset in [false, true] {
        for predictable in [false, true] {
            for input in [0x80, 0xaa] {
                let mut decoder = legacy_raw_pair_decoder(1);
                decoder.style.reset_contexts = reset;
                decoder.style.predictable_termination = predictable;
                let before = decoder.clone();
                let result = decoder.decode_legacy_segment(&[input], 2, &ResourceLimits::default());
                let mut expected = expected_legacy_raw_pair(&before, reset);
                if predictable && input == 0x80 {
                    expected.decoded_segments = 0;
                    expected.decoded_bytes = 0;
                    assert_eq!(result, Err(invalid_code_block()));
                } else {
                    assert_eq!(
                        result,
                        Ok(Tier1SegmentDecode {
                            passes: 2,
                            bytes: 1,
                            statistics: Tier1PassStatistics {
                                coefficients_scanned: 2,
                                coding_symbols: 1,
                                refined_coefficients: 1,
                                ..Tier1PassStatistics::default()
                            },
                        })
                    );
                }
                assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
            }
        }
    }
}

#[test]
fn legacy_segment_low_work_failure_keeps_only_the_real_pass_and_coefficient_prefix() {
    let mut decoder = legacy_raw_pair_decoder(2);
    let before = decoder.clone();
    let limits = ResourceLimits::default()
        .with_maximum_work_units(1)
        .unwrap();
    assert_eq!(
        decoder.decode_legacy_segment(&[0xaa], 2, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2,
        })
    );
    let mut expected = before.clone();
    expected.plane.coefficients[0].magnitude = 12;
    expected.plane.coefficients[0].legacy_bitplane = Some(2);
    expected.plane.coefficients[0].refined = true;
    let mut state = legacy_bitplane_from_plane(&before.plane, 2).unwrap();
    state.significance_propagation_complete = true;
    expected.bitplane_state = Some(state);
    expected.next_pass = 11;
    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
}

#[test]
fn actual_legacy_contribution_replays_retained_bytes_and_accounts_extra_work_exactly() {
    for reset in [false, true] {
        let mut decoder = legacy_raw_pair_decoder(1);
        decoder.style.reset_contexts = reset;
        let before = decoder.clone();
        decoder
            .decode_legacy_contribution(&[0xaa], 1, &ResourceLimits::default())
            .unwrap();
        let mut expected_prefix = before.clone();
        expected_prefix.next_pass = 11;
        expected_prefix.decoded_segments = 1;
        expected_prefix.decoded_bytes = 1;
        expected_prefix.legacy_decode_work = 2;
        expected_prefix.reset_contexts_before_mq = reset;
        let mut state = legacy_bitplane_from_plane(&before.plane, 2).unwrap();
        state.significance_propagation_complete = true;
        expected_prefix.bitplane_state = Some(state);
        let mut retained = before.legacy_segment_snapshot().unwrap();
        retained.input = vec![0xaa];
        retained.passes = 1;
        expected_prefix.legacy_segment = Some(retained);
        assert_eq!(format!("{decoder:?}"), format!("{expected_prefix:?}"));
        decoder
            .decode_legacy_contribution(&[], 1, &ResourceLimits::default())
            .unwrap();
        let mut expected = expected_legacy_raw_pair(&before, reset);
        expected.legacy_decode_work = 5;
        assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));

        let mut whole = before;
        whole
            .decode_legacy_contribution(&[0xaa], 2, &ResourceLimits::default())
            .unwrap();
        expected.legacy_decode_work = 3;
        assert_eq!(format!("{whole:?}"), format!("{expected:?}"));
    }
}

#[test]
fn retained_contribution_late_input_limit_failure_consumes_snapshot_but_not_payload_state() {
    let mut decoder = legacy_raw_pair_decoder(1);
    let before = decoder.clone();
    decoder
        .decode_legacy_contribution(&[0xaa], 1, &ResourceLimits::default())
        .unwrap();
    let limits = ResourceLimits::default()
        .with_maximum_input_bytes(1)
        .unwrap();
    assert_eq!(
        decoder.decode_legacy_contribution(&[0], 1, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: 1,
            actual: 2,
        })
    );
    let mut expected = before;
    expected.legacy_decode_work = 6;
    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
}

#[test]
fn contribution_and_segment_first_errors_and_late_accounting_preserve_every_other_field() {
    let mut decoder = legacy_raw_pair_decoder(1);
    decoder.next_pass = u32::MAX;
    let mut expected = decoder.clone();
    expected.legacy_decode_work = 2;
    assert_eq!(
        decoder.decode_legacy_contribution(&[0], 1, &ResourceLimits::default()),
        Err(arithmetic_overflow())
    );
    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));

    let mut decoder = legacy_raw_pair_decoder(1);
    let before = format!("{decoder:?}");
    let limits = ResourceLimits::default()
        .with_maximum_code_block_passes(11)
        .unwrap();
    assert_eq!(
        decoder.decode_legacy_segment(&[0], 2, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlockPasses,
            limit: 11,
            actual: 12,
        })
    );
    assert_eq!(format!("{decoder:?}"), before);

    let mut decoder = legacy_raw_pair_decoder(1);
    let mut expected = decoder.clone();
    if let Ok(bytes) = usize::try_from(u64::from(u32::MAX) + 1) {
        expected.decoded_segments = 1;
        expected.decoded_bytes = bytes as u64;
        assert_eq!(
            decoder.commit_legacy_segment(bytes, 2, Tier1PassStatistics::default()),
            Err(arithmetic_overflow())
        );
        assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
    }
}

#[test]
fn actual_mq_cleanup_contribution_completes_a_block_with_exact_probability_contexts() {
    let mut decoder =
        Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, Tier1CodingStyle::default())
            .unwrap();
    let mut expected = decoder.clone();
    let limits = ResourceLimits::default()
        .with_maximum_work_units(2)
        .unwrap();
    assert_eq!(
        decoder.decode_legacy_contribution(&[0xff], 1, &limits),
        Ok(())
    );
    let mut contexts = MqDecoder::new(&[], &ResourceLimits::default()).unwrap();
    for index in 0..19 {
        contexts
            .set_context(
                index,
                match index {
                    0 => 5,
                    17 => 3,
                    18 => 46,
                    _ => 0,
                },
                false,
            )
            .unwrap();
    }
    expected.next_pass = 1;
    expected.decoded_segments = 1;
    expected.decoded_bytes = 1;
    expected.legacy_decode_work = 2;
    expected.mq_context_state = Some(contexts.context_state());
    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
    assert!(decoder.is_complete());

    let mut decoder =
        Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, Tier1CodingStyle::default())
            .unwrap();
    let mut expected = decoder.clone();
    let limits = ResourceLimits::default()
        .with_maximum_work_units(1)
        .unwrap();
    expected.bitplane_state = Some(Tier1BitplaneState {
        width: 1,
        height: 1,
        bitplane: 0,
        significant_before: vec![false],
        significance_visited: vec![false],
        significance_propagation_complete: false,
        magnitude_refinement_complete: false,
        cleanup_complete: false,
    });
    assert_eq!(
        decoder.decode_legacy_segment(&[0xff], 1, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2,
        })
    );
    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
}

#[test]
fn legacy_plans_cover_all_style_flags_and_full_native_pass_index_boundaries() {
    for bits in 0..=u8::MAX {
        for block_coding in [
            Tier1BlockCoding::Legacy,
            Tier1BlockCoding::HighThroughput,
            Tier1BlockCoding::Mixed,
        ] {
            let style = Tier1CodingStyle {
                block_coding,
                force_high_throughput: bits & 128 != 0,
                selective_arithmetic_coding_bypass: bits & 1 != 0,
                reset_contexts: bits & 2 != 0,
                terminate_all_passes: bits & 4 != 0,
                vertical_causal_context: bits & 8 != 0,
                predictable_termination: bits & 16 != 0,
                segmentation_symbols: bits & 32 != 0,
            };
            for index in (0..=17).chain([u32::MAX - 2, u32::MAX - 1, u32::MAX]) {
                let phase = index % 3;
                let kind = match phase {
                    0 => Tier1PassKind::Cleanup,
                    1 => Tier1PassKind::SignificancePropagation,
                    _ => Tier1PassKind::MagnitudeRefinement,
                };
                let raw = bits & 1 != 0 && index >= 10 && phase != 0;
                let terminated =
                    bits & 4 != 0 || (bits & 1 != 0 && (index == 9 || (index >= 10 && phase != 1)));
                assert_eq!(pass_kind(index), kind);
                assert_eq!(
                    style.pass_plan(index),
                    Tier1PassPlan {
                        kind,
                        coding_mode: if raw {
                            Tier1CodingMode::Raw
                        } else {
                            Tier1CodingMode::Mq
                        },
                        terminates_segment: terminated,
                        reset_contexts_after_pass: bits & 2 != 0,
                        validate_predictable_termination: bits & 16 != 0 && terminated && !raw,
                        expect_segmentation_symbol: bits & 32 != 0 && phase == 0,
                    }
                );
                let boundary = if bits & 4 != 0 {
                    1
                } else if bits & 1 == 0 {
                    u32::MAX
                } else if index < 10 {
                    10 - index
                } else if phase == 1 {
                    2
                } else {
                    1
                };
                for available in [0, 1, 2, 3, 9, 10, u32::MAX] {
                    assert_eq!(
                        style.segment_passes(index, available),
                        available.min(boundary)
                    );
                }
            }
        }
    }
}

#[test]
fn legacy_zero_bitplanes_preserves_native_range_and_prior_value_error_priority() {
    for bitplane in 0..=u16::MAX {
        assert_eq!(
            legacy_maximum_passes(bitplane),
            Ok(u32::from(bitplane) * 3 + 1)
        );
    }
    for bitplane in [0, 2, 291, 292, u16::MAX] {
        for zero in [0, 1, 2, 291, 292, u16::MAX] {
            for previous in [None, Some(zero), Some(zero ^ 1)] {
                for next_pass in [0, u32::MAX] {
                    for decoded_segments in [0, u32::MAX] {
                        let mut decoder = legacy_raw_pair_decoder(1);
                        decoder.bitplane = bitplane;
                        decoder.zero_bitplanes = previous;
                        decoder.next_pass = next_pass;
                        decoder.decoded_segments = decoded_segments;
                        let mut expected = decoder.clone();
                        let result = if previous == Some(zero) {
                            Ok(())
                        } else if previous.is_some()
                            || next_pass != 0
                            || decoded_segments != 0
                            || zero > bitplane
                        {
                            Err(invalid_code_block())
                        } else {
                            expected.bitplane = bitplane - zero;
                            expected.maximum_passes = u32::from(bitplane - zero) * 3 + 1;
                            expected.zero_bitplanes = Some(zero);
                            Ok(())
                        };
                        assert_eq!(decoder.set_zero_bitplanes(zero), result);
                        assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
                    }
                }
            }
        }
    }
}

#[test]
fn legacy_raw_data_clones_preserve_malformed_shapes_words_and_independent_vectors() {
    let mut mq = MqDecoder::new(&[0xff, 0x90], &ResourceLimits::default()).unwrap();
    for index in 0..19 {
        mq.set_context(index, (index * 2) as u8, index % 2 == 0)
            .unwrap();
    }
    for (width, height) in [(0, 0), (1, 1), (u16::MAX, 0), (u16::MAX, u16::MAX)] {
        for before_len in 0..=4 {
            for visited_len in 0..=4 {
                for flags in 0..8 {
                    let plane = CodeBlockPlane {
                        width,
                        height,
                        coefficients: (0..3)
                            .map(|i| CoefficientState {
                                magnitude: u64::MAX - i,
                                magnitude_high: [i, u64::MAX, 1 << 63, i + 1, 37],
                                legacy_bitplane: Some(u16::MAX),
                                negative: i != 1,
                                significant: i == 1,
                                refined: i == 2,
                            })
                            .collect(),
                    };
                    let bitplane_state = Tier1BitplaneState {
                        width: height,
                        height: width,
                        bitplane: u16::MAX,
                        significant_before: (0..before_len).map(|i| i % 2 == 0).collect(),
                        significance_visited: (0..visited_len).map(|i| i % 2 != 0).collect(),
                        significance_propagation_complete: flags & 1 != 0,
                        magnitude_refinement_complete: flags & 2 != 0,
                        cleanup_complete: flags & 4 != 0,
                    };
                    for retained in [None, Some(bitplane_state.clone())] {
                        let original = LegacySegmentState {
                            plane: plane.clone(),
                            next_pass: u32::MAX,
                            bitplane: u16::MAX,
                            bitplane_state: retained,
                            mq_context_state: Some(mq.context_state()),
                            reset_contexts_before_mq: flags & 1 != 0,
                            decoded_segments: u32::MAX,
                            decoded_bytes: u64::MAX,
                            input: vec![0xff, 0x90, 0, 0xff],
                            passes: u32::MAX,
                        };
                        let before = format!("{original:?}");
                        let mut cloned = original.clone();
                        assert_eq!(format!("{cloned:?}"), before);
                        cloned.input[0] = 0;
                        cloned.plane.coefficients[0].magnitude_high[4] = 0;
                        if let Some(state) = &mut cloned.bitplane_state {
                            state.significant_before.push(false);
                            state.significance_visited.push(true);
                            state.bitplane = 0;
                        }
                        assert_eq!(format!("{original:?}"), before);
                        assert_eq!(original.plane, plane);
                        assert_eq!(bitplane_state.clone(), bitplane_state);
                    }
                }
            }
        }
    }
}

#[test]
fn legacy_raw_significance_refinement_and_mq_cleanup_have_exact_whole_results() {
    for width in 1..=4 {
        for height in 1..=9 {
            for orientation in [
                SubbandOrientation::Ll,
                SubbandOrientation::Lh,
                SubbandOrientation::Hl,
                SubbandOrientation::Hh,
            ] {
                for causal in [false, true] {
                    let mut plane = CodeBlockPlane::new(width, height).unwrap();
                    plane.mark_significant(0, 0, 8, false).unwrap();
                    let mut state = legacy_bitplane_from_plane(&plane, 2).unwrap();
                    let style = Tier1CodingStyle {
                        vertical_causal_context: causal,
                        ..Tier1CodingStyle::default()
                    };
                    let mut reader = raw_reader_from_input(&[0xff, 0x90], 2, 1000).unwrap();
                    let count = u32::from(width) * u32::from(height);
                    let significance = decode_raw_significance_propagation_pass(
                        &mut plane,
                        &mut state,
                        &mut reader,
                        orientation,
                        style,
                    )
                    .unwrap();
                    assert_eq!(
                        significance,
                        Tier1PassStatistics {
                            coefficients_scanned: count,
                            coding_symbols: 2 * (count - 1),
                            newly_significant: count - 1,
                            ..Tier1PassStatistics::default()
                        }
                    );
                    assert!(state.significance_propagation_complete);
                    assert!(!state.magnitude_refinement_complete && !state.cleanup_complete);
                    assert_eq!(
                        state.significant_before,
                        (0..count).map(|i| i == 0).collect::<Vec<_>>()
                    );
                    assert_eq!(
                        state.significance_visited,
                        (0..count).map(|i| i != 0).collect::<Vec<_>>()
                    );
                    for (index, coefficient) in plane.coefficients.iter().enumerate() {
                        assert_eq!(
                            *coefficient,
                            CoefficientState {
                                magnitude: if index == 0 { 8 } else { 4 },
                                magnitude_high: [0; 5],
                                legacy_bitplane: if index == 0 { None } else { Some(2) },
                                negative: index != 0,
                                significant: true,
                                refined: false,
                            }
                        );
                    }
                    assert_eq!(
                        decode_raw_magnitude_refinement_pass(
                            &mut plane,
                            &mut state,
                            &mut reader,
                            style
                        ),
                        Ok(Tier1PassStatistics {
                            coefficients_scanned: count,
                            coding_symbols: 1,
                            refined_coefficients: 1,
                            ..Tier1PassStatistics::default()
                        })
                    );
                    assert_eq!(plane.coefficients[0].magnitude, 12);
                    assert!(plane.coefficients[0].refined);
                    assert!(
                        state.significance_propagation_complete
                            && state.magnitude_refinement_complete
                            && !state.cleanup_complete
                    );
                    assert_eq!(reader.work_units, u64::from(2 * (count - 1) + 1));
                    let before = plane.clone();
                    let mut mq = MqDecoder::new(&[], &ResourceLimits::default()).unwrap();
                    let before_mq = format!("{mq:?}");
                    assert_eq!(
                        decode_cleanup_pass_with_style(
                            &mut plane,
                            &mut state,
                            &mut mq,
                            orientation,
                            style
                        ),
                        Ok(Tier1PassStatistics {
                            coefficients_scanned: count,
                            ..Tier1PassStatistics::default()
                        })
                    );
                    assert_eq!(plane, before);
                    assert!(state.cleanup_complete);
                    assert_eq!(format!("{mq:?}"), before_mq);
                }
            }
        }
    }
}

#[test]
fn legacy_significance_budget_errors_preserve_exact_decoded_prefix_and_flags() {
    for maximum in 0..=3 {
        let mut plane = CodeBlockPlane::new(2, 1).unwrap();
        plane.mark_significant(0, 0, 8, false).unwrap();
        let mut state = legacy_bitplane_from_plane(&plane, 2).unwrap();
        let before = plane.clone();
        let mut reader = raw_reader_from_input(&[0xff], 1, maximum).unwrap();
        let result = decode_raw_significance_propagation_pass(
            &mut plane,
            &mut state,
            &mut reader,
            SubbandOrientation::Ll,
            Tier1CodingStyle::default(),
        );
        let mut expected_state = legacy_bitplane_from_plane(&before, 2).unwrap();
        expected_state.significance_visited[1] = maximum >= 1;
        expected_state.significance_propagation_complete = maximum >= 2;
        assert_eq!(state, expected_state);
        assert_eq!(
            reader,
            RawBitReader {
                input: &[0xff],
                next_index: 1,
                current_byte: 0xff,
                bits_remaining: if maximum == 0 { 7 } else { 6 },
                marker_padding_count: 0,
                work_units: if maximum == 0 { 1 } else { 2 },
                maximum_work_units: maximum,
            }
        );
        if maximum < 2 {
            assert_eq!(plane, before);
            assert_eq!(
                result,
                Err(DecodeError::LimitExceeded {
                    resource: Resource::WorkUnits,
                    limit: maximum,
                    actual: maximum + 1,
                })
            );
        } else {
            assert_eq!(
                plane.coefficients[1],
                CoefficientState {
                    magnitude: 4,
                    magnitude_high: [0; 5],
                    legacy_bitplane: Some(2),
                    negative: true,
                    significant: true,
                    refined: false,
                }
            );
            assert_eq!(
                result,
                Ok(Tier1PassStatistics {
                    coefficients_scanned: 2,
                    coding_symbols: 2,
                    newly_significant: 1,
                    ..Tier1PassStatistics::default()
                })
            );
        }
    }
}

#[test]
fn legacy_sign_mark_covers_every_native_bitplane_without_constructor_assumptions() {
    for bitplane in 0..=u16::MAX {
        let mut plane = CodeBlockPlane::new(2, 1).unwrap();
        plane.mark_significant(0, 0, 1, false).unwrap();
        let before = plane.clone();
        let mut state = legacy_bitplane_from_plane(&plane, 0).unwrap();
        state.bitplane = bitplane;
        let mut reader = raw_reader_from_input(&[0xff], 1, 2).unwrap();
        let result = decode_raw_significance_propagation_pass(
            &mut plane,
            &mut state,
            &mut reader,
            SubbandOrientation::Hh,
            Tier1CodingStyle::default(),
        );
        assert_eq!(state.significance_visited, [false, true]);
        assert_eq!(reader.work_units, 2);
        assert_eq!(reader.bits_remaining, 6);
        assert_eq!(state.significant_before, [true, false]);
        assert!(!state.magnitude_refinement_complete && !state.cleanup_complete);
        if bitplane < 384 {
            let mut limbs = [0_u64; 6];
            limbs[usize::from(bitplane / 64)] = 1 << (bitplane % 64);
            assert_eq!(plane.coefficients[0], before.coefficients[0]);
            assert_eq!(plane.coefficients[1].magnitude, limbs[0]);
            assert_eq!(plane.coefficients[1].magnitude_high, limbs[1..]);
            assert_eq!(plane.coefficients[1].legacy_bitplane, Some(bitplane));
            assert!(
                plane.coefficients[1].significant
                    && plane.coefficients[1].negative
                    && !plane.coefficients[1].refined
            );
            assert!(state.significance_propagation_complete);
            assert_eq!(
                result,
                Ok(Tier1PassStatistics {
                    coefficients_scanned: 2,
                    coding_symbols: 2,
                    newly_significant: 1,
                    ..Tier1PassStatistics::default()
                })
            );
        } else {
            assert_eq!(plane, before);
            assert!(!state.significance_propagation_complete);
            assert_eq!(result, Err(arithmetic_overflow()));
        }
    }
}

#[test]
fn legacy_raw_refinement_keeps_high_words_tags_and_exact_failure_priority() {
    for bitplane in [0, 63, 64, 127, 191, 255, 291, 292, 383, 384, u16::MAX] {
        for bit in [false, true] {
            let mut plane = CodeBlockPlane::new(1, 1).unwrap();
            plane.coefficients[0] = CoefficientState {
                magnitude: u64::MAX,
                magnitude_high: [u64::MAX; 5],
                legacy_bitplane: Some(u16::MAX),
                negative: true,
                significant: true,
                refined: false,
            };
            let before = plane.clone();
            let mut state = legacy_bitplane_from_plane(&plane, 0).unwrap();
            state.bitplane = bitplane;
            state.significance_propagation_complete = true;
            let mut reader = raw_reader_from_input(if bit { &[0x80] } else { &[0] }, 1, 1).unwrap();
            let result = decode_raw_magnitude_refinement_pass(
                &mut plane,
                &mut state,
                &mut reader,
                Tier1CodingStyle::default(),
            );
            assert_eq!(reader.work_units, 1);
            assert_eq!(reader.bits_remaining, 7);
            assert_eq!(state.significant_before, [true]);
            assert_eq!(state.significance_visited, [false]);
            assert!(state.significance_propagation_complete && !state.cleanup_complete);
            if bitplane >= 292 || bit {
                assert_eq!(
                    result,
                    Err(if bitplane >= 292 {
                        invalid_code_block()
                    } else {
                        arithmetic_overflow()
                    })
                );
                assert_eq!(plane, before);
                assert!(!state.magnitude_refinement_complete);
            } else {
                assert_eq!(
                    result,
                    Ok(Tier1PassStatistics {
                        coefficients_scanned: 1,
                        coding_symbols: 1,
                        refined_coefficients: 1,
                        ..Tier1PassStatistics::default()
                    })
                );
                let mut expected = before;
                expected.coefficients[0].refined = true;
                expected.coefficients[0].legacy_bitplane = Some(bitplane);
                assert_eq!(plane, expected);
                assert!(state.magnitude_refinement_complete);
            }
        }
    }
}

#[test]
fn legacy_cleanup_run_and_segsym_errors_keep_exact_real_symbol_prefix() {
    for maximum in 0..=11 {
        for valid_segsym in [false, true] {
            let input = [if valid_segsym { 0xa2 } else { 0xa0 }, 0x80];
            let mut plane = CodeBlockPlane::new(1, 4).unwrap();
            let mut state = legacy_bitplane_from_plane(&plane, 2).unwrap();
            let mut reader = raw_reader_from_input(&input, 2, maximum).unwrap();
            let result = decode_cleanup(
                &mut plane,
                &mut state,
                &mut reader,
                SubbandOrientation::Hl,
                true,
                true,
            );
            let work = if maximum < 10 { maximum + 1 } else { 10 };
            assert_eq!(
                reader,
                RawBitReader {
                    input: &input,
                    next_index: if work <= 8 { 1 } else { 2 },
                    current_byte: if work <= 8 { input[0] } else { input[1] },
                    bits_remaining: if work <= 8 {
                        (8 - work) as u8
                    } else {
                        (16 - work) as u8
                    },
                    marker_padding_count: 0,
                    work_units: work,
                    maximum_work_units: maximum,
                }
            );
            let mut expected = CodeBlockPlane::new(1, 4).unwrap();
            if maximum >= 4 {
                expected.coefficients[1] = CoefficientState {
                    magnitude: 4,
                    magnitude_high: [0; 5],
                    legacy_bitplane: Some(2),
                    negative: false,
                    significant: true,
                    refined: false,
                };
            }
            assert_eq!(plane, expected);
            assert_eq!(state.significant_before, [false; 4]);
            assert_eq!(state.significance_visited, [false; 4]);
            assert!(
                !state.significance_propagation_complete && !state.magnitude_refinement_complete
            );
            assert_eq!(state.cleanup_complete, maximum >= 10 && valid_segsym);
            assert_eq!(
                result,
                if maximum < 10 {
                    Err(DecodeError::LimitExceeded {
                        resource: Resource::WorkUnits,
                        limit: maximum,
                        actual: maximum + 1,
                    })
                } else if !valid_segsym {
                    Err(invalid_code_block())
                } else {
                    Ok(Tier1PassStatistics {
                        coefficients_scanned: 4,
                        coding_symbols: 10,
                        newly_significant: 1,
                        run_mode_columns: 1,
                        ..Tier1PassStatistics::default()
                    })
                }
            );
        }
    }
}

fn raw_token_oracle(input: &[u8], rank: usize) -> (bool, usize, u8, u8, u64) {
    assert!(input.len() <= 2);
    let remaining = |position: usize| u8::try_from(7 - position % 8).unwrap();
    let bit = |byte: u8, position: usize| {
        (u16::from(byte) / 2_u16.pow(u32::try_from(position).unwrap())) % 2 == 1
    };
    if input.is_empty() {
        return (
            true,
            0,
            0xff,
            remaining(rank),
            u64::try_from(rank / 8).unwrap(),
        );
    }
    if rank < 8 {
        return (bit(input[0], 7 - rank), 1, input[0], remaining(rank), 0);
    }
    if input.len() == 1 || (input[0] == 0xff && input[1] > 0x8f) {
        let offset = rank - 8;
        return (
            true,
            1,
            0xff,
            remaining(offset),
            u64::try_from(offset / 8).unwrap() + u64::from(input[0] == 0xff),
        );
    }
    let width = if input[0] == 0xff { 7 } else { 8 };
    if rank < 8 + width {
        let shift = width - 1 - (rank - 8);
        return (
            bit(input[1], shift),
            2,
            input[1],
            u8::try_from(shift).unwrap(),
            0,
        );
    }
    let offset = rank - 8 - width;
    (
        true,
        2,
        0xff,
        remaining(offset),
        u64::try_from(offset / 8).unwrap() + u64::from(input[1] == 0xff),
    )
}

fn check_raw_token_trace(input: &[u8]) {
    let limits = ResourceLimits::default();
    let mut reader = RawBitReader::new(input, &limits).unwrap();
    for rank in 0..24 {
        let (bit, next_index, current_byte, bits_remaining, marker_padding_count) =
            raw_token_oracle(input, rank);
        assert_eq!(reader.read_bit(), Ok(bit));
        assert_eq!(
            reader,
            RawBitReader {
                input,
                next_index,
                current_byte,
                bits_remaining,
                marker_padding_count,
                work_units: u64::try_from(rank + 1).unwrap(),
                maximum_work_units: limits.maximum_work_units(),
            },
        );
        assert_eq!(reader.bytes_consumed(), next_index);
        assert_eq!(reader.marker_padding_count(), marker_padding_count);
    }
}

#[test]
fn raw_reader_transitions_match_exhaustive_two_byte_token_oracle() {
    check_raw_token_trace(&[]);
    for first in 0..=u8::MAX {
        check_raw_token_trace(&[first]);
        for second in 0..=u8::MAX {
            check_raw_token_trace(&[first, second]);
        }
    }
}

#[test]
fn raw_reader_limits_preserve_post_bit_counter_and_exact_state() {
    for input in [
        &[][..],
        &[0][..],
        &[0xff][..],
        &[0xff, 0x7f][..],
        &[0xff, 0x8f][..],
        &[0xff, 0x90][..],
        &[0x12, 0xff][..],
    ] {
        for maximum_work_units in 0..=20 {
            let mut reader = raw_reader_from_input(input, u64::MAX, maximum_work_units).unwrap();
            for rank in 0..24 {
                let work_units = u64::try_from(rank + 1).unwrap();
                let (bit, next_index, current_byte, bits_remaining, marker_padding_count) =
                    raw_token_oracle(input, rank);
                let expected = if work_units <= maximum_work_units {
                    Ok(bit)
                } else {
                    Err(DecodeError::LimitExceeded {
                        resource: Resource::WorkUnits,
                        limit: maximum_work_units,
                        actual: work_units,
                    })
                };
                assert_eq!(reader.read_bit(), expected);
                assert_eq!(
                    reader,
                    RawBitReader {
                        input,
                        next_index,
                        current_byte,
                        bits_remaining,
                        marker_padding_count,
                        work_units,
                        maximum_work_units,
                    },
                );
            }
        }
    }
}

#[test]
fn raw_reader_overflow_and_invalid_state_errors_preserve_complete_state() {
    let mut work = raw_reader_from_input(&[0xa5], u64::MAX, u64::MAX).unwrap();
    work.work_units = u64::MAX;
    let mut expected = work;
    expected.next_index = 1;
    expected.current_byte = 0xa5;
    expected.bits_remaining = 7;
    assert_eq!(
        work.read_bit(),
        Err(DecodeError::MalformedInput {
            offset: 1,
            kind: MalformedKind::ArithmeticOverflow,
        }),
    );
    assert_eq!(work, expected);

    let mut padding = raw_reader_from_input(&[0xff, 0x90], u64::MAX, 5).unwrap();
    padding.next_index = 1;
    padding.current_byte = 0xff;
    padding.marker_padding_count = u64::MAX;
    padding.work_units = 5;
    let mut expected = padding;
    expected.bits_remaining = 8;
    assert_eq!(
        padding.read_bit(),
        Err(DecodeError::MalformedInput {
            offset: 1,
            kind: MalformedKind::ArithmeticOverflow,
        }),
    );
    assert_eq!(padding, expected);
    expected.bits_remaining = 7;
    expected.work_units = 6;
    assert_eq!(
        padding.read_bit(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 5,
            actual: 6,
        }),
    );
    assert_eq!(padding, expected);

    for bits_remaining in [9, u8::MAX] {
        let mut invalid = raw_reader_from_input(&[], u64::MAX, u64::MAX).unwrap();
        invalid.bits_remaining = bits_remaining;
        let expected = invalid;
        assert_eq!(
            invalid.read_bit(),
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidBitStuffing,
            }),
        );
        assert_eq!(invalid, expected);
    }
    let mut past = raw_reader_from_input(&[], u64::MAX, 1).unwrap();
    past.next_index = usize::MAX;
    let mut expected = past;
    expected.current_byte = 0xff;
    expected.bits_remaining = 7;
    expected.work_units = 1;
    assert_eq!(past.read_bit(), Ok(true));
    assert_eq!(past, expected);
}

#[test]
fn raw_reader_initial_input_limits_match_exact_claims() {
    let bytes = [1, 2];
    for length in 0..=2 {
        for limit in 0..=2 {
            let input = &bytes[..length];
            let result = raw_reader_from_input(input, limit, 17);
            if u64::try_from(length).unwrap() > limit {
                assert_eq!(
                    result,
                    Err(DecodeError::LimitExceeded {
                        resource: Resource::InputBytes,
                        limit,
                        actual: u64::try_from(length).unwrap(),
                    }),
                );
            } else {
                assert_eq!(
                    result,
                    Ok(RawBitReader {
                        input,
                        next_index: 0,
                        current_byte: 0,
                        bits_remaining: 0,
                        marker_padding_count: 0,
                        work_units: 0,
                        maximum_work_units: 17,
                    }),
                );
            }
        }
    }
}

#[test]
fn raw_reader_termination_matches_independent_alternating_suffix_arithmetic() {
    let limits = ResourceLimits::default();
    let invalid = Err(DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    });
    for byte in 0..=u8::MAX {
        let input = [byte];
        let mut reader = RawBitReader::new(&input, &limits).unwrap();
        assert_eq!(
            reader.validate_predictable_termination(),
            if byte == 0x55 { Ok(()) } else { invalid },
        );
        for consumed in 1..=8 {
            reader.read_bit().unwrap();
            let tail_modulus = 2_u16.pow(8 - consumed);
            let valid = u16::from(byte) % tail_modulus == (tail_modulus - 1) / 3;
            assert_eq!(
                reader.validate_predictable_termination(),
                if valid { Ok(()) } else { invalid },
            );
        }
    }
    let mut empty = RawBitReader::new(&[], &limits).unwrap();
    assert_eq!(empty.validate_predictable_termination(), Ok(()));
    empty.read_bit().unwrap();
    assert_eq!(empty.validate_predictable_termination(), invalid);
    let mut unread = RawBitReader::new(&[0x55, 0x55], &limits).unwrap();
    unread.read_bit().unwrap();
    assert_eq!(unread.validate_predictable_termination(), invalid);
    let mut marker = RawBitReader::new(&[0xff, 0x90], &limits).unwrap();
    for _ in 0..24 {
        marker.read_bit().unwrap();
        assert_eq!(marker.validate_predictable_termination(), invalid);
    }
}

#[test]
fn later_empty_terminated_mq_pass_preserves_real_pass_accounting() {
    let style = Tier1CodingStyle::from_code_block_style(0x14).unwrap();
    let limits = ResourceLimits::default();
    let mut decoder = Tier1CodeBlockDecoder::new(1, 1, 2, SubbandOrientation::Ll, style).unwrap();
    decoder.next_pass = 1;
    decoder.bitplane = 0;
    let plane = decoder.plane.clone();
    let result = decoder.decode_segment(&[], 1, &limits).unwrap();
    assert_eq!(result.passes, 1);
    assert_eq!(result.bytes, 0);
    assert_eq!(result.statistics.coding_symbols, 0);
    assert_eq!(result.statistics.coefficients_scanned, 1);
    assert_eq!(decoder.next_pass, 2);
    assert_eq!(decoder.decoded_segments, 1);
    assert_eq!(decoder.decoded_bytes, 0);
    assert_eq!(decoder.plane, plane);
    assert!(decoder.mq_context_state.is_some());
    assert!(
        decoder
            .bitplane_state
            .as_ref()
            .unwrap()
            .significance_propagation_complete()
    );
}

#[test]
fn empty_initial_and_unterminated_legacy_segments_remain_invalid() {
    let limits = ResourceLimits::default();
    let invalid = Err(DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    });
    for style in [
        Tier1CodingStyle::default(),
        Tier1CodingStyle::from_code_block_style(0x14).unwrap(),
    ] {
        let mut initial =
            Tier1CodeBlockDecoder::new(1, 1, 2, SubbandOrientation::Ll, style).unwrap();
        assert_eq!(initial.decode_segment(&[], 1, &limits), invalid);
        assert_eq!(initial.next_pass, 0);
        assert_eq!(initial.decoded_segments, 0);
        assert_eq!(initial.decoded_bytes, 0);
    }
    let mut unfinished =
        Tier1CodeBlockDecoder::new(1, 1, 2, SubbandOrientation::Ll, Tier1CodingStyle::default())
            .unwrap();
    unfinished.next_pass = 1;
    unfinished.bitplane = 0;
    assert_eq!(unfinished.decode_segment(&[], 1, &limits), invalid);
    assert_eq!(unfinished.next_pass, 1);
    assert_eq!(unfinished.decoded_segments, 0);
    assert_eq!(unfinished.decoded_bytes, 0);
}

#[test]
fn empty_raw_predictable_termination_requires_no_consumed_symbols() {
    let limits = ResourceLimits::default();
    let mut reader = RawBitReader::new(&[], &limits).unwrap();
    assert_eq!(reader.validate_predictable_termination(), Ok(()));
    reader.read_bit().unwrap();
    assert_eq!(
        reader.validate_predictable_termination(),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock,
        }),
    );
    assert_eq!(reader.bytes_consumed(), 0);
    assert_eq!(reader.work_units, 1);
}

#[test]
fn raw_predictable_termination_checks_the_exact_stuffed_ff_tail() {
    let limits = ResourceLimits::default();
    let invalid = Err(DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    });
    for first in 0..=u8::MAX {
        for tail in 0..=u8::MAX {
            let input = [first, tail];
            let mut reader = RawBitReader::new(&input, &limits).unwrap();
            for _ in 0..8 {
                reader.read_bit().unwrap();
            }
            assert_eq!(
                reader.validate_predictable_termination(),
                if first == 0xff && tail == 0x2a {
                    Ok(())
                } else {
                    invalid
                },
            );
            assert_eq!(reader.bytes_consumed(), 1);
            assert_eq!(reader.work_units, 8);
        }
    }
    let mut partial = RawBitReader::new(&[0xff, 0x2a], &limits).unwrap();
    for _ in 0..7 {
        partial.read_bit().unwrap();
        assert_eq!(partial.validate_predictable_termination(), invalid);
    }
}

#[test]
fn ht_cleanup_u_bound_includes_packet_msbs_and_placeholders() {
    assert_eq!(crate::refinement::part15_cleanup_u_bound(0, 0, 74), 2);
    assert_eq!(crate::refinement::part15_cleanup_u_bound(6, 0, 8), 8);
    assert_eq!(crate::refinement::part15_cleanup_u_bound(6, 1, 74), 9);
    assert_eq!(crate::refinement::part15_cleanup_u_bound(6, 1, 8), 9);
    assert_eq!(crate::refinement::part15_cleanup_u_bound(30, 0, 31), 32);
    assert_eq!(
        crate::refinement::part15_cleanup_u_bound(u16::MAX, u16::MAX, 74),
        75
    );
}

#[test]
fn leading_zero_bitplanes_are_configured_once_before_coding() {
    let mut decoder =
        Tier1CodeBlockDecoder::new(1, 1, 5, SubbandOrientation::Ll, Tier1CodingStyle::default())
            .unwrap();
    assert!(decoder.set_zero_bitplanes(5).is_err());
    assert_eq!(decoder.maximum_passes(), 13);
    decoder.set_zero_bitplanes(2).unwrap();
    assert_eq!(decoder.bitplane, 2);
    assert_eq!(decoder.maximum_passes(), 7);
    decoder.set_zero_bitplanes(2).unwrap();
    assert!(decoder.set_zero_bitplanes(1).is_err());
    assert_eq!(decoder.bitplane, 2);
    assert_eq!(decoder.maximum_passes(), 7);
}

#[test]
fn raw_reader_applies_seven_bit_stuffing_after_ff() {
    let mut reader = RawBitReader::new(&[0xff, 0x7f], &ResourceLimits::default()).unwrap();
    for _ in 0..8 {
        assert!(reader.read_bit().unwrap());
    }
    let mut second_byte = Vec::new();
    for _ in 0..7 {
        second_byte.push(reader.read_bit().unwrap());
    }
    assert_eq!(second_byte, [true; 7]);
    assert_eq!(reader.bytes_consumed(), 2);
}

#[test]
fn raw_reader_stops_at_marker_without_reading_past_input() {
    let mut reader = RawBitReader::new(&[0xff, 0x90], &ResourceLimits::default()).unwrap();
    for _ in 0..16 {
        assert!(reader.read_bit().unwrap());
    }
    assert_eq!(reader.bytes_consumed(), 1);
    assert!(reader.marker_padding_count() > 0);
}

#[test]
fn validates_raw_predictable_termination_fill() {
    let limits = ResourceLimits::default();
    let mut valid = RawBitReader::new(&[0xaa], &limits).unwrap();
    assert!(valid.read_bit().unwrap());
    valid.validate_predictable_termination().unwrap();

    let mut invalid = RawBitReader::new(&[0xab], &limits).unwrap();
    assert!(invalid.read_bit().unwrap());
    assert!(invalid.validate_predictable_termination().is_err());
}

#[test]
fn tier_one_pass_schedule_repeats_normative_cycle() {
    assert_eq!(pass_kind(0), Tier1PassKind::Cleanup);
    assert_eq!(pass_kind(1), Tier1PassKind::SignificancePropagation);
    assert_eq!(pass_kind(2), Tier1PassKind::MagnitudeRefinement);
    assert_eq!(pass_kind(3), Tier1PassKind::Cleanup);
    assert_eq!(pass_kind(4), Tier1PassKind::SignificancePropagation);
}

#[test]
fn validates_code_block_style_and_raw_bypass_schedule() {
    let style = Tier1CodingStyle::from_code_block_style(0x3f).unwrap();
    assert!(style.selective_arithmetic_coding_bypass);
    assert!(style.reset_contexts);
    assert!(style.terminate_all_passes);
    assert!(style.vertical_causal_context);
    assert!(style.predictable_termination);
    assert!(style.segmentation_symbols);
    assert!(!style.uses_raw_bypass(9));
    assert!(style.uses_raw_bypass(10));
    assert!(style.uses_raw_bypass(11));
    assert!(!style.uses_raw_bypass(12));
    let ht = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    assert_eq!(ht.block_coding, Tier1BlockCoding::HighThroughput);
    let mut ht_decoder = Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, ht).unwrap();
    let decoded = ht_decoder
        .decode_high_throughput_segments(
            &[0x00, 0x63, 0x00],
            1,
            None,
            0,
            &ResourceLimits::default(),
        )
        .unwrap();
    assert_eq!(decoded.passes, 1);
    assert_eq!(decoded.statistics.newly_significant, 1);
    assert_eq!(ht_decoder.next_pass(), 1);
    assert_eq!(ht_decoder.plane().signed_coefficient(0, 0).unwrap(), -1);
    let mixed = Tier1CodingStyle::from_code_block_style(0xc0).unwrap();
    assert_eq!(mixed.block_coding, Tier1BlockCoding::Mixed);
    assert!(mixed.block_coding.selects_high_throughput(3));
    assert!(!mixed.block_coding.selects_high_throughput(4));
    assert!(Tier1CodingStyle::from_code_block_style(0x80).is_err());
    assert!(Tier1CodingStyle::from_code_block_style(0x41).is_err());

    let cleanup = style.pass_plan(12);
    assert_eq!(cleanup.kind, Tier1PassKind::Cleanup);
    assert_eq!(cleanup.coding_mode, Tier1CodingMode::Mq);
    assert!(cleanup.terminates_segment);
    assert!(cleanup.reset_contexts_after_pass);
    assert!(cleanup.validate_predictable_termination);
    assert!(cleanup.expect_segmentation_symbol);

    let bypass = Tier1CodingStyle::from_code_block_style(0x01).unwrap();
    assert_eq!(bypass.segment_passes(0, 20), 10);
    assert_eq!(bypass.segment_passes(8, 20), 2);
    assert_eq!(bypass.segment_passes(10, 20), 2);
    assert_eq!(bypass.segment_passes(11, 20), 1);
    assert_eq!(bypass.segment_passes(12, 20), 1);
    assert_eq!(bypass.segment_passes(12, 0), 0);

    let default_style = Tier1CodingStyle::default();
    assert_eq!(default_style.segment_passes(0, 20), 20);
    assert!(!default_style.pass_plan(0).terminates_segment);
}

#[test]
fn groups_ht_packet_passes_and_retains_bounded_stream_views() {
    assert_eq!(
        HtPassGroup::from_packet_passes(1).unwrap(),
        HtPassGroup {
            cleanup_passes: 1,
            refinement_passes: 0,
            placeholder_passes: 0,
            skipped_bitplanes: 0,
        }
    );
    assert_eq!(
        HtPassGroup::from_packet_passes(3).unwrap(),
        HtPassGroup {
            cleanup_passes: 1,
            refinement_passes: 2,
            placeholder_passes: 0,
            skipped_bitplanes: 0,
        }
    );
    assert!(HtPassGroup::from_packet_passes(0).is_err());
    assert!(HtPassGroup::from_packet_passes(165).is_err());
    assert_eq!(
        HtPassGroup::from_packet_passes(4).unwrap(),
        HtPassGroup {
            cleanup_passes: 4,
            refinement_passes: 0,
            placeholder_passes: 3,
            skipped_bitplanes: 1,
        }
    );

    let cleanup = [0xaa, 0xbb, 0x03, 0x00];
    let refinement = [0x11, 0x22];
    let segments =
        parse_ht_block_segments(&cleanup, Some(&refinement), &ResourceLimits::default()).unwrap();
    assert_eq!(segments.bytes(), 6);
    assert_eq!(segments.cleanup().scup(), 3);
    assert_eq!(segments.cleanup().mag_sgn().bytes(), &[0xaa]);
    assert_eq!(segments.cleanup().mel_vlc().bytes(), &[0xbb, 0x03, 0x00]);
    assert_eq!(segments.cleanup().mel().bytes(), &[0xbb, 0x03]);
    assert_eq!(
        segments.cleanup().vlc().direction(),
        HtStreamDirection::Reverse
    );
    let retained = segments.refinement().unwrap();
    assert_eq!(retained.encoded(), &refinement);
    assert_eq!(
        retained.significance_propagation().direction(),
        HtStreamDirection::Forward
    );
    assert_eq!(
        retained.magnitude_refinement().direction(),
        HtStreamDirection::Reverse
    );
    assert_eq!(retained.significance_propagation().offset(), 4);
}

#[test]
fn raw_plane_getters_preserve_malformed_shapes_and_exact_index_errors() {
    let coefficient = CoefficientState {
        magnitude: 17,
        magnitude_high: [2, 3, 4, 5, 6],
        legacy_bitplane: Some(65535),
        negative: true,
        significant: false,
        refined: true,
    };
    let plane = CodeBlockPlane {
        width: 2,
        height: 2,
        coefficients: vec![coefficient],
    };
    assert_eq!(
        (plane.width(), plane.height(), plane.coefficients()),
        (2, 2, &[coefficient][..])
    );
    assert_eq!(plane.coefficient(0, 0), Ok(coefficient));
    for (x, y) in [(1, 0), (0, 1), (2, 0), (0, 2), (65535, 65535)] {
        assert_eq!(
            plane.coefficient(x, y),
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodeBlock,
            })
        );
    }
    let trailing = CodeBlockPlane {
        width: 1,
        height: 1,
        coefficients: vec![coefficient, CoefficientState::default()],
    };
    assert_eq!(trailing.coefficients().len(), 2);
    assert_eq!(trailing.coefficient(0, 0), Ok(coefficient));
    assert_eq!(trailing.coefficient(0, 1), Err(invalid_code_block()));
    let zero_shape = CodeBlockPlane {
        width: 0,
        height: 0,
        coefficients: vec![coefficient],
    };
    assert_eq!(
        (
            zero_shape.width(),
            zero_shape.height(),
            zero_shape.coefficients().len()
        ),
        (0, 0, 1)
    );
    assert_eq!(zero_shape.coefficient(0, 0), Err(invalid_code_block()));
    let mut decoder =
        Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, Tier1CodingStyle::default())
            .unwrap();
    decoder.plane = plane;
    assert_eq!(
        (
            decoder.plane().width(),
            decoder.plane().height(),
            decoder.plane().coefficients()
        ),
        (2, 2, &[coefficient][..])
    );
}

#[test]
fn raw_signed_coefficients_keep_full_words_flags_and_native_midpoint_errors() {
    let mut coefficient = CoefficientState {
        magnitude: 17,
        magnitude_high: [2, 3, 4, 5, 6],
        legacy_bitplane: Some(65535),
        negative: true,
        significant: false,
        refined: true,
    };
    let wide = coefficient.wide_magnitude();
    for (index, expected) in [17, 2, 3, 4, 5, 6].into_iter().enumerate() {
        assert_eq!(wide.limb(index), Some(expected));
    }
    let absent = coefficient.signed_magnitude().unwrap();
    assert_eq!(absent.magnitude, Magnitude::ZERO);
    assert!(!absent.negative);
    coefficient = CoefficientState {
        magnitude: 0,
        magnitude_high: [0; 5],
        legacy_bitplane: None,
        negative: true,
        significant: true,
        refined: false,
    };
    let negative_zero = coefficient.signed_magnitude().unwrap();
    assert_eq!(negative_zero.magnitude, Magnitude::ZERO);
    assert!(negative_zero.negative);
    coefficient.magnitude = u64::MAX;
    coefficient.legacy_bitplane = Some(1);
    let carry = coefficient.signed_magnitude().unwrap();
    assert_eq!(carry.magnitude.limb(0), Some(0));
    assert_eq!(carry.magnitude.limb(1), Some(1));
    assert!(carry.negative);
    coefficient.magnitude = 0;
    coefficient.legacy_bitplane = Some(384);
    let high = coefficient.signed_magnitude().unwrap();
    for (index, expected) in [0, 0, 0, 0, 0, 1_u64 << 63].into_iter().enumerate() {
        assert_eq!(high.magnitude.limb(index), Some(expected));
    }
    for bitplane in [385, 65535] {
        coefficient.legacy_bitplane = Some(bitplane);
        assert_eq!(
            coefficient.signed_magnitude(),
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::ArithmeticOverflow,
            })
        );
    }
    coefficient.magnitude = u64::MAX;
    coefficient.magnitude_high = [u64::MAX; 5];
    coefficient.legacy_bitplane = Some(0);
    assert_eq!(
        coefficient.signed_magnitude().unwrap().magnitude,
        Magnitude::from_limbs([u64::MAX; 6])
    );
    coefficient.legacy_bitplane = Some(1);
    assert_eq!(
        coefficient.signed_magnitude(),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        })
    );
}

fn refinement_segment(bytes: &[u8]) -> HtRefinementSegment<'_> {
    HtRefinementSegment {
        encoded: bytes,
        significance_propagation: HtSubstreamView {
            bytes,
            offset: 0,
            direction: HtStreamDirection::Forward,
        },
        magnitude_refinement: HtSubstreamView {
            bytes,
            offset: 0,
            direction: HtStreamDirection::Reverse,
        },
    }
}

fn refinement_core<'a>(
    plane: CodeBlockPlane,
    bytes: &'a [u8],
    reverse: bool,
) -> HtRefinementPlaneState<'a> {
    let mask = plane.coefficients.iter().map(|c| c.significant).collect();
    HtRefinementPlaneState {
        output: plane,
        readers: ht_refinement_readers_from_inputs(bytes, bytes, bytes.len(), reverse, 1000)
            .unwrap(),
        cleanup_significant: mask,
        statistics: Tier1PassStatistics::default(),
    }
}

fn raw_refinement_coefficient(
    low: u64,
    high: [u64; 5],
    significant: bool,
    negative: bool,
    refined: bool,
) -> CoefficientState {
    CoefficientState {
        magnitude: low,
        magnitude_high: high,
        legacy_bitplane: Some(u16::MAX),
        significant,
        negative,
        refined,
    }
}

#[test]
fn ht_refinement_snapshot_preserves_original_collection_capacity_and_raw_order() {
    for length in [0, 1, 2, 3, 7, 8, 16, 4096] {
        let input: Vec<_> = (0..length)
            .map(|i| CoefficientState {
                significant: i % 3 == 1,
                negative: i % 2 == 0,
                refined: true,
                ..CoefficientState::default()
            })
            .collect();
        let original: Vec<bool> = input.iter().map(|c| c.significant).collect();
        let actual = ht_collect_cleanup_significance(&input).unwrap();
        // The private fallible producer uses the qualified fresh-reserve profile.
        let reserved = crate::allocation::empty_with_capacity::<bool>(length).unwrap();
        assert_eq!(actual.capacity(), reserved.capacity());
        assert_eq!(actual, original);
        assert_eq!(actual, (0..length).map(|i| i % 3 == 1).collect::<Vec<_>>());
    }
}

#[test]
fn ht_full_refinement_both_passes_preserve_raw_flags_and_all_six_words() {
    let limits = ResourceLimits::default();
    let first = raw_refinement_coefficient(3, [0; 5], true, true, false);
    let stale = raw_refinement_coefficient(17, [2, 3, 5, 7, 11], false, true, true);
    let cleanup = CodeBlockPlane {
        width: 2,
        height: 1,
        coefficients: vec![first, stale],
    };
    for (bytes, passes, scanned, symbols, refined) in
        [(&[1][..], 1, 2, 2, 0), (&[1, 1][..], 2, 4, 3, 1)]
    {
        let (output, statistics) = decode_ht_refinement_plane(
            &cleanup,
            refinement_segment(bytes),
            passes,
            2,
            false,
            &limits,
        )
        .unwrap();
        let mut expected_first = first;
        expected_first.refined = passes == 2;
        assert_eq!(
            output.coefficients(),
            &[
                expected_first,
                CoefficientState {
                    magnitude: 1,
                    magnitude_high: [0; 5],
                    legacy_bitplane: None,
                    significant: true,
                    negative: false,
                    refined: false,
                }
            ]
        );
        assert_eq!(
            statistics,
            Tier1PassStatistics {
                coefficients_scanned: scanned,
                coding_symbols: symbols,
                newly_significant: 1,
                refined_coefficients: refined,
                run_mode_columns: 0,
            }
        );
    }
    assert_eq!(cleanup.coefficients(), &[first, stale]);
    let (lower, _) =
        decode_ht_refinement_plane(&cleanup, refinement_segment(&[]), 2, 2, false, &limits)
            .unwrap();
    assert_eq!(
        lower.coefficients()[0],
        CoefficientState {
            magnitude: 2,
            refined: true,
            ..first
        }
    );
    assert_eq!(lower.coefficients()[1], stale);
}

#[test]
fn ht_full_refinement_uses_wide_native_borrow_addition_and_no_midpoint_normalization() {
    let limits = ResourceLimits::default();
    for (base, bytes, planes, expected) in [
        ([0, 1, 0, 0, 0, 0], &[][..], 3, [u64::MAX, 0, 0, 0, 0, 0]),
        ([0, 1, 0, 0, 0, 0], &[1][..], 3, [1, 1, 0, 0, 0, 0]),
        (
            [0, 0, 0, 0, 0, 1],
            &[][..],
            292,
            [0, 0, 0, 0, u64::MAX - (1_u64 << 33) + 1, 0],
        ),
    ] {
        let coefficient = raw_refinement_coefficient(
            base[0],
            [base[1], base[2], base[3], base[4], base[5]],
            true,
            true,
            false,
        );
        let cleanup = CodeBlockPlane {
            width: 1,
            height: 1,
            coefficients: vec![coefficient],
        };
        let (output, statistics) = decode_ht_refinement_plane(
            &cleanup,
            refinement_segment(bytes),
            2,
            planes,
            false,
            &limits,
        )
        .unwrap();
        assert_eq!(
            output.coefficients()[0],
            raw_refinement_coefficient(
                expected[0],
                [
                    expected[1],
                    expected[2],
                    expected[3],
                    expected[4],
                    expected[5]
                ],
                true,
                true,
                true
            )
        );
        assert_eq!(
            (
                statistics.coefficients_scanned,
                statistics.coding_symbols,
                statistics.refined_coefficients
            ),
            (2, 1, 1)
        );
        assert_eq!(cleanup.coefficients()[0], coefficient);
    }
}

#[test]
fn ht_full_refinement_delays_patch_signs_and_keeps_discovery_distinct() {
    let mut cleanup = CodeBlockPlane::new(3, 1).unwrap();
    cleanup.coefficients[0] = raw_refinement_coefficient(3, [0; 5], true, false, false);
    let mut patch = HtSignificancePatchState {
        core: refinement_core(cleanup.clone(), &[0x0b], false),
        discovery: cleanup,
        pending: Vec::new(),
    };
    patch
        .discover_patch(0, 3, 0, 1, Magnitude::from_u64(1), false)
        .unwrap();
    assert_eq!(patch.pending, [(1, 0), (2, 0)]);
    assert!(
        !patch.core.output.coefficients()[1].significant
            && !patch.core.output.coefficients()[2].significant
    );
    assert!(
        patch.discovery.coefficients()[1].significant
            && patch.discovery.coefficients()[2].significant
    );
    assert_eq!(
        (
            patch.core.readers.forward.physical_bits_read,
            patch.core.readers.claimed.as_slice()
        ),
        (2, &[3][..])
    );
    assert_eq!(
        (
            patch.core.statistics.coefficients_scanned,
            patch.core.statistics.coding_symbols,
            patch.core.statistics.newly_significant
        ),
        (3, 2, 0)
    );
    patch.signs(Magnitude::from_u64(1)).unwrap();
    assert!(
        !patch.core.output.coefficients()[1].negative
            && patch.core.output.coefficients()[2].negative
    );
    assert!(
        !patch.discovery.coefficients()[1].negative && !patch.discovery.coefficients()[2].negative
    );
    assert_eq!(patch.pending, [(1, 0), (2, 0)]);
    assert_eq!(
        (
            patch.core.readers.forward.physical_bits_read,
            patch.core.readers.claimed.as_slice()
        ),
        (4, &[15][..])
    );
    assert_eq!(
        (
            patch.core.statistics.coding_symbols,
            patch.core.statistics.newly_significant
        ),
        (4, 2)
    );
    assert_eq!(patch.core.readers.finish(&[0x0b]), Ok(()));

    let mut cleanup = CodeBlockPlane::new(5, 1).unwrap();
    cleanup.coefficients[0] = raw_refinement_coefficient(3, [0; 5], true, false, false);
    let (output, statistics) = decode_ht_refinement_plane(
        &cleanup,
        refinement_segment(&[0x77]),
        1,
        2,
        false,
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(
        output
            .coefficients()
            .iter()
            .map(|c| (c.magnitude, c.negative))
            .collect::<Vec<_>>(),
        [(3, false), (1, false), (1, true), (1, true), (1, false)]
    );
    assert_eq!(
        (
            statistics.coefficients_scanned,
            statistics.coding_symbols,
            statistics.newly_significant
        ),
        (5, 8, 4)
    );
}

#[test]
fn ht_full_refinement_vertical_causality_changes_only_actual_neighbor_admission() {
    let limits = ResourceLimits::default();
    let mut cleanup = CodeBlockPlane::new(1, 5).unwrap();
    cleanup.coefficients[4] = raw_refinement_coefficient(3, [0; 5], true, false, false);
    let (noncausal, statistics) =
        decode_ht_refinement_plane(&cleanup, refinement_segment(&[3]), 1, 2, false, &limits)
            .unwrap();
    assert_eq!(
        noncausal.coefficients()[3],
        CoefficientState {
            magnitude: 1,
            magnitude_high: [0; 5],
            legacy_bitplane: None,
            significant: true,
            negative: true,
            refined: false,
        }
    );
    assert_eq!(
        (
            statistics.coefficients_scanned,
            statistics.coding_symbols,
            statistics.newly_significant
        ),
        (5, 2, 1)
    );
    let (causal, statistics) =
        decode_ht_refinement_plane(&cleanup, refinement_segment(&[0]), 1, 2, true, &limits)
            .unwrap();
    assert_eq!(causal, cleanup);
    assert_eq!(
        (
            statistics.coefficients_scanned,
            statistics.coding_symbols,
            statistics.newly_significant
        ),
        (5, 0, 0)
    );
    assert_eq!(
        decode_ht_refinement_plane(&cleanup, refinement_segment(&[3]), 1, 2, true, &limits),
        Err(invalid_code_block())
    );
}

#[test]
fn ht_full_refinement_first_errors_keep_real_reader_claim_and_counter_order() {
    let coefficient = raw_refinement_coefficient(3, [0; 5], true, false, false);
    for field in 0..3 {
        let cleanup = CodeBlockPlane {
            width: 1,
            height: 1,
            coefficients: vec![coefficient],
        };
        let mut core = refinement_core(cleanup, &[1], true);
        match field {
            0 => core.statistics.coefficients_scanned = u32::MAX,
            1 => core.statistics.coding_symbols = u32::MAX,
            _ => core.statistics.refined_coefficients = u32::MAX,
        }
        assert_eq!(
            core.magnitude_sample(0, 0, Magnitude::from_u64(1), 3),
            Err(arithmetic_overflow())
        );
        assert_eq!(
            core.output.coefficients()[0].magnitude,
            if field == 0 { 3 } else { 4 }
        );
        assert_eq!(core.output.coefficients()[0].refined, field != 0);
        assert_eq!(
            core.statistics.coefficients_scanned,
            if field == 0 { u32::MAX } else { 1 }
        );
        assert_eq!(
            core.statistics.coding_symbols,
            if field == 1 {
                u32::MAX
            } else {
                u32::from(field == 2)
            }
        );
        assert_eq!(
            core.statistics.refined_coefficients,
            if field == 2 { u32::MAX } else { 0 }
        );
        assert_eq!(
            core.readers.reverse.unwrap().physical_bits_read,
            u64::from(field != 0)
        );
        assert_eq!(core.readers.claimed, [u8::from(field != 0)]);
    }
    let mut work = refinement_core(
        CodeBlockPlane {
            width: 1,
            height: 1,
            coefficients: vec![coefficient],
        },
        &[1],
        true,
    );
    work.readers.reverse.as_mut().unwrap().maximum_work_units = 0;
    assert_eq!(
        work.magnitude_sample(0, 0, Magnitude::from_u64(1), 3),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 0,
            actual: 1,
        })
    );
    assert_eq!(work.output.coefficients()[0], coefficient);
    assert_eq!(
        (
            work.readers.reverse.unwrap().physical_bits_read,
            work.readers.claimed.as_slice()
        ),
        (1, &[0][..])
    );
    assert_eq!(
        (
            work.statistics.coefficients_scanned,
            work.statistics.coding_symbols
        ),
        (1, 0)
    );

    let mut cleanup = CodeBlockPlane::new(2, 1).unwrap();
    cleanup.coefficients[0] = coefficient;
    let mut core = refinement_core(cleanup.clone(), &[0xff], true);
    core.magnitude_pass(2, 1, Magnitude::from_u64(1), 2)
        .unwrap();
    let discovery = core.output.clone();
    let (result, phase) = run_ht_significance_pass(
        HtSigpropPlaneState { core, discovery },
        2,
        1,
        Magnitude::from_u64(1),
        false,
    );
    assert_eq!(result, Err(invalid_code_block()));
    assert!(phase.core.output.coefficients()[0].refined);
    assert!(!phase.core.output.coefficients()[1].significant);
    assert_eq!(
        (
            phase.core.readers.forward.physical_bits_read,
            phase.core.readers.reverse.unwrap().physical_bits_read
        ),
        (1, 1)
    );
    assert_eq!(
        (
            phase.core.readers.claimed.as_slice(),
            phase.core.readers.stuffed.as_slice()
        ),
        (&[1][..], &[0x80][..])
    );
    assert_eq!(
        (
            phase.core.statistics.coefficients_scanned,
            phase.core.statistics.coding_symbols,
            phase.core.statistics.refined_coefficients
        ),
        (4, 1, 1)
    );
    assert_eq!(
        decode_ht_refinement_plane(
            &cleanup,
            refinement_segment(&[0xff]),
            2,
            2,
            false,
            &ResourceLimits::default()
        ),
        Err(invalid_code_block())
    );
    assert_eq!(cleanup.coefficients()[0], coefficient);
}

#[test]
fn ht_full_refinement_native_rejections_overflow_underflow_and_zero_are_exact() {
    let limits = ResourceLimits::default();
    let empty = CodeBlockPlane::new(1, 1).unwrap();
    for passes in 0_u8..=u8::MAX {
        for planes in [0_u16, 1, 2, 292, 293, u16::MAX] {
            let result = decode_ht_refinement_plane(
                &empty,
                refinement_segment(&[]),
                passes,
                planes,
                false,
                &limits,
            );
            if !(1..=2).contains(&passes) || !(2..=292).contains(&planes) {
                assert_eq!(result, Err(invalid_code_block()));
            } else {
                let (output, stats) = result.unwrap();
                assert_eq!(output, empty);
                assert_eq!(
                    stats,
                    Tier1PassStatistics {
                        coefficients_scanned: u32::from(passes),
                        ..Tier1PassStatistics::default()
                    }
                );
            }
        }
    }
    for (low, high, bytes, delta, error) in [
        (u64::MAX, [u64::MAX; 5], &[1][..], 1, arithmetic_overflow()),
        (1, [0; 5], &[][..], 2, invalid_code_block()),
        (1, [0; 5], &[][..], 1, invalid_code_block()),
    ] {
        let coefficient = raw_refinement_coefficient(low, high, true, true, false);
        let mut core = refinement_core(
            CodeBlockPlane {
                width: 1,
                height: 1,
                coefficients: vec![coefficient],
            },
            bytes,
            true,
        );
        assert_eq!(
            core.magnitude_sample(0, 0, Magnitude::from_u64(delta), 3),
            Err(error)
        );
        assert_eq!(core.output.coefficients()[0], coefficient);
        assert_eq!(
            (
                core.statistics.coefficients_scanned,
                core.statistics.coding_symbols,
                core.statistics.refined_coefficients
            ),
            (1, 0, 0)
        );
        assert_eq!(
            core.readers.reverse.unwrap().physical_bits_read
                + core.readers.reverse.unwrap().fill_bits_read,
            1
        );
    }
}

#[test]
fn ht_refinement_neighbor_overflows_and_malformed_shapes_have_ordered_effects() {
    let mut plane = CodeBlockPlane::new(2, 2).unwrap();
    plane.coefficients[1] = raw_refinement_coefficient(1, [0; 5], true, false, false);
    let mut summary = NeighborSummary {
        horizontal_significant: 1,
        horizontal_sign_balance: i8::MAX,
        ..NeighborSummary::default()
    };
    assert_eq!(
        plane.accumulate_neighbor(0, 0, (1, 0), NeighborKind::Horizontal, &mut summary),
        Err(arithmetic_overflow())
    );
    assert_eq!(
        (
            summary.horizontal_significant,
            summary.horizontal_sign_balance
        ),
        (2, i8::MAX)
    );
    summary.horizontal_significant = u8::MAX;
    let before = summary;
    assert_eq!(
        plane.accumulate_neighbor(0, 0, (1, 0), NeighborKind::Horizontal, &mut summary),
        Err(arithmetic_overflow())
    );
    assert_eq!(summary, before);
    assert_eq!(
        plane.accumulate_neighbor(0, 0, (-1, 0), NeighborKind::Horizontal, &mut summary),
        Ok(())
    );
    assert_eq!(summary, before);

    let mut discovery = plane.clone();
    discovery.coefficients.truncate(2);
    let mut patch = HtSignificancePatchState {
        core: refinement_core(plane, &[1], false),
        discovery,
        pending: vec![(1, 1)],
    };
    let before = patch.discovery.clone();
    assert_eq!(
        patch.discover_sample(0, 0, Magnitude::from_u64(1), false),
        Err(invalid_code_block())
    );
    assert_eq!(patch.discovery, before);
    assert_eq!(patch.pending, [(1, 1)]);
    assert_eq!(
        (
            patch.core.statistics.coefficients_scanned,
            patch.core.statistics.coding_symbols,
            patch.core.readers.forward.physical_bits_read
        ),
        (1, 0, 0)
    );
}

#[test]
fn ht_full_symbol_caller_distinguishes_none_empty_refinement_and_pre_refinement_plane() {
    let limits = ResourceLimits::default();
    for (refinement, passes, magnitude, refined, scanned, symbols, refined_count, retained) in [
        (None, 1, 3, false, 1, 1, 0, 0),
        (Some(&[][..]), 2, 3, false, 2, 1, 0, 1),
        (Some(&[][..]), 3, 2, true, 3, 2, 1, 2),
        (Some(&[1][..]), 3, 3, true, 3, 2, 1, 2),
    ] {
        let segments = parse_ht_block_segments(&[0, 0x63, 0], refinement, &limits).unwrap();
        let mut decoder = cleanup_caller_decoder();
        decoder.maximum_passes = 4;
        let mut expected = decoder.clone();
        let cleanup_coefficient = CoefficientState {
            magnitude: 3,
            magnitude_high: [0; 5],
            legacy_bitplane: None,
            significant: true,
            negative: true,
            refined: false,
        };
        expected.plane = CodeBlockPlane {
            width: 1,
            height: 1,
            coefficients: vec![CoefficientState {
                magnitude,
                refined,
                ..cleanup_coefficient
            }],
        };
        expected.ht_cleanup_plane = Some(CodeBlockPlane {
            width: 1,
            height: 1,
            coefficients: vec![cleanup_coefficient],
        });
        expected.ht_refinement_data = refinement.unwrap_or(&[]).to_vec();
        expected.ht_refinement_passes = retained;
        expected.ht_decoded_bitplanes = 2;
        expected.ht_current_set_has_cleanup = true;
        expected.ht_sets_seen += 1;
        expected.next_pass += passes;
        expected.decoded_segments += if refinement.is_some() { 2 } else { 1 };
        expected.decoded_bytes += if refinement == Some(&[1][..]) { 4 } else { 3 };
        let result = decoder
            .decode_ht_coefficient_symbols(segments, passes, 1, 0, &limits)
            .unwrap();
        assert_eq!(
            result,
            Tier1SegmentDecode {
                passes,
                bytes: if refinement == Some(&[1][..]) { 4 } else { 3 },
                statistics: Tier1PassStatistics {
                    coefficients_scanned: scanned,
                    coding_symbols: symbols,
                    newly_significant: 1,
                    refined_coefficients: refined_count,
                    run_mode_columns: 0
                }
            }
        );
        assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
    }
    for (maximum_passes, passes, bytes, error) in [
        (1, 2, &[][..], invalid_code_block()),
        (4, 0, &[][..], invalid_code_block()),
        (4, 257, &[][..], arithmetic_overflow()),
        (4, 3, &[0xff][..], invalid_code_block()),
    ] {
        let segments = parse_ht_block_segments(&[0, 0x63, 0], Some(bytes), &limits).unwrap();
        let mut decoder = cleanup_caller_decoder();
        decoder.maximum_passes = maximum_passes;
        let mut expected = decoder.clone();
        expected.ht_refinement_data.clear();
        expected.ht_refinement_passes = 0;
        assert_eq!(
            decoder.decode_ht_coefficient_symbols(segments, passes, 1, 0, &limits),
            Err(error)
        );
        assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
    }
}

#[test]
fn ht_public_segment_entry_binds_actual_pass_byte_work_admission_and_error_order() {
    let default = ResourceLimits::default();
    let pass_zero = default.with_maximum_code_block_passes(0).unwrap();
    let byte_two = default.with_maximum_code_block_bytes(2).unwrap();
    let byte_three = default.with_maximum_code_block_bytes(3).unwrap();
    let work_four = default.with_maximum_work_units(4).unwrap();
    for (maximum_passes, cleanup, limits, error) in [
        (u32::MAX, &[0][..], default, arithmetic_overflow()),
        (
            u32::MAX,
            &[0][..],
            pass_zero,
            DecodeError::LimitExceeded {
                resource: Resource::CodeBlockPasses,
                limit: 0,
                actual: 1,
            },
        ),
        (
            4,
            &[0, 0, 0][..],
            byte_two,
            DecodeError::LimitExceeded {
                resource: Resource::CodeBlockBytes,
                limit: 2,
                actual: 3,
            },
        ),
        (4, &[0, 0, 0][..], byte_three, invalid_code_block()),
        (
            4,
            &[0, 0x63, 0][..],
            byte_three,
            DecodeError::LimitExceeded {
                resource: Resource::CodeBlockBytes,
                limit: 3,
                actual: 14,
            },
        ),
        (
            4,
            &[0, 0x63, 0][..],
            work_four,
            DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 4,
                actual: 5,
            },
        ),
    ] {
        let mut decoder = cleanup_caller_decoder();
        decoder.maximum_passes = maximum_passes;
        decoder.next_pass = 0;
        decoder.ht_sets_seen = 0;
        let before = format!("{decoder:?}");
        assert_eq!(
            decoder.decode_high_throughput_segments(cleanup, 1, None, 0, &limits),
            Err(error)
        );
        assert_eq!(format!("{decoder:?}"), before);
    }
    let mut decoder = cleanup_caller_decoder();
    decoder.maximum_passes = u32::MAX;
    decoder.next_pass = u32::MAX;
    decoder.ht_sets_seen = 1;
    let before = format!("{decoder:?}");
    assert_eq!(
        decoder.decode_high_throughput_segments(&[], 1, None, 0, &default),
        Err(invalid_code_block())
    );
    assert_eq!(format!("{decoder:?}"), before);
    decoder.ht_sets_seen = 0;
    let before = format!("{decoder:?}");
    assert_eq!(
        decoder.decode_high_throughput_segments(&[], 1, None, 0, &pass_zero),
        Err(arithmetic_overflow())
    );
    assert_eq!(format!("{decoder:?}"), before);
}

#[test]
fn ht_public_segment_entry_keeps_none_and_some_empty_distinct_without_assumed_context() {
    let limits = ResourceLimits::default();
    for (refinement, refinement_passes, scanned, retained) in [
        (None, 0, 1, 0),
        (Some(&[][..]), 1, 2, 1),
        (Some(&[][..]), 2, 3, 2),
    ] {
        let mut decoder = cleanup_caller_decoder();
        decoder.maximum_passes = 4;
        decoder.next_pass = 0;
        decoder.ht_sets_seen = 0;
        let before_legacy = format!("{:?}", decoder.legacy_segment);
        let result = decoder
            .decode_high_throughput_segments(
                &[0, 0x63, 0],
                1,
                refinement,
                refinement_passes,
                &limits,
            )
            .unwrap();
        assert_eq!(
            (
                result.passes,
                result.bytes,
                result.statistics.coefficients_scanned
            ),
            (u32::from(refinement_passes) + 1, 3, scanned)
        );
        assert_eq!(
            (
                decoder.ht_refinement_passes,
                decoder.decoded_segments,
                decoder.decoded_bytes
            ),
            (retained, if refinement.is_none() { 8 } else { 9 }, 14)
        );
        assert_eq!(
            decoder.plane.coefficients()[0].magnitude,
            if refinement_passes == 2 { 2 } else { 3 }
        );
        assert_eq!(
            decoder.plane.coefficients()[0].refined,
            refinement_passes == 2
        );
        assert_eq!(format!("{:?}", decoder.legacy_segment), before_legacy);
    }
    for (refinement, count) in [(None, 1), (Some(&[][..]), 0)] {
        let mut decoder = cleanup_caller_decoder();
        let before = format!("{decoder:?}");
        assert_eq!(
            decoder.decode_high_throughput_segments(&[], 1, refinement, count, &limits),
            Err(invalid_code_block())
        );
        assert_eq!(format!("{decoder:?}"), before);
    }
}

fn retained_refinement_decoder() -> Tier1CodeBlockDecoder {
    let mut decoder = cleanup_caller_decoder();
    let mut cleanup = CodeBlockPlane::new(2, 1).unwrap();
    cleanup.coefficients[0] = CoefficientState {
        magnitude: 3,
        significant: true,
        ..CoefficientState::default()
    };
    decoder.ht_cleanup_plane = Some(cleanup);
    decoder.plane = CodeBlockPlane {
        width: 1,
        height: 1,
        coefficients: vec![raw_refinement_coefficient(
            29,
            [1, 2, 3, 4, 5],
            false,
            true,
            true,
        )],
    };
    decoder.ht_refinement_data.clear();
    decoder.ht_refinement_passes = 0;
    decoder.ht_decoded_bitplanes = 2;
    decoder.ht_current_set_has_cleanup = true;
    decoder.next_pass = 1;
    decoder.maximum_passes = 0;
    decoder
}

fn literal_replayed_plane(magnitude: u64, refined: bool) -> CodeBlockPlane {
    CodeBlockPlane {
        width: 2,
        height: 1,
        coefficients: vec![
            CoefficientState {
                magnitude,
                significant: true,
                refined,
                ..CoefficientState::default()
            },
            CoefficientState {
                magnitude: 1,
                significant: true,
                ..CoefficientState::default()
            },
        ],
    }
}

#[test]
fn ht_continuation_replays_real_concatenation_from_cleanup_not_current_output() {
    let limits = ResourceLimits::default()
        .with_maximum_code_block_passes(0)
        .unwrap();
    let mut decoder = retained_refinement_decoder();
    decoder.next_pass = 2;
    decoder.ht_refinement_passes = 1;
    decoder.ht_refinement_data = vec![1];
    let mut expected = decoder.clone();
    expected.plane = literal_replayed_plane(3, true);
    expected.ht_refinement_data = vec![1, 1];
    expected.ht_refinement_passes = 2;
    expected.next_pass = 3;
    expected.decoded_segments += 1;
    expected.decoded_bytes += 1;
    let result = decoder
        .decode_high_throughput_refinement(&[1], 1, &limits)
        .unwrap();
    assert_eq!(
        result,
        Tier1SegmentDecode {
            passes: 1,
            bytes: 1,
            statistics: Tier1PassStatistics {
                coefficients_scanned: 4,
                coding_symbols: 3,
                newly_significant: 1,
                refined_coefficients: 1,
                run_mode_columns: 0,
            }
        }
    );
    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
    assert!(decoder.next_pass > decoder.maximum_passes);

    let mut decoder = retained_refinement_decoder();
    decoder.ht_refinement_data = Vec::with_capacity(64);
    decoder.ht_refinement_data.push(1);
    let source_pointer = decoder.ht_refinement_data.as_ptr();
    assert_eq!(
        decoder.clone().ht_refinement_data.capacity(),
        decoder.ht_refinement_data.clone().capacity()
    );
    let copy_capacity = super::ht_refinement::copy_ht_refinement_bytes(
        &decoder.ht_refinement_data,
        HtRefinementCopyRole::RetainedReplay,
    )
    .unwrap()
    .capacity();
    let mut expected = decoder.clone();
    expected.plane = literal_replayed_plane(3, false);
    expected.ht_refinement_passes = 1;
    expected.next_pass = 2;
    expected.decoded_segments += 1;
    let result = decoder
        .decode_high_throughput_refinement(&[], 1, &limits)
        .unwrap();
    assert_eq!(
        (
            result.bytes,
            result.statistics.coefficients_scanned,
            result.statistics.coding_symbols
        ),
        (0, 2, 2)
    );
    assert_eq!(decoder.ht_refinement_data.capacity(), copy_capacity);
    assert_ne!(decoder.ht_refinement_data.as_ptr(), source_pointer);
    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
}

#[test]
fn ht_continuation_empty_concatenation_preserves_output_and_skips_replay_only() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(0)
        .unwrap()
        .with_maximum_code_block_passes(0)
        .unwrap();
    let mut decoder = retained_refinement_decoder();
    decoder.ht_cleanup_plane = Some(CodeBlockPlane {
        width: 0,
        height: 7,
        coefficients: vec![],
    });
    decoder.ht_decoded_bitplanes = 0;
    decoder.ht_refinement_data = Vec::with_capacity(64);
    let mut expected = decoder.clone();
    expected.ht_refinement_passes = 1;
    expected.next_pass = 2;
    expected.decoded_segments += 1;
    assert_eq!(
        decoder.decode_high_throughput_refinement(&[], 1, &limits),
        Ok(Tier1SegmentDecode {
            passes: 1,
            bytes: 0,
            statistics: Tier1PassStatistics::default()
        })
    );
    assert_eq!(decoder.ht_refinement_data.capacity(), 64);
    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));

    let before = format!("{decoder:?}");
    let byte_limit = limits.with_maximum_code_block_bytes(10).unwrap();
    assert_eq!(
        decoder.decode_high_throughput_refinement(&[], 1, &byte_limit),
        Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlockBytes,
            limit: 10,
            actual: 11
        })
    );
    assert_eq!(format!("{decoder:?}"), before);
    decoder.ht_cleanup_plane = None;
    let before = format!("{decoder:?}");
    assert_eq!(
        decoder.decode_high_throughput_refinement(&[], 1, &byte_limit),
        Err(invalid_code_block())
    );
    assert_eq!(format!("{decoder:?}"), before);
}

#[test]
fn ht_continuation_rejects_before_commit_but_keeps_exact_late_accounting_writes() {
    let limits = ResourceLimits::default();
    for (nonempty, segment_overflow) in [(false, false), (false, true), (true, false), (true, true)]
    {
        let mut decoder = retained_refinement_decoder();
        let (input, passes): (&[u8], u8) = if nonempty && !segment_overflow {
            (&[1, 1], 2)
        } else if nonempty {
            (&[1], 1)
        } else if segment_overflow {
            (&[], 1)
        } else {
            (&[], 2)
        };
        if segment_overflow {
            decoder.decoded_segments = u32::MAX;
        } else {
            decoder.next_pass = u32::MAX - 1;
        }
        let mut expected = decoder.clone();
        if nonempty {
            expected.plane = literal_replayed_plane(3, passes == 2);
            expected.ht_refinement_data = input.to_vec();
        }
        expected.ht_refinement_passes = passes;
        if segment_overflow {
            expected.next_pass += u32::from(passes);
        }
        assert_eq!(
            decoder.decode_high_throughput_refinement(input, passes, &limits),
            Err(arithmetic_overflow())
        );
        assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
    }
    for input in [&[0xff][..], &[0x80][..]] {
        let mut decoder = retained_refinement_decoder();
        let before = format!("{decoder:?}");
        assert_eq!(
            decoder.decode_high_throughput_refinement(input, 1, &limits),
            Err(invalid_code_block())
        );
        assert_eq!(format!("{decoder:?}"), before);
    }
    let mut decoder = retained_refinement_decoder();
    decoder.decoded_bytes = u64::MAX;
    let before = format!("{decoder:?}");
    assert_eq!(
        decoder.decode_high_throughput_refinement(&[1], 1, &limits),
        Err(arithmetic_overflow())
    );
    assert_eq!(format!("{decoder:?}"), before);
}

#[test]
fn ht_continuation_native_pass_domain_and_retained_size_boundaries_are_exact() {
    let limits = ResourceLimits::default();
    let template = retained_refinement_decoder();
    for existing in 0_u8..=u8::MAX {
        for additional in 0_u8..=u8::MAX {
            let mut decoder = template.clone();
            decoder.ht_refinement_passes = existing;
            decoder.ht_cleanup_plane = Some(CodeBlockPlane {
                width: 0,
                height: 0,
                coefficients: vec![],
            });
            let result = decoder.decode_high_throughput_refinement(&[], additional, &limits);
            if additional > 0 && u16::from(existing) + u16::from(additional) <= 2 {
                assert!(result.is_ok());
                assert_eq!(decoder.ht_refinement_passes, existing + additional);
                assert_eq!(decoder.next_pass, 1 + u32::from(additional));
            } else {
                assert_eq!(result, Err(invalid_code_block()));
                assert_eq!(
                    (
                        decoder.ht_refinement_passes,
                        decoder.next_pass,
                        decoder.decoded_segments
                    ),
                    (existing, 1, template.decoded_segments)
                );
            }
        }
    }
    for (retained, incoming, accepted) in [(2046, 0, true), (2046, 1, false), (2047, 0, false)] {
        let mut decoder = retained_refinement_decoder();
        decoder.ht_refinement_data = vec![0; retained];
        let before = format!("{decoder:?}");
        let result = decoder.decode_high_throughput_refinement(&vec![0; incoming], 1, &limits);
        if accepted {
            let result = result.unwrap();
            assert_eq!((result.bytes, result.statistics.coding_symbols), (0, 1));
            assert_eq!(decoder.ht_refinement_data.len(), 2046);
        } else {
            assert_eq!(result, Err(invalid_code_block()));
            assert_eq!(format!("{decoder:?}"), before);
        }
    }
}

#[test]
fn ht_placeholder_all_native_passes_and_phases_preserve_actual_admission() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(0)
        .unwrap()
        .with_maximum_code_block_bytes(0)
        .unwrap();
    let mut template = retained_refinement_decoder();
    template.maximum_passes = u32::MAX;
    template.ht_sets_seen = 0;
    template.ht_refinement_data = vec![7, 9];
    template.ht_refinement_passes = u8::MAX;
    template.decoded_bytes = u64::MAX;
    for phase in 0_u32..3 {
        for has_cleanup in [false, true] {
            for passes in 0_u8..=u8::MAX {
                let mut decoder = template.clone();
                decoder.next_pass = phase;
                decoder.ht_current_set_has_cleanup = has_cleanup;
                let before = format!("{decoder:?}");
                let admitted = (1..=2).contains(&passes)
                    && if phase == 0 {
                        passes == 1
                    } else {
                        u32::from(passes) <= 3 - phase && !has_cleanup
                    };
                let result = decoder.skip_high_throughput_segment(passes, &limits);
                if !admitted {
                    assert_eq!(result, Err(invalid_code_block()));
                    assert_eq!(format!("{decoder:?}"), before);
                } else {
                    let mut expected = template.clone();
                    expected.next_pass = phase + u32::from(passes);
                    expected.decoded_segments += 1;
                    expected.ht_current_set_has_cleanup = has_cleanup;
                    if phase == 0 {
                        expected.ht_current_set_has_cleanup = false;
                        expected.ht_refinement_data.clear();
                        expected.ht_refinement_passes = 0;
                    }
                    assert_eq!(
                        result,
                        Ok(Tier1SegmentDecode {
                            passes: u32::from(passes),
                            bytes: 0,
                            statistics: Tier1PassStatistics::default()
                        })
                    );
                    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
                }
            }
        }
    }
}

#[test]
fn ht_placeholder_replacement_and_late_errors_retain_cleanup_option_and_prior_writes() {
    let limits = ResourceLimits::default();
    for failure in 0..4 {
        let mut decoder = retained_refinement_decoder();
        decoder.next_pass = 3;
        decoder.maximum_passes = 10;
        decoder.ht_refinement_data = vec![5, 6];
        decoder.ht_refinement_passes = 2;
        decoder.ht_sets_seen = if failure == 1 { u16::MAX } else { 1 };
        decoder.allow_multiple_ht_sets = failure != 0;
        if failure == 2 {
            decoder.decoded_segments = u32::MAX;
        }
        let mut expected = decoder.clone();
        let result = decoder.skip_high_throughput_segment(1, &limits);
        if failure < 2 {
            assert_eq!(
                result,
                Err(if failure == 0 {
                    invalid_code_block()
                } else {
                    arithmetic_overflow()
                })
            );
        } else {
            expected.ht_sets_seen = 2;
            expected.ht_current_set_has_cleanup = false;
            expected.ht_refinement_data.clear();
            expected.ht_refinement_passes = 0;
            expected.next_pass = 4;
            if failure == 2 {
                assert_eq!(result, Err(arithmetic_overflow()));
            } else {
                expected.decoded_segments += 1;
                assert!(result.is_ok());
            }
        }
        assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
    }
    let mut decoder = retained_refinement_decoder();
    decoder.next_pass = 3;
    decoder.maximum_passes = 3;
    let before = format!("{decoder:?}");
    let pass_zero = limits.with_maximum_code_block_passes(0).unwrap();
    assert_eq!(
        decoder.skip_high_throughput_segment(1, &pass_zero),
        Err(invalid_code_block())
    );
    assert_eq!(format!("{decoder:?}"), before);
    decoder.maximum_passes = 10;
    let before = format!("{decoder:?}");
    assert_eq!(
        decoder.skip_high_throughput_segment(1, &pass_zero),
        Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlockPasses,
            limit: 0,
            actual: 4,
        })
    );
    assert_eq!(format!("{decoder:?}"), before);
    decoder.next_pass = u32::MAX;
    decoder.maximum_passes = u32::MAX;
    let before = format!("{decoder:?}");
    assert_eq!(
        decoder.skip_high_throughput_segment(1, &pass_zero),
        Err(arithmetic_overflow())
    );
    assert_eq!(format!("{decoder:?}"), before);
}

#[test]
fn ht_actual_staged_group_runs_all_placeholder_groups_and_rolls_back_failures() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    for (passes, planes, groups, magnitude) in [(4, 3, 1, 3), (7, 4, 2, 3), (163, 55, 54, 1)] {
        let mut decoder =
            Tier1CodeBlockDecoder::new(1, 1, planes, SubbandOrientation::Ll, style).unwrap();
        let result = decoder
            .decode_segment(&[0, 0x63, 0], passes, &limits)
            .unwrap();
        assert_eq!((result.passes, result.bytes), (u32::from(passes), 3));
        assert_eq!(
            decoder.plane.coefficients()[0],
            CoefficientState {
                magnitude,
                significant: true,
                negative: true,
                ..CoefficientState::default()
            }
        );
        assert_eq!(
            (
                decoder.next_pass,
                decoder.decoded_segments,
                decoder.decoded_bytes,
                decoder.ht_sets_seen
            ),
            (u32::from(passes), groups * 2 + 1, 3, 1)
        );
        assert_eq!(
            result.statistics,
            Tier1PassStatistics {
                coefficients_scanned: 1,
                coding_symbols: 1,
                newly_significant: 1,
                ..Tier1PassStatistics::default()
            }
        );
    }
    for (input, work, error) in [
        (&[2, 0][..], 1000, invalid_code_block()),
        (
            &[0, 0x63, 0][..],
            4,
            DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 4,
                actual: 5,
            },
        ),
        (&[][..], 1000, invalid_code_block()),
    ] {
        let mut decoder =
            Tier1CodeBlockDecoder::new(1, 1, 3, SubbandOrientation::Hh, style).unwrap();
        decoder.legacy_segment = cleanup_caller_decoder().legacy_segment;
        decoder.ht_refinement_data = vec![6, 7];
        let before = format!("{decoder:?}");
        let limits = limits.with_maximum_work_units(work).unwrap();
        assert_eq!(decoder.decode_segment(input, 4, &limits), Err(error));
        assert_eq!(format!("{decoder:?}"), before);
    }
}

#[test]
fn ht_actual_groups_continue_and_replace_using_real_retained_state() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut decoder = Tier1CodeBlockDecoder::new(1, 1, 5, SubbandOrientation::Ll, style).unwrap();
    decoder.decode_segment(&[0, 0x63, 0], 4, &limits).unwrap();
    assert_eq!(
        (
            decoder.plane.coefficients()[0].magnitude,
            decoder.ht_decoded_bitplanes,
            decoder.next_pass
        ),
        (12, 4, 4)
    );
    let first = decoder
        .decode_high_throughput_refinement(&[0], 1, &limits)
        .unwrap();
    assert_eq!(
        (
            first.bytes,
            first.statistics.coefficients_scanned,
            first.statistics.coding_symbols
        ),
        (1, 1, 0)
    );
    let second = decoder
        .decode_high_throughput_refinement(&[1], 1, &limits)
        .unwrap();
    assert_eq!(
        (
            second.bytes,
            second.statistics.coefficients_scanned,
            second.statistics.refined_coefficients
        ),
        (1, 2, 1)
    );
    assert_eq!(decoder.ht_refinement_data, [0, 1]);
    assert_eq!(
        (
            decoder.plane.coefficients()[0].magnitude,
            decoder.next_pass,
            decoder.decoded_bytes
        ),
        (14, 6, 5)
    );
    let before = format!("{decoder:?}");
    assert_eq!(
        decoder.skip_high_throughput_segment(1, &limits),
        Err(invalid_code_block())
    );
    assert_eq!(format!("{decoder:?}"), before);
    decoder.allow_multiple_ht_sets = true;
    decoder.skip_high_throughput_segment(1, &limits).unwrap();
    assert_eq!(
        decoder.ht_cleanup_plane.as_ref().unwrap().coefficients()[0].magnitude,
        12
    );
    assert!(!decoder.ht_current_set_has_cleanup);
    assert!(decoder.ht_refinement_data.is_empty());
    assert_eq!(decoder.ht_refinement_passes, 0);
    decoder.skip_high_throughput_segment(2, &limits).unwrap();
    decoder
        .decode_high_throughput_segments(&[0, 0x63, 0], 1, None, 0, &limits)
        .unwrap();
    assert_eq!(
        (
            decoder.plane.coefficients()[0].magnitude,
            decoder.ht_decoded_bitplanes
        ),
        (3, 2)
    );
    assert_eq!(
        (
            decoder.next_pass,
            decoder.decoded_segments,
            decoder.decoded_bytes,
            decoder.ht_sets_seen
        ),
        (10, 8, 8, 3)
    );
}

#[test]
fn ht_whole_decoder_clone_preserves_all_raw_malformed_fields_and_independent_storage() {
    let limits = ResourceLimits::default();
    let mut mq = MqDecoder::new(&[0xff, 0x90], &limits).unwrap();
    for context in 0..19 {
        mq.set_context(context, (context * 2) as u8, context % 2 == 0)
            .unwrap();
    }
    for value in 0_u16..1600 {
        let mut decoder = cleanup_caller_decoder();
        decoder.plane = CodeBlockPlane {
            width: if value % 2 == 0 { 0 } else { u16::MAX },
            height: value,
            coefficients: vec![
                raw_refinement_coefficient(
                    u64::from(value),
                    [u64::MAX; 5],
                    value % 2 == 0,
                    true,
                    value % 3 == 0
                );
                usize::from(value % 4)
            ],
        };
        decoder.bitplane_state = Some(Tier1BitplaneState {
            width: value,
            height: u16::MAX,
            bitplane: u16::MAX,
            significant_before: vec![true; usize::from(value % 5)],
            significance_visited: vec![false; usize::from(value % 3)],
            significance_propagation_complete: value & 1 != 0,
            magnitude_refinement_complete: value & 2 != 0,
            cleanup_complete: value & 4 != 0,
        });
        decoder.mq_context_state = Some(mq.context_state());
        if value % 2 == 0 {
            let legacy = decoder.legacy_segment.as_mut().unwrap();
            legacy.bitplane_state = decoder.bitplane_state.clone();
            legacy.mq_context_state = decoder.mq_context_state;
            legacy.input = vec![value as u8; usize::from(value % 7)];
            legacy.plane = decoder.plane.clone();
        } else {
            decoder.legacy_segment = None;
        }
        decoder.ht_cleanup_plane = if value % 3 == 0 {
            None
        } else {
            Some(decoder.plane.clone())
        };
        decoder.ht_refinement_data = vec![value as u8; usize::from(value % 9)];
        decoder.ht_refinement_passes = value as u8;
        decoder.next_pass = u32::MAX - u32::from(value);
        decoder.decoded_bytes = u64::MAX - u64::from(value);
        let original = format!("{decoder:?}");
        let mut cloned = decoder.clone();
        assert_eq!(format!("{cloned:?}"), original);
        assert_eq!(
            cloned.plane.coefficients.capacity(),
            decoder.plane.coefficients.clone().capacity()
        );
        assert_eq!(
            cloned.ht_refinement_data.capacity(),
            decoder.ht_refinement_data.clone().capacity()
        );
        cloned.ht_refinement_data.push(7);
        cloned
            .bitplane_state
            .as_mut()
            .unwrap()
            .significant_before
            .push(false);
        if let Some(legacy) = cloned.legacy_segment.as_mut() {
            legacy.input.push(9);
        }
        if let Some(coefficient) = cloned.plane.coefficients.first_mut() {
            coefficient.magnitude = 99;
        }
        if let Some(plane) = cloned.ht_cleanup_plane.as_mut() {
            plane.coefficients.push(CoefficientState::default());
        }
        assert_eq!(format!("{decoder:?}"), original);
    }
}

#[test]
fn ht_staged_group_complete_native_pass_domain_uses_real_grouping_and_rollback() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    for passes in 0_u8..=u8::MAX {
        let mut decoder =
            Tier1CodeBlockDecoder::new(1, 1, 55, SubbandOrientation::Ll, style).unwrap();
        let before = format!("{decoder:?}");
        let result = decoder.decode_segment(&[0, 0x63, 0], passes, &limits);
        if passes > 0 && passes <= 164 && (passes - 1) % 3 == 0 {
            let result = result.unwrap();
            let groups = u32::from((passes - 1) / 3);
            let planes = 55 - u16::try_from(groups).unwrap();
            let expected_magnitude = if planes == 1 {
                1
            } else {
                3_u64 << (planes - 2)
            };
            assert_eq!((result.passes, result.bytes), (u32::from(passes), 3));
            assert_eq!(
                (
                    decoder.plane.coefficients()[0].magnitude,
                    decoder.plane.coefficients()[0].negative
                ),
                (expected_magnitude, true)
            );
            assert_eq!(
                (
                    decoder.next_pass,
                    decoder.decoded_segments,
                    decoder.decoded_bytes,
                    decoder.ht_sets_seen
                ),
                (u32::from(passes), groups * 2 + 1, 3, 1)
            );
        } else {
            assert_eq!(result, Err(invalid_code_block()));
            assert_eq!(format!("{decoder:?}"), before);
        }
    }
    for remaining in 1_u8..=8 {
        let mut decoder =
            Tier1CodeBlockDecoder::new(1, 1, 55, SubbandOrientation::Ll, style).unwrap();
        let result = decoder.run_ht_placeholder_groups(remaining, &limits);
        let groups = u32::from(remaining / 3) + u32::from(remaining % 3 != 0);
        assert_eq!(decoder.next_pass, groups * 3);
        assert_eq!(decoder.decoded_segments, groups * 2);
        if remaining % 3 == 0 {
            assert_eq!(result, Ok(()));
        } else {
            assert_eq!(result, Err(arithmetic_overflow()));
        }
    }
}

#[test]
fn ht_staged_group_every_late_failure_keeps_original_state_not_staged_partial_writes() {
    let defaults = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    for failure in 0..5 {
        let mut decoder =
            Tier1CodeBlockDecoder::new(1, 1, 3, SubbandOrientation::Hh, style).unwrap();
        decoder.legacy_segment = cleanup_caller_decoder().legacy_segment;
        decoder.ht_refinement_data = vec![17, 19];
        decoder.ht_refinement_passes = 2;
        decoder.ht_cleanup_plane = Some(CodeBlockPlane {
            width: 0,
            height: 0,
            coefficients: vec![],
        });
        let (input, limits, expected) = match failure {
            0 => (
                &[0, 0x63, 0][..],
                defaults.with_maximum_code_block_passes(1).unwrap(),
                DecodeError::LimitExceeded {
                    resource: Resource::CodeBlockPasses,
                    limit: 1,
                    actual: 3,
                },
            ),
            1 => (
                &[0, 0x63, 0][..],
                defaults.with_maximum_work_units(4).unwrap(),
                DecodeError::LimitExceeded {
                    resource: Resource::WorkUnits,
                    limit: 4,
                    actual: 5,
                },
            ),
            2 => (&[2, 0][..], defaults, invalid_code_block()),
            3 => {
                decoder.decoded_segments = u32::MAX;
                (&[0, 0x63, 0][..], defaults, arithmetic_overflow())
            }
            _ => {
                decoder.ht_sets_seen = u16::MAX;
                decoder.allow_multiple_ht_sets = true;
                (&[0, 0x63, 0][..], defaults, arithmetic_overflow())
            }
        };
        let before = format!("{decoder:?}");
        assert_eq!(decoder.decode_segment(input, 4, &limits), Err(expected));
        assert_eq!(format!("{decoder:?}"), before);
    }
    let mut mixed = Tier1CodeBlockDecoder::new(
        1,
        1,
        3,
        SubbandOrientation::Ll,
        Tier1CodingStyle {
            block_coding: Tier1BlockCoding::Mixed,
            ..Tier1CodingStyle::default()
        },
    )
    .unwrap();
    mixed.ht_cleanup_plane = Some(CodeBlockPlane {
        width: 0,
        height: 0,
        coefficients: vec![],
    });
    mixed.ht_current_set_has_cleanup = false;
    assert!(mixed.decode_segment(&[0, 0x63, 0], 4, &defaults).is_ok());
    assert_eq!(
        (mixed.next_pass, mixed.plane.coefficients()[0].magnitude),
        (4, 3)
    );
}

#[test]
fn mixed_segment_dispatch_uses_actual_cleanup_option_not_current_flag() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0xc0).unwrap();
    let mut legacy = Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
    legacy.decode_segment(&[0xff], 1, &limits).unwrap();
    assert_eq!(legacy.plane.signed_coefficient(0, 0).unwrap(), 0);
    assert_eq!(
        (
            legacy.next_pass,
            legacy.decoded_segments,
            legacy.decoded_bytes
        ),
        (1, 1, 1)
    );
    let mut ht = Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
    ht.ht_cleanup_plane = Some(ht.plane.clone());
    assert!(!ht.ht_current_set_has_cleanup);
    ht.decode_segment(&[0, 0x63, 0], 1, &limits).unwrap();
    assert_eq!(ht.plane.signed_coefficient(0, 0).unwrap(), -1);
    assert_eq!(
        (ht.next_pass, ht.decoded_segments, ht.decoded_bytes),
        (1, 1, 3)
    );
    for mut decoder in [legacy, ht] {
        let before = format!("{decoder:?}");
        assert_eq!(
            decoder.decode_segment(&[], 0, &limits),
            Err(invalid_code_block())
        );
        assert_eq!(format!("{decoder:?}"), before);
    }
}

#[test]
fn ht_packet_segment_routes_real_slices_and_keeps_progress_after_decoder_effects() {
    let limits = ResourceLimits::default();
    let mut decoder = cleanup_caller_decoder();
    decoder.next_pass = 0;
    decoder.ht_sets_seen = 0;
    let mut expected = decoder.clone();
    expected.plane = literal_cleanup_coefficient();
    expected.ht_cleanup_plane = Some(literal_cleanup_coefficient());
    expected.ht_refinement_data.clear();
    expected.ht_refinement_passes = 0;
    expected.ht_decoded_bitplanes = 1;
    expected.ht_current_set_has_cleanup = true;
    expected.ht_sets_seen = 1;
    expected.next_pass = 1;
    expected.decoded_segments += 1;
    expected.decoded_bytes += 3;
    let mut offset = 1;
    let mut decoded_passes = 17;
    crate::packet::ht_route_test_support::segment_body(
        &mut decoder,
        1,
        3,
        &[0xaa, 0, 0x63, 0, 0x90],
        &mut offset,
        &mut decoded_passes,
        &limits,
    )
    .unwrap();
    assert_eq!((offset, decoded_passes), (4, 18));
    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));

    let mut decoder = retained_refinement_decoder();
    let mut expected = decoder.clone();
    expected.ht_refinement_passes = 1;
    expected.next_pass += 1;
    expected.decoded_segments += 1;
    let mut offset = 0;
    let mut decoded_passes = u32::MAX;
    assert_eq!(
        crate::packet::ht_route_test_support::segment_body(
            &mut decoder,
            1,
            0,
            &[],
            &mut offset,
            &mut decoded_passes,
            &limits,
        ),
        Err(arithmetic_overflow())
    );
    assert_eq!((offset, decoded_passes), (0, u32::MAX));
    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
}

#[test]
fn ht_packet_segment_pass_length_range_and_route_errors_keep_exact_first_state() {
    let limits = ResourceLimits::default();
    for (passes, length, start, body, expected_error) in [
        (0, 1, usize::MAX, &[][..], invalid_code_block()),
        (1, 1, usize::MAX, &[][..], arithmetic_overflow()),
        (1, 0, 1, &[][..], invalid_code_block()),
        (2, 2, 0, &[1][..], invalid_code_block()),
    ] {
        let mut decoder = retained_refinement_decoder();
        let before = format!("{decoder:?}");
        let mut offset = start;
        let mut decoded_passes = 11;
        assert_eq!(
            crate::packet::ht_route_test_support::segment_body(
                &mut decoder,
                passes,
                length,
                body,
                &mut offset,
                &mut decoded_passes,
                &limits,
            ),
            Err(expected_error)
        );
        assert_eq!((offset, decoded_passes), (start, 11));
        assert_eq!(format!("{decoder:?}"), before);
    }
    for (phase, has_cleanup, passes, body) in [(0, true, 2, &[][..]), (1, false, 1, &[1][..])] {
        let mut decoder = retained_refinement_decoder();
        decoder.next_pass = phase;
        decoder.ht_current_set_has_cleanup = has_cleanup;
        let before = format!("{decoder:?}");
        let mut offset = 0;
        let mut decoded_passes = 0;
        assert_eq!(
            crate::packet::ht_route_test_support::segment_body(
                &mut decoder,
                passes,
                body.len() as u32,
                body,
                &mut offset,
                &mut decoded_passes,
                &limits,
            ),
            Err(invalid_code_block())
        );
        assert_eq!((offset, decoded_passes), (0, 0));
        assert_eq!(format!("{decoder:?}"), before);
    }
}

fn cleanup_caller_decoder() -> Tier1CodeBlockDecoder {
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut decoder = Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Hh, style).unwrap();
    decoder.plane.coefficients[0] = CoefficientState {
        magnitude: 17,
        magnitude_high: [3, 5, 7, 11, 13],
        legacy_bitplane: Some(u16::MAX),
        significant: false,
        negative: true,
        refined: true,
    };
    decoder.next_pass = 4;
    decoder.decoded_segments = 7;
    decoder.decoded_bytes = 11;
    decoder.ht_sets_seen = 9;
    decoder.ht_refinement_data = vec![77, 88];
    decoder.ht_refinement_passes = 2;
    decoder.ht_decoded_bitplanes = 19;
    decoder.ht_cleanup_plane = Some(decoder.plane.clone());
    decoder.legacy_decode_work = 123;
    decoder.legacy_segment = Some(LegacySegmentState {
        plane: decoder.plane.clone(),
        next_pass: 11,
        bitplane: 17,
        bitplane_state: None,
        mq_context_state: None,
        reset_contexts_before_mq: true,
        decoded_segments: 13,
        decoded_bytes: 19,
        input: vec![0xde, 0xad],
        passes: 23,
    });
    decoder
}

fn literal_cleanup_coefficient() -> CodeBlockPlane {
    CodeBlockPlane {
        width: 1,
        height: 1,
        coefficients: vec![CoefficientState {
            magnitude: 1,
            magnitude_high: [0; 5],
            legacy_bitplane: None,
            significant: true,
            negative: true,
            refined: false,
        }],
    }
}

#[test]
fn ht_cleanup_caller_composes_real_metadata_numeric_duplicate_and_complete_decoder_state() {
    let limits = ResourceLimits::default();
    let segments = parse_ht_block_segments(&[0, 0x63, 0], None, &limits).unwrap();
    let mut decoder = cleanup_caller_decoder();
    let mut expected = decoder.clone();
    expected.plane = literal_cleanup_coefficient();
    expected.ht_cleanup_plane = Some(literal_cleanup_coefficient());
    expected.ht_refinement_data.clear();
    expected.ht_refinement_passes = 0;
    expected.ht_decoded_bitplanes = 1;
    expected.ht_current_set_has_cleanup = true;
    expected.ht_sets_seen = 10;
    expected.next_pass = 5;
    expected.decoded_segments = 8;
    expected.decoded_bytes = 14;
    let result = decoder
        .decode_ht_coefficient_symbols(segments, 1, 1, 0, &limits)
        .unwrap();
    assert_eq!(
        result,
        Tier1SegmentDecode {
            passes: 1,
            bytes: 3,
            statistics: Tier1PassStatistics {
                coefficients_scanned: 1,
                coding_symbols: 1,
                newly_significant: 1,
                refined_coefficients: 0,
                run_mode_columns: 0,
            }
        }
    );
    assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
}

#[test]
fn ht_cleanup_caller_preserves_metadata_before_native_pass_error_order_and_full_failure_frame() {
    let limits = ResourceLimits::default();
    let bad_metadata = parse_ht_block_segments(&[2, 0], None, &limits).unwrap();
    let valid = parse_ht_block_segments(&[0, 0x63, 0], None, &limits).unwrap();
    let mut decoder = cleanup_caller_decoder();
    decoder.maximum_passes = u32::MAX;
    let before = format!("{decoder:?}");
    assert_eq!(
        decoder.decode_ht_coefficient_symbols(bad_metadata, 1, 1, 0, &limits),
        Err(invalid_code_block())
    );
    assert_eq!(format!("{decoder:?}"), before);
    for (maximum_passes, skipped) in [(u32::MAX, 0), (196606, 0), (1, 2)] {
        let mut decoder = cleanup_caller_decoder();
        decoder.maximum_passes = maximum_passes;
        let before = format!("{decoder:?}");
        assert_eq!(
            decoder.decode_ht_coefficient_symbols(valid, 1, 1, skipped, &limits),
            Err(arithmetic_overflow())
        );
        assert_eq!(format!("{decoder:?}"), before);
    }
    let mut decoder = cleanup_caller_decoder();
    decoder.maximum_passes = 0;
    let before = format!("{decoder:?}");
    assert_eq!(
        decoder.decode_ht_coefficient_symbols(valid, 1, 1, 0, &limits),
        Err(invalid_code_block())
    );
    assert_eq!(format!("{decoder:?}"), before);
}

#[test]
fn ht_cleanup_caller_metadata_work_failure_retains_every_decoder_field() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(23)
        .unwrap();
    let segments = parse_ht_block_segments(&[0xff, 3, 0], None, &limits).unwrap();
    let mut decoder = cleanup_caller_decoder();
    decoder.plane = CodeBlockPlane::new(5, 5).unwrap();
    let before = format!("{decoder:?}");
    assert_eq!(
        decoder.decode_ht_coefficient_symbols(segments, 1, 1, 0, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 23,
            actual: 24,
        })
    );
    assert_eq!(format!("{decoder:?}"), before);
}

#[test]
fn ht_cleanup_caller_accounting_failures_preserve_ordered_commits_not_rollback() {
    let limits = ResourceLimits::default();
    let segments = parse_ht_block_segments(&[0, 0x63, 0], None, &limits).unwrap();
    for failure in 0..4 {
        let mut decoder = cleanup_caller_decoder();
        match failure {
            0 => decoder.ht_sets_seen = u16::MAX,
            1 => decoder.next_pass = u32::MAX,
            2 => decoder.decoded_segments = u32::MAX,
            _ => decoder.decoded_bytes = u64::MAX,
        }
        let mut expected = decoder.clone();
        expected.plane = literal_cleanup_coefficient();
        expected.ht_cleanup_plane = Some(literal_cleanup_coefficient());
        expected.ht_refinement_data.clear();
        expected.ht_refinement_passes = 0;
        expected.ht_decoded_bitplanes = 1;
        expected.ht_current_set_has_cleanup = true;
        if failure > 0 {
            expected.ht_sets_seen += 1;
        }
        if failure > 1 {
            expected.next_pass += 1;
        }
        if failure > 2 {
            expected.decoded_segments += 1;
        }
        assert_eq!(
            decoder.decode_ht_coefficient_symbols(segments, 1, 1, 0, &limits),
            Err(arithmetic_overflow())
        );
        assert_eq!(format!("{decoder:?}"), format!("{expected:?}"));
    }
}

#[test]
fn ht_cleanup_duplicate_preserves_full_raw_coefficients_and_rejects_bad_shapes() {
    let decoder = cleanup_caller_decoder();
    let duplicate = decoder
        .plane
        .duplicate(CoefficientStorageRole::Duplicate)
        .unwrap();
    assert_eq!(duplicate, decoder.plane);
    for plane in [
        CodeBlockPlane {
            width: 0,
            height: 1,
            coefficients: vec![CoefficientState::default()],
        },
        CodeBlockPlane {
            width: 2,
            height: 2,
            coefficients: vec![CoefficientState::default()],
        },
        CodeBlockPlane {
            width: 1,
            height: 1,
            coefficients: vec![CoefficientState::default(); 2],
        },
    ] {
        let before = plane.clone();
        assert_eq!(
            plane.duplicate(CoefficientStorageRole::Duplicate),
            Err(invalid_code_block())
        );
        assert_eq!(plane, before);
    }
}

fn plane_quad(x: u16, y: u16, significance: u8, u_base: u8) -> HtQuadMetadata {
    HtQuadMetadata {
        x,
        y,
        context: 255,
        initial_row: true,
        significance,
        embedded_magnitude: 0,
        embedded_bit_mask: 0,
        u_offset: true,
        u_base,
        codeword_bits: 255,
    }
}

fn plane_metadata(width: u16, height: u16, quads: Vec<HtQuadMetadata>) -> HtCleanupMetadata {
    HtCleanupMetadata {
        width,
        height,
        quads,
        significant_samples: u16::MAX,
        mel_bits: u32::MAX,
        vlc_bits: u32::MAX,
        mel_events: u32::MAX,
    }
}

fn plane_state(input: &[u8], width: u16, height: u16) -> HtCleanupPlaneReconstruction<'_> {
    HtCleanupPlaneReconstruction {
        output: CodeBlockPlane::new(width, height).unwrap(),
        reader: HtForwardMagSgnReader::new(input, &ResourceLimits::default()).unwrap(),
        previous_exponents: vec![5, 4, 3],
        current_exponents: vec![9, 8, 7],
        statistics: Tier1PassStatistics::default(),
    }
}

#[test]
fn ht_cleanup_plane_places_literal_full_words_flags_and_ignores_old_coefficients() {
    let limits = ResourceLimits::default();
    let mut input = CodeBlockPlane::new(1, 2).unwrap();
    input.coefficients[0] = CoefficientState {
        magnitude: u64::MAX,
        magnitude_high: [u64::MAX; 5],
        legacy_bitplane: Some(u16::MAX),
        negative: true,
        significant: true,
        refined: true,
    };
    let cleanup = parse_ht_block_segments(&[0xfa, 2, 0], None, &limits)
        .unwrap()
        .cleanup();
    let metadata = plane_metadata(1, 2, vec![plane_quad(0, 0, 3, 2)]);
    let (output, statistics) =
        reconstruct_ht_cleanup_plane(&input, cleanup, &metadata, 2, 3, &limits).unwrap();
    let expected = CoefficientState {
        magnitude: 10,
        magnitude_high: [0; 5],
        legacy_bitplane: None,
        negative: false,
        significant: true,
        refined: false,
    };
    assert_eq!(output.coefficients(), &[expected, expected]);
    assert_eq!(
        statistics,
        Tier1PassStatistics {
            coefficients_scanned: 2,
            coding_symbols: 2,
            newly_significant: 2,
            refined_coefficients: 0,
            run_mode_columns: 0
        }
    );
    assert_eq!(input.coefficients[0].legacy_bitplane, Some(u16::MAX));

    let data = [
        0xff, 0x7f, 0xff, 0x7f, 0xff, 0x7f, 0xff, 0x7f, 0xff, 0x7f, 2, 0,
    ];
    let cleanup = parse_ht_block_segments(&data, None, &limits)
        .unwrap()
        .cleanup();
    let metadata = plane_metadata(1, 1, vec![plane_quad(0, 0, 1, 75)]);
    let (output, statistics) =
        reconstruct_ht_cleanup_plane(&input, cleanup, &metadata, 75, 292, &limits).unwrap();
    assert_eq!(
        output.coefficients()[0],
        CoefficientState {
            magnitude: 0,
            magnitude_high: [0, 0, 0, 1_u64 << 34, 1_u64 << 45],
            legacy_bitplane: None,
            negative: true,
            significant: true,
            refined: false,
        }
    );
    assert_eq!(output.coefficients()[1], CoefficientState::default());
    assert_eq!((output.width(), output.height()), (1, 2));
    assert_eq!(
        (
            statistics.coefficients_scanned,
            statistics.coding_symbols,
            statistics.newly_significant
        ),
        (1, 1, 1)
    );
}

#[test]
fn ht_cleanup_plane_preserves_permissive_metadata_domains_and_coordinate_error_order() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(0)
        .unwrap();
    let cleanup = parse_ht_block_segments(&[2, 0], None, &limits)
        .unwrap()
        .cleanup();
    let input = CodeBlockPlane::new(1, 1).unwrap();
    for metadata in [
        plane_metadata(1, 0, vec![]),
        plane_metadata(1, 0, vec![plane_quad(0, 0, 255, 0)]),
        plane_metadata(1, 1, vec![plane_quad(0, 0, 0xf0, 255)]),
    ] {
        let (output, statistics) =
            reconstruct_ht_cleanup_plane(&input, cleanup, &metadata, 255, u16::MAX, &limits)
                .unwrap();
        assert_eq!(output.coefficients(), &[CoefficientState::default()]);
        assert_eq!(
            (statistics.coding_symbols, statistics.newly_significant),
            (0, 0)
        );
    }
    let coordinate_overflow = plane_metadata(1, 0, vec![plane_quad(u16::MAX, 0, 0, 0)]);
    assert_eq!(
        reconstruct_ht_cleanup_plane(&input, cleanup, &coordinate_overflow, 0, 0, &limits),
        Err(arithmetic_overflow())
    );
    let mut noninitial = plane_quad(0, 0, 0, 1);
    noninitial.initial_row = false;
    assert_eq!(
        reconstruct_ht_cleanup_plane(
            &input,
            cleanup,
            &plane_metadata(1, 0, vec![noninitial]),
            0,
            0,
            &limits
        ),
        Err(invalid_code_block())
    );
    let no_numeric = plane_metadata(1, 1, vec![plane_quad(0, 0, 0, 76)]);
    assert!(reconstruct_ht_cleanup_plane(&input, cleanup, &no_numeric, 255, 0, &limits).is_ok());
    let numeric = plane_metadata(1, 1, vec![plane_quad(0, 0, 1, 76)]);
    assert_eq!(
        reconstruct_ht_cleanup_plane(&input, cleanup, &numeric, 255, 0, &limits),
        Err(invalid_code_block())
    );
    let malformed = CodeBlockPlane {
        width: 0,
        height: 1,
        coefficients: vec![CoefficientState::default()],
    };
    assert_eq!(
        reconstruct_ht_cleanup_plane(&malformed, cleanup, &no_numeric, 255, 0, &limits),
        Err(invalid_code_block())
    );
}

#[test]
fn ht_cleanup_plane_placement_errors_follow_magsgn_consumption_and_scanning() {
    let mut duplicate = plane_state(&[0xff], 1, 1);
    let quad = plane_quad(0, 0, 1, 1);
    duplicate.quad(quad, 1, 1, 1, 1, 2, 0).unwrap();
    let output = duplicate.output.clone();
    assert_eq!(
        duplicate.quad(quad, 1, 1, 1, 1, 2, 1),
        Err(invalid_code_block())
    );
    assert_eq!(duplicate.output, output);
    assert_eq!(
        (
            duplicate.statistics.coefficients_scanned,
            duplicate.statistics.coding_symbols,
            duplicate.statistics.newly_significant,
            duplicate.reader.physical_bits_read,
            duplicate.reader.work_units
        ),
        (2, 1, 1, 2, 2)
    );

    let mut mismatch = plane_state(&[0xff], 1, 1);
    let before = mismatch.output.clone();
    assert_eq!(
        mismatch.sample(plane_quad(1, 0, 1, 1), 2, 1, 0, 1, 1, 0),
        Err(invalid_code_block())
    );
    assert_eq!(mismatch.output, before);
    assert_eq!(
        (
            mismatch.statistics.coefficients_scanned,
            mismatch.statistics.coding_symbols,
            mismatch.statistics.newly_significant,
            mismatch.reader.physical_bits_read
        ),
        (1, 0, 0, 1)
    );
    assert_eq!(mismatch.current_exponents, [9, 8, 7]);
}

#[test]
fn ht_cleanup_plane_statistic_overflows_retain_each_ordered_partial_effect() {
    let quad = plane_quad(0, 0, 3, 1);
    for field in 0..3 {
        let mut state = plane_state(&[0xff], 2, 2);
        match field {
            0 => state.statistics.coefficients_scanned = u32::MAX,
            1 => state.statistics.coding_symbols = u32::MAX,
            _ => state.statistics.newly_significant = u32::MAX,
        }
        assert_eq!(
            state.sample(quad, 2, 2, 0, 1, 1, 1),
            Err(arithmetic_overflow())
        );
        assert_eq!(
            state.statistics.coefficients_scanned,
            if field == 0 { u32::MAX } else { 1 }
        );
        assert_eq!(
            state.statistics.coding_symbols,
            if field == 1 {
                u32::MAX
            } else if field == 2 {
                1
            } else {
                0
            }
        );
        assert_eq!(
            state.statistics.newly_significant,
            if field == 2 { u32::MAX } else { 0 }
        );
        assert_eq!(state.output.coefficients()[2].significant, field != 0);
        assert_eq!(state.reader.physical_bits_read, u64::from(field != 0));
        assert_eq!(state.current_exponents, [9, 8, 7]);
        assert_eq!(state.previous_exponents, [5, 4, 3]);
    }
    let mut work = plane_state(&[0xff], 2, 2);
    work.reader.maximum_work_units = 0;
    let before = work.output.clone();
    assert_eq!(
        work.sample(quad, 2, 2, 0, 1, 1, 0),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 0,
            actual: 1,
        })
    );
    assert_eq!(work.output, before);
    assert_eq!(
        (
            work.statistics.coefficients_scanned,
            work.statistics.coding_symbols,
            work.reader.work_units,
            work.reader.physical_bits_read
        ),
        (1, 0, 1, 1)
    );
}

#[test]
fn ht_cleanup_plane_stencils_reset_max_overwrite_swap_and_drive_noninitial_u() {
    let mut state = plane_state(&[], 4, 4);
    state
        .sample(plane_quad(0, 0, 2, 1), 4, 4, 0, 1, 1, 1)
        .unwrap();
    assert_eq!(state.current_exponents, [9, 8, 7]);
    state
        .sample(plane_quad(0, 0, 8, 1), 4, 4, 0, 1, 1, 3)
        .unwrap();
    assert_eq!(state.current_exponents, [9, 1, 7]);

    let mut state = plane_state(&[], 4, 4);
    state
        .quad(plane_quad(0, 0, 0, 0), 4, 4, 4, 1, 2, 0)
        .unwrap();
    assert_eq!(state.current_exponents, [0, 0, 0]);
    assert_eq!(state.previous_exponents, [5, 4, 3]);
    state
        .quad(plane_quad(2, 0, 10, 4), 4, 4, 4, 1, 2, 1)
        .unwrap();
    assert_eq!(state.previous_exponents, [0, 4, 4]);
    assert_eq!(state.current_exponents, [5, 4, 3]);
    let mut noninitial = plane_quad(0, 2, 3, 1);
    noninitial.initial_row = false;
    state.quad(noninitial, 4, 4, 4, 1, 2, 2).unwrap();
    assert_eq!(state.current_exponents, [3, 0, 0]);
    assert_eq!(state.previous_exponents, [0, 4, 4]);
    assert_eq!(
        (
            state.output.coefficient(0, 2).unwrap().magnitude,
            state.output.coefficient(0, 3).unwrap().magnitude
        ),
        (4, 4)
    );
    assert_eq!(
        (
            state.statistics.coefficients_scanned,
            state.statistics.coding_symbols,
            state.statistics.newly_significant,
            state.reader.fill_bits_read
        ),
        (12, 4, 4, 14)
    );
    assert_eq!(
        complete_ht_kappa(1, 1, 255, 0, 75),
        Err(arithmetic_overflow())
    );
    assert_eq!(
        complete_ht_kappa(0, 1, 255, 0, 75),
        Err(invalid_code_block())
    );
    assert_eq!(
        complete_ht_kappa(1, 0xf0, 255, 0, 75),
        Err(invalid_code_block())
    );
    assert_eq!(complete_ht_kappa(1, 3, 2, 4, 3), Ok(3));
}

#[test]
fn ht_cleanup_plane_finish_preserves_outputs_and_reports_physical_padding_stuffing_and_budget() {
    for (input, maximum_work, error, physical, work) in [
        (&[0xfe][..], 100, invalid_code_block(), 1, 1),
        (
            &[0xff, 0x80][..],
            100,
            DecodeError::MalformedInput {
                offset: 1,
                kind: MalformedKind::InvalidBitStuffing,
            },
            8,
            8,
        ),
        (
            &[0xff][..],
            7,
            DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 7,
                actual: 8,
            },
            8,
            8,
        ),
    ] {
        let mut state = plane_state(input, 1, 1);
        state.reader.maximum_work_units = maximum_work;
        state.statistics.coefficients_scanned = 42;
        let output = state.output.clone();
        assert_eq!(state.finish(), Err(error));
        assert_eq!(state.output, output);
        assert_eq!(state.statistics.coefficients_scanned, 42);
        assert_eq!(state.previous_exponents, [5, 4, 3]);
        assert_eq!(state.current_exponents, [9, 8, 7]);
        assert_eq!(
            (state.reader.physical_bits_read, state.reader.work_units),
            (physical, work)
        );
    }
    let limits = ResourceLimits::default();
    let cleanup = parse_ht_block_segments(&[0xfe, 2, 0], None, &limits)
        .unwrap()
        .cleanup();
    let metadata = plane_metadata(1, 1, vec![]);
    assert_eq!(
        reconstruct_ht_cleanup_plane(
            &CodeBlockPlane::new(1, 1).unwrap(),
            cleanup,
            &metadata,
            0,
            0,
            &limits
        ),
        Err(invalid_code_block())
    );
}

#[test]
fn ht_numeric_reconstruction_has_independent_full_value_sign_and_exponent_fixtures() {
    let limits = ResourceLimits::default();
    for (data, completed, embedded_bit, embedded_value, planes, low, negative, exponent, bits) in [
        (&[0x01][..], 3, false, false, 1, 1, true, 1, 3),
        (&[0x06][..], 3, false, false, 3, 18, false, 3, 3),
        (&[0x00][..], 1, false, true, 1, 2, false, 2, 1),
        (&[][..], 3, false, false, 1, 4, true, 3, 3),
        (&[][..], 3, true, true, 1, 4, true, 3, 2),
        (&[][..], 3, true, false, 1, 2, true, 2, 2),
        (&[][..], 3, false, true, 1, 8, true, 4, 3),
    ] {
        let mut reader = HtForwardMagSgnReader::new(data, &limits).unwrap();
        let result =
            reconstruct_ht_magnitude(&mut reader, completed, embedded_bit, embedded_value, planes)
                .unwrap();
        assert_eq!(
            (result.0.to_u64(), result.1, result.2),
            (Some(low), negative, exponent)
        );
        for index in 1..6 {
            assert_eq!(result.0.limb(index), Some(0));
        }
        assert_eq!(reader.work_units, bits);
        assert_eq!(reader.physical_bits_read + reader.fill_bits_read, bits);
    }
    let mut no_read = HtForwardMagSgnReader::new(&[], &limits).unwrap();
    no_read.work_units = u64::MAX;
    no_read.fill_bits_read = u64::MAX;
    let before = no_read;
    let result = reconstruct_ht_magnitude(&mut no_read, 1, true, false, 1).unwrap();
    assert_eq!((result.0.to_u64(), result.1, result.2), (Some(1), false, 1));
    assert_eq!(no_read, before);
}

#[test]
fn ht_numeric_reconstruction_preserves_wide_bits_at_the_native_precision_ceiling() {
    let data = [0xff, 0x7f, 0xff, 0x7f, 0xff, 0x7f, 0xff, 0x7f, 0xff, 0x7f];
    let limits = ResourceLimits::default();
    let mut unscaled = HtForwardMagSgnReader::new(&data, &limits).unwrap();
    let (magnitude, negative, exponent) =
        reconstruct_ht_magnitude(&mut unscaled, 75, false, false, 1).unwrap();
    for (index, expected) in [0, 1024, 0, 0, 0, 0].into_iter().enumerate() {
        assert_eq!(magnitude.limb(index), Some(expected));
    }
    assert_eq!(
        (
            negative,
            exponent,
            unscaled.physical_bits_read,
            unscaled.fill_bits_read
        ),
        (true, 75, 75, 0)
    );
    let mut scaled = HtForwardMagSgnReader::new(&data, &limits).unwrap();
    let (magnitude, negative, exponent) =
        reconstruct_ht_magnitude(&mut scaled, 75, false, false, 292).unwrap();
    for (index, expected) in [0, 0, 0, 0, 1_u64 << 34, 1_u64 << 45]
        .into_iter()
        .enumerate()
    {
        assert_eq!(magnitude.limb(index), Some(expected));
    }
    assert_eq!(magnitude.to_u64(), None);
    assert_eq!(
        (
            negative,
            exponent,
            scaled.work_units,
            scaled.physical_bits_read
        ),
        (true, 75, 75, 75)
    );
    assert_eq!(
        (
            scaled.next_byte,
            scaled.value,
            scaled.next_bit,
            scaled.last_bit,
            scaled.has_byte,
            scaled.current_is_physical,
            scaled.previous_was_ff
        ),
        (10, 0x7f, 7, 6, true, true, false)
    );
}

#[test]
fn ht_numeric_first_reader_failures_keep_every_actual_cursor_and_counter() {
    let limits = ResourceLimits::default();
    let data = [0xff, 0x80];
    let mut reader = HtForwardMagSgnReader::new(&data, &limits).unwrap();
    assert_eq!(
        reconstruct_ht_magnitude(&mut reader, 9, false, false, 1),
        Err(DecodeError::MalformedInput {
            offset: 1,
            kind: MalformedKind::InvalidBitStuffing
        })
    );
    assert_eq!(
        reader,
        HtForwardMagSgnReader {
            input: &data,
            next_byte: 1,
            value: 0xff,
            next_bit: 8,
            last_bit: 7,
            has_byte: true,
            current_is_physical: true,
            previous_was_ff: true,
            physical_bits_read: 8,
            fill_bits_read: 0,
            work_units: 8,
            maximum_work_units: 1_000_000_000,
        }
    );
    let budget = limits.with_maximum_work_units(2).unwrap();
    let data = [0x06];
    let mut physical = HtForwardMagSgnReader::new(&data, &budget).unwrap();
    assert_eq!(
        reconstruct_ht_magnitude(&mut physical, 3, false, false, 1),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 2,
            actual: 3
        })
    );
    assert_eq!(
        physical,
        HtForwardMagSgnReader {
            input: &data,
            next_byte: 1,
            value: 6,
            next_bit: 3,
            last_bit: 7,
            has_byte: true,
            current_is_physical: true,
            previous_was_ff: false,
            physical_bits_read: 3,
            fill_bits_read: 0,
            work_units: 3,
            maximum_work_units: 2,
        }
    );
    let mut fill = HtForwardMagSgnReader::new(&[], &budget).unwrap();
    assert_eq!(
        reconstruct_ht_magnitude(&mut fill, 3, false, false, 1),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 2,
            actual: 3
        })
    );
    assert_eq!(
        fill,
        HtForwardMagSgnReader {
            input: &[],
            next_byte: 0,
            value: 0xff,
            next_bit: 3,
            last_bit: 7,
            has_byte: true,
            current_is_physical: false,
            previous_was_ff: true,
            physical_bits_read: 0,
            fill_bits_read: 3,
            work_units: 3,
            maximum_work_units: 2,
        }
    );
}

#[test]
fn ht_numeric_header_and_native_overflow_order_do_not_assume_a_valid_reader() {
    let limits = ResourceLimits::default();
    let mut reader = HtForwardMagSgnReader::new(&[], &limits).unwrap();
    reader.fill_bits_read = u64::MAX;
    reader.work_units = 7;
    let before = reader;
    for (completed, planes) in [(0, 1), (76, 1), (255, 1), (1, 0), (1, 293), (1, u16::MAX)] {
        assert_eq!(
            reconstruct_ht_magnitude(&mut reader, completed, false, false, planes),
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodeBlock
            })
        );
        assert_eq!(reader, before);
    }
    assert_eq!(
        reconstruct_ht_magnitude(&mut reader, 1, false, false, 1),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    assert_eq!(
        reader,
        HtForwardMagSgnReader {
            input: &[],
            next_byte: 0,
            value: 0xff,
            next_bit: 1,
            last_bit: 7,
            has_byte: true,
            current_is_physical: false,
            previous_was_ff: true,
            physical_bits_read: 0,
            fill_bits_read: u64::MAX,
            work_units: 7,
            maximum_work_units: 1_000_000_000,
        }
    );
    assert_eq!(
        center_ht_numeric_magnitude(
            Magnitude::from_limbs([u64::MAX; 6]),
            false,
            255,
            0,
            false,
            1
        ),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    assert_eq!(
        center_ht_numeric_magnitude(
            Magnitude::single_bit(200).unwrap(),
            true,
            201,
            0,
            false,
            292
        ),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    let (value, negative, exponent) =
        center_ht_numeric_magnitude(Magnitude::from_u64(1), true, 255, 0, true, 1).unwrap();
    assert_eq!((value.to_u64(), negative, exponent), (Some(2), true, 1));
}

#[test]
fn ht_complete_metadata_odd_rows_pairs_and_members_have_literal_outputs() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(24)
        .unwrap();
    let metadata = decode_ht_cleanup_metadata(&[0xff, 3, 0], 5, 5, 1, &limits).unwrap();
    let expected_quads: Vec<_> = [
        (0, 0),
        (2, 0),
        (4, 0),
        (0, 2),
        (2, 2),
        (4, 2),
        (0, 4),
        (2, 4),
        (4, 4),
    ]
    .into_iter()
    .map(|(x, y)| HtQuadMetadata {
        x,
        y,
        context: 0,
        initial_row: y == 0,
        significance: 0,
        embedded_magnitude: 0,
        embedded_bit_mask: 0,
        u_offset: false,
        u_base: 1,
        codeword_bits: 0,
    })
    .collect();
    assert_eq!(
        metadata,
        HtCleanupMetadata {
            width: 5,
            height: 5,
            quads: expected_quads,
            significant_samples: 0,
            mel_bits: 6,
            vlc_bits: 0,
            mel_events: 9,
        }
    );
    let one_short = ResourceLimits::default()
        .with_maximum_work_units(23)
        .unwrap();
    assert_eq!(
        decode_ht_cleanup_metadata(&[0xff, 3, 0], 5, 5, 1, &one_short),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 23,
            actual: 24
        })
    );
}

#[test]
fn ht_metadata_last_row_budget_failure_retains_stored_quad_and_all_counters() {
    let mut readers = ht_cleanup_readers_from_inputs(&[0xff, 3], &[0xff, 3, 0], 23).unwrap();
    let mut quads = Vec::with_capacity(9);
    let mut previous = vec![0; 3];
    let mut significant = 0;
    assert_eq!(
        decode_ht_metadata_row(
            &mut readers,
            &mut quads,
            &mut previous,
            &mut significant,
            3,
            0,
            5,
            5,
            1
        ),
        Ok(())
    );
    assert_eq!(
        (
            quads.len(),
            readers.work_units,
            readers.mel.bits_read,
            readers.mel_events
        ),
        (3, 9, 3, 3)
    );
    assert_eq!(
        decode_ht_metadata_row(
            &mut readers,
            &mut quads,
            &mut previous,
            &mut significant,
            3,
            1,
            5,
            5,
            1
        ),
        Ok(())
    );
    assert_eq!(
        (
            quads.len(),
            readers.work_units,
            readers.mel.bits_read,
            readers.mel_events
        ),
        (6, 17, 5, 6)
    );
    assert_eq!(
        decode_ht_metadata_row(
            &mut readers,
            &mut quads,
            &mut previous,
            &mut significant,
            3,
            2,
            5,
            5,
            1
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 23,
            actual: 24
        })
    );
    assert_eq!(quads.len(), 9);
    assert_eq!(
        quads[8],
        HtQuadMetadata {
            x: 4,
            y: 4,
            context: 0,
            initial_row: false,
            significance: 0,
            embedded_magnitude: 0,
            embedded_bit_mask: 0,
            u_offset: false,
            u_base: 1,
            codeword_bits: 0,
        }
    );
    assert_eq!(previous, [0, 0, 0]);
    assert_eq!(
        (
            significant,
            readers.work_units,
            readers.maximum_work_units,
            readers.mel_state,
            readers.mel_zero_events,
            readers.mel_terminating_one,
            readers.mel_events,
            readers.mel_last_byte,
            readers.vlc_last_byte
        ),
        (0, 24, 23, 6, 0, false, 9, Some(0), None)
    );
    assert_eq!(
        (
            readers.mel.next_byte,
            readers.mel.current_byte,
            readers.mel.value,
            readers.mel.next_bit,
            readers.mel.previous_was_ff,
            readers.mel.bits_read,
            readers.mel.maximum_work_units
        ),
        (1, 0, 0xff, 1, true, 6, 23)
    );
    assert_eq!(
        (
            readers.vlc.current_byte,
            readers.vlc.value,
            readers.vlc.next_bit,
            readers.vlc.last_bit,
            readers.vlc.has_byte,
            readers.vlc.later_byte_requires_unstuffing,
            readers.vlc.bits_read,
            readers.vlc.maximum_work_units
        ),
        (1, 3, 4, 7, true, false, 0, 23)
    );
}

#[test]
fn ht_metadata_actual_word_phase_chooses_each_neighbor_and_west_context() {
    for (previous, left, expected) in [
        ([0, 0, 0], 2, 2),
        ([0, 8, 0], 0, 1),
        ([0, 0, 2], 0, 1),
        ([0, 0, 8], 0, 4),
        ([0, 8, 8], 2, 7),
    ] {
        let mut readers = ht_cleanup_readers_from_inputs(&[0, 0, 4], &[0, 0, 4, 0], 100).unwrap();
        let mut current = [0; 3];
        let mut west = left;
        let (words, contexts) = decode_ht_metadata_words(
            &mut readers,
            &mut current,
            &mut west,
            &previous,
            3,
            2,
            false,
        )
        .unwrap();
        assert_eq!(contexts, [expected, 0]);
        assert_eq!(words[1], 0);
        assert_eq!(&current[..2], &[0, 0]);
        assert_eq!(readers.mel.bits_read, 0);
    }
    let mut readers = ht_cleanup_readers_from_inputs(&[0, 0, 4], &[0, 0, 4, 0], 100).unwrap();
    let mut current = [0; 3];
    let mut west = 0;
    let (_, contexts) = decode_ht_metadata_words(
        &mut readers,
        &mut current,
        &mut west,
        &[0, 2, 0],
        3,
        0,
        false,
    )
    .unwrap();
    assert_eq!(contexts[0], 4);
}

#[test]
fn ht_metadata_sample_error_and_counter_overflow_have_exact_mutation_frames() {
    let mut readers = ht_cleanup_readers_from_inputs(&[0], &[0, 0], 100).unwrap();
    let original_mel = readers.mel;
    let original_vlc = readers.vlc;
    let mut quads = Vec::new();
    let mut significant = 0;
    assert_eq!(
        append_ht_metadata_quad(
            &mut readers,
            &mut quads,
            &mut significant,
            0,
            0,
            1,
            1,
            1,
            0x0055,
            0,
            5,
            1,
            true
        ),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock
        })
    );
    assert_eq!(significant, 1);
    assert!(quads.is_empty());
    assert_eq!(readers.mel, original_mel);
    assert_eq!(readers.vlc, original_vlc);
    assert_eq!((readers.work_units, readers.mel_events), (0, 0));
    significant = u16::MAX;
    assert_eq!(
        append_ht_metadata_quad(
            &mut readers,
            &mut quads,
            &mut significant,
            0,
            0,
            1,
            1,
            1,
            0x0014,
            0,
            1,
            1,
            true
        ),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    assert_eq!(significant, u16::MAX);
    assert!(quads.is_empty());
    assert_eq!(readers.mel, original_mel);
    assert_eq!(readers.vlc, original_vlc);
    assert_eq!(readers.work_units, 0);
    readers.work_units = u64::MAX;
    significant = 0;
    assert_eq!(
        append_ht_metadata_quad(
            &mut readers,
            &mut quads,
            &mut significant,
            0,
            0,
            2,
            2,
            1,
            0x00f7,
            0,
            15,
            1,
            true
        ),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    assert_eq!(
        (significant, quads.len(), readers.work_units),
        (4, 1, u64::MAX)
    );
    assert_eq!(
        quads[0],
        HtQuadMetadata {
            x: 0,
            y: 0,
            context: 0,
            initial_row: true,
            significance: 15,
            embedded_magnitude: 0,
            embedded_bit_mask: 0,
            u_offset: false,
            u_base: 1,
            codeword_bits: 7,
        }
    );
    assert_eq!(readers.mel, original_mel);
    assert_eq!(readers.vlc, original_vlc);
}

#[test]
fn ht_metadata_public_header_order_and_empty_private_streams_are_typed() {
    let limits = ResourceLimits::default();
    let too_small = limits.with_maximum_code_block_bytes(2).unwrap();
    assert_eq!(
        decode_ht_cleanup_metadata(&[0xff, 3, 0], 0, 0, 0, &too_small),
        Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlockBytes,
            limit: 2,
            actual: 3
        })
    );
    for (width, height, maximum) in [
        (0, 1, 1),
        (1, 0, 1),
        (65535, 65535, 1),
        (1, 1, 0),
        (1, 1, 76),
        (1, 1, 255),
    ] {
        assert_eq!(
            decode_ht_cleanup_metadata(&[0xff, 3, 0], width, height, maximum, &limits),
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodeBlock
            })
        );
    }
    let segments = parse_ht_block_segments(&[0xff, 3, 0], None, &limits).unwrap();
    let mut cleanup = segments.cleanup();
    cleanup.mel.bytes = &[];
    assert_eq!(
        decode_ht_cleanup_segment_metadata(cleanup, 1, 1, 1, &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock
        })
    );
    cleanup = segments.cleanup();
    cleanup.vlc.bytes = &[0];
    assert_eq!(
        decode_ht_cleanup_segment_metadata(cleanup, 1, 1, 1, &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock
        })
    );
}

#[test]
fn decodes_bounded_ht_cleanup_quad_metadata() {
    let limits = ResourceLimits::default();
    let metadata = decode_ht_cleanup_metadata(&[0x00, 0x63, 0x00], 1, 1, 1, &limits).unwrap();
    assert_eq!(metadata.width, 1);
    assert_eq!(metadata.height, 1);
    assert_eq!(metadata.significant_samples, 1);
    assert_eq!(metadata.mel_events, 1);
    assert_eq!(metadata.quads.len(), 1);
    assert_eq!(
        metadata.quads[0],
        HtQuadMetadata {
            x: 0,
            y: 0,
            context: 0,
            initial_row: true,
            significance: 1,
            embedded_magnitude: 0,
            embedded_bit_mask: 0,
            u_offset: false,
            u_base: 1,
            codeword_bits: 4,
        }
    );
    assert_eq!(metadata.mel_bits, 1);
    assert_eq!(metadata.vlc_bits, 4);
}

#[test]
fn ht_complete_partition_preserves_every_stream_and_optional_empty() {
    let limits = ResourceLimits::default();
    let cleanup = [0xaa, 0xbb, 0x23, 0];
    let refinement = [0x5a, 0];
    let segments = parse_ht_block_segments(&cleanup, Some(&refinement), &limits).unwrap();
    assert_eq!(segments.bytes(), 6);
    let segment = segments.cleanup();
    assert_eq!(segment.encoded(), &[0xaa, 0xbb, 0x23, 0]);
    assert_eq!(segment.scup(), 3);
    for (view, bytes, offset, direction) in [
        (
            segment.mag_sgn(),
            &[0xaa][..],
            0,
            HtStreamDirection::Forward,
        ),
        (
            segment.mel_vlc(),
            &[0xbb, 0x23, 0][..],
            1,
            HtStreamDirection::Forward,
        ),
        (
            segment.mel(),
            &[0xbb, 0x23][..],
            1,
            HtStreamDirection::Forward,
        ),
        (
            segment.vlc(),
            &[0xbb, 0x23, 0][..],
            1,
            HtStreamDirection::Reverse,
        ),
    ] {
        assert_eq!(
            (view.bytes(), view.offset(), view.direction()),
            (bytes, offset, direction)
        );
    }
    let refinement = segments.refinement().unwrap();
    assert_eq!(refinement.encoded(), &[0x5a, 0]);
    assert_eq!(
        (
            refinement.significance_propagation().bytes(),
            refinement.significance_propagation().offset(),
            refinement.significance_propagation().direction()
        ),
        (&[0x5a, 0][..], 4, HtStreamDirection::Forward)
    );
    assert_eq!(
        (
            refinement.magnitude_refinement().bytes(),
            refinement.magnitude_refinement().offset(),
            refinement.magnitude_refinement().direction()
        ),
        (&[0x5a, 0][..], 4, HtStreamDirection::Reverse)
    );
    let absent = parse_ht_block_segments(&cleanup, None, &limits).unwrap();
    let empty = parse_ht_block_segments(&cleanup, Some(&[]), &limits).unwrap();
    assert_eq!((absent.bytes(), empty.bytes()), (4, 4));
    assert!(absent.refinement().is_none());
    let empty = empty.refinement().unwrap();
    assert!(empty.encoded().is_empty());
    assert_eq!(
        (
            empty.significance_propagation().bytes(),
            empty.significance_propagation().offset(),
            empty.significance_propagation().direction()
        ),
        (&[][..], 4, HtStreamDirection::Forward)
    );
    assert_eq!(
        (
            empty.magnitude_refinement().bytes(),
            empty.magnitude_refinement().offset(),
            empty.magnitude_refinement().direction()
        ),
        (&[][..], 4, HtStreamDirection::Reverse)
    );
}

#[test]
fn ht_partition_checks_actual_budget_before_scup_and_sizes_before_budget() {
    let limits = ResourceLimits::default()
        .with_maximum_code_block_bytes(1)
        .unwrap();
    assert_eq!(
        parse_ht_block_segments(&[0, 0], None, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlockBytes,
            limit: 1,
            actual: 2,
        })
    );
    assert_eq!(
        parse_ht_block_segments(&[0], None, &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock,
        })
    );
    assert_eq!(
        parse_ht_block_segments(&[2, 0], Some(&[0; 2047]), &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock
        })
    );
    let exact = ResourceLimits::default()
        .with_maximum_code_block_bytes(2)
        .unwrap();
    assert!(parse_ht_block_segments(&[2, 0], Some(&[]), &exact).is_ok());
    assert_eq!(
        parse_ht_block_segments(&[0, 0], None, &exact),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock
        })
    );
}

#[test]
fn ht_partition_native_capacity_and_scup_boundaries_are_exact() {
    let limits = ResourceLimits::default();
    let mut cleanup = vec![0; 65534];
    cleanup[65532] = 2;
    let refinement = [0; 2046];
    let segments = parse_ht_block_segments(&cleanup, Some(&refinement), &limits).unwrap();
    assert_eq!(
        (
            segments.bytes(),
            segments.cleanup().scup(),
            segments.cleanup().mag_sgn().bytes().len(),
            segments.cleanup().vlc().offset()
        ),
        (67580, 2, 65532, 65532)
    );
    assert_eq!(
        parse_ht_block_segments(&[0; 65535], None, &limits),
        Err(invalid_code_block())
    );
    assert_eq!(
        parse_ht_block_segments(&[3, 0], None, &limits),
        Err(invalid_code_block())
    );
    let mut maximum_scup = vec![0; 4079];
    maximum_scup[4077] = 0x0f;
    maximum_scup[4078] = 0xfe;
    let segment = parse_ht_block_segments(&maximum_scup, None, &limits)
        .unwrap()
        .cleanup();
    assert_eq!(
        (
            segment.scup(),
            segment.mag_sgn().bytes().len(),
            segment.mel().bytes().len(),
            segment.vlc().bytes().len()
        ),
        (4079, 0, 4078, 4079)
    );
    let mut excessive_scup = vec![0; 4080];
    excessive_scup[4079] = 0xff;
    assert_eq!(
        parse_ht_block_segments(&excessive_scup, None, &limits),
        Err(invalid_code_block())
    );
}

#[test]
fn ht_packet_pass_group_has_literal_complete_fields_and_native_rejections() {
    for (passes, cleanup, refinement, placeholders, skipped) in [
        (1, 1, 0, 0, 0),
        (2, 1, 1, 0, 0),
        (3, 1, 2, 0, 0),
        (4, 4, 0, 3, 1),
        (5, 4, 1, 3, 1),
        (6, 4, 2, 3, 1),
        (162, 160, 2, 159, 53),
        (163, 163, 0, 162, 54),
        (164, 163, 1, 162, 54),
    ] {
        assert_eq!(
            HtPassGroup::from_packet_passes(passes),
            Ok(HtPassGroup {
                cleanup_passes: cleanup,
                refinement_passes: refinement,
                placeholder_passes: placeholders,
                skipped_bitplanes: skipped,
            })
        );
    }
    for passes in [0, 165, 255] {
        assert_eq!(
            HtPassGroup::from_packet_passes(passes),
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodeBlock,
            })
        );
    }
}

#[test]
fn ht_uvlc_prefixes_and_suffixes_use_exact_physical_bits() {
    for (bytes, expected, bits, cursor) in [
        ([0x10, 0], (1, 0, 1), 1, 5),
        ([0x20, 0], (2, 0, 2), 2, 6),
        ([0x40, 0], (3, 1, 3), 3, 7),
        ([0x00, 0], (5, 5, 3), 3, 7),
    ] {
        let mut readers = ht_cleanup_readers_from_inputs(&[0], &bytes, 100).unwrap();
        let mel = readers.mel;
        assert_eq!(readers.read_prefix(), Ok(expected));
        assert_eq!(
            (
                readers.vlc.bits_read,
                readers.vlc.next_bit,
                readers.work_units
            ),
            (bits, cursor, bits)
        );
        assert_eq!(readers.mel, mel);
    }
    let mut value = ht_cleanup_readers_from_inputs(&[0, 0], &[0x0b, 0, 0], 100).unwrap();
    assert_eq!(value.prefix_value(), Ok((27, 3)));
    assert_eq!(
        (
            value.vlc.current_byte,
            value.vlc.value,
            value.vlc.next_bit,
            value.vlc.bits_read,
            value.work_units
        ),
        (0, 0x0b, 4, 8, 8)
    );

    let mut zero_extended = ht_cleanup_readers_from_inputs(&[0; 41], &[0; 42], 1000).unwrap();
    assert_eq!(zero_extended.read_suffix(255), Ok(0));
    assert_eq!(
        (
            zero_extended.vlc.current_byte,
            zero_extended.vlc.next_bit,
            zero_extended.vlc.bits_read,
            zero_extended.work_units
        ),
        (8, 3, 255, 255)
    );
}

#[test]
fn ht_uvlc_result_width_and_budget_rejections_keep_the_consumed_bit() {
    let mut width = ht_cleanup_readers_from_inputs(&[0, 0], &[0x10, 0, 0], 100).unwrap();
    let mel = width.mel;
    assert_eq!(
        width.read_suffix(9),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock,
        })
    );
    assert_eq!(
        (
            width.vlc.current_byte,
            width.vlc.next_bit,
            width.vlc.bits_read,
            width.vlc_last_byte,
            width.work_units
        ),
        (0, 5, 9, Some(0), 9)
    );
    assert_eq!(width.mel, mel);
    let mut budget = ht_cleanup_readers_from_inputs(&[0, 0], &[0x10, 0, 0], 8).unwrap();
    assert_eq!(
        budget.read_suffix(9),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 8,
            actual: 9,
        })
    );
    assert_eq!(
        (budget.vlc.next_bit, budget.vlc.bits_read, budget.work_units),
        (5, 9, 8)
    );

    let mut prefix = ht_cleanup_readers_from_inputs(&[0], &[0x40, 0], 2).unwrap();
    assert_eq!(
        prefix.read_prefix(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 2,
            actual: 3,
        })
    );
    assert_eq!(
        (prefix.vlc.next_bit, prefix.vlc.bits_read, prefix.work_units),
        (7, 3, 2)
    );
}

#[test]
fn ht_uvlc_initial_and_noninitial_modes_have_literal_pair_results() {
    for (mode, initial_expected, noninitial_expected, bits) in [
        (0, [1, 1], [1, 1], 0),
        (1, [2, 1], [2, 1], 1),
        (2, [1, 2], [1, 2], 1),
        (3, [2, 2], [2, 2], 2),
    ] {
        let mut initial = ht_cleanup_readers_from_inputs(&[0], &[0x30, 0], 100).unwrap();
        let mut noninitial = ht_cleanup_readers_from_inputs(&[0], &[0x30, 0], 100).unwrap();
        assert_eq!(initial.decode_initial_u(mode), Ok(initial_expected));
        assert_eq!(
            noninitial.decode_non_initial_u(mode),
            Ok(noninitial_expected)
        );
        assert_eq!((initial.vlc.bits_read, initial.work_units), (bits, bits));
        assert_eq!(
            (noninitial.vlc.bits_read, noninitial.work_units),
            (bits, bits)
        );
    }
    let mut biased = ht_cleanup_readers_from_inputs(&[0], &[0x30, 0], 100).unwrap();
    assert_eq!(biased.decode_initial_u(4), Ok([4, 4]));
    assert_eq!((biased.vlc.bits_read, biased.work_units), (2, 2));
    let mut special = ht_cleanup_readers_from_inputs(&[0, 0], &[0, 0xc0, 0], 100).unwrap();
    let mut ordinary = ht_cleanup_readers_from_inputs(&[0, 0], &[0, 0xc0, 0], 100).unwrap();
    assert_eq!(special.decode_initial_u(3), Ok([4, 3]));
    assert_eq!(ordinary.decode_non_initial_u(3), Ok([4, 2]));
    assert_eq!(
        (
            special.vlc.bits_read,
            special.work_units,
            ordinary.vlc.bits_read,
            ordinary.work_units
        ),
        (5, 5, 5, 5)
    );
    let mut long = ht_cleanup_readers_from_inputs(&[0, 0], &[0x1f, 0, 0], 100).unwrap();
    assert_eq!(long.decode_initial_u(3), Ok([37, 2]));
    assert_eq!((long.vlc.bits_read, long.work_units), (9, 9));
}

#[test]
fn ht_uvlc_invalid_modes_are_unchanged_and_byte_conversion_is_checked() {
    for mode in [5, 255] {
        let mut readers = ht_cleanup_readers_from_inputs(&[0], &[0x30, 0], 0).unwrap();
        let mel = readers.mel;
        let vlc = readers.vlc;
        assert_eq!(readers.decode_initial_u(mode), Err(invalid_code_block()));
        assert_eq!(readers.mel, mel);
        assert_eq!(readers.vlc, vlc);
        assert_eq!(
            (
                readers.mel_last_byte,
                readers.vlc_last_byte,
                readers.work_units
            ),
            (None, None, 0)
        );
    }
    let mut readers = ht_cleanup_readers_from_inputs(&[0], &[0x30, 0], 0).unwrap();
    let vlc = readers.vlc;
    assert_eq!(readers.decode_non_initial_u(4), Err(invalid_code_block()));
    assert_eq!(readers.vlc, vlc);
    for base in [0, 1, 5, 255] {
        for suffix in [0, 31, 254, 255] {
            for bias in [0, 1, 3, 255] {
                let wide = u16::from(base) + u16::from(suffix) + u16::from(bias);
                let expected = if wide <= 255 {
                    Ok(wide as u8)
                } else {
                    Err(DecodeError::MalformedInput {
                        offset: 0,
                        kind: MalformedKind::ArithmeticOverflow,
                    })
                };
                assert_eq!(ht_uvlc_byte(base, suffix, bias), expected);
            }
        }
    }
}

#[test]
fn ht_quad_word_context_suppression_and_charge_order_are_exact() {
    let mut word = ht_cleanup_readers_from_inputs(&[0], &[0, 0], 100).unwrap();
    let mel = word.mel;
    assert_eq!(word.decode_quad_word(true, 1), Ok(0x0002));
    assert_eq!(word.mel, mel);
    assert_eq!(
        (word.vlc.next_bit, word.vlc.bits_read, word.work_units),
        (6, 2, 3)
    );

    let mut suppressed = ht_cleanup_readers_from_inputs(&[0], &[0, 0], 0).unwrap();
    suppressed.mel_zero_events = 1;
    suppressed.mel_state = 255;
    let mel = suppressed.mel;
    let vlc = suppressed.vlc;
    assert_eq!(
        suppressed.decode_quad_word(true, 0),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 0,
            actual: 1,
        })
    );
    assert_eq!(suppressed.mel, mel);
    assert_eq!(suppressed.vlc, vlc);
    assert_eq!(
        (
            suppressed.mel_zero_events,
            suppressed.mel_state,
            suppressed.mel_events,
            suppressed.work_units
        ),
        (0, 255, 1, 1)
    );

    let mut final_charge = ht_cleanup_readers_from_inputs(&[0], &[0, 0], 2).unwrap();
    assert_eq!(
        final_charge.decode_quad_word(true, 1),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 2,
            actual: 3,
        })
    );
    assert_eq!(
        (
            final_charge.vlc.next_bit,
            final_charge.vlc.bits_read,
            final_charge.work_units
        ),
        (6, 2, 3)
    );
    let mut invalid = ht_cleanup_readers_from_inputs(&[0], &[0, 0], 100).unwrap();
    let mel = invalid.mel;
    let vlc = invalid.vlc;
    assert_eq!(
        invalid.decode_quad_word(false, 255),
        Err(invalid_code_block())
    );
    assert_eq!(invalid.mel, mel);
    assert_eq!(invalid.vlc, vlc);
    assert_eq!((invalid.mel_events, invalid.work_units), (0, 0));
}

#[test]
fn ht_cleanup_vlc_words_peek_without_mutation_and_advance_to_first_error() {
    let mut readers = ht_cleanup_readers_from_inputs(&[0, 0], &[0x7f, 0x90, 0], 100).unwrap();
    let mel = readers.mel;
    let vlc = readers.vlc;
    for (count, expected) in [(0, 0), (4, 9), (11, 0x7f9), (255, 0x7f9)] {
        assert_eq!(readers.peek_vlc(count), expected);
    }
    assert_eq!(readers.mel, mel);
    assert_eq!(readers.vlc, vlc);
    assert_eq!(
        (
            readers.mel_last_byte,
            readers.vlc_last_byte,
            readers.work_units,
            readers.mel_events
        ),
        (None, None, 0, 0)
    );
    assert_eq!(readers.advance_vlc(0), Ok(()));
    assert_eq!(readers.vlc, vlc);
    assert_eq!(readers.advance_vlc(4), Ok(()));
    assert_eq!(
        (
            readers.vlc.current_byte,
            readers.vlc.next_bit,
            readers.vlc.last_bit,
            readers.vlc.bits_read,
            readers.vlc_last_byte,
            readers.work_units
        ),
        (0, 0, 6, 4, Some(1), 4)
    );
    assert_eq!(readers.advance_vlc(8), Err(invalid_code_block()));
    assert_eq!(
        (
            readers.vlc.current_byte,
            readers.vlc.next_bit,
            readers.vlc.has_byte,
            readers.vlc.bits_read,
            readers.vlc_last_byte,
            readers.work_units
        ),
        (0, 7, false, 11, Some(0), 11)
    );

    let capacity = ht_cleanup_readers_from_inputs(&[0, 0, 0], &[0xff, 0xff, 0, 0], 100).unwrap();
    assert_eq!(capacity.peek_vlc(16), 0xfff0);
    assert_eq!(capacity.peek_vlc(255), 0xfff0);
    assert_eq!(capacity.vlc.bits_read, 0);
    let budget = ht_cleanup_readers_from_inputs(&[0, 0], &[0x7f, 0x90, 0], 3).unwrap();
    assert_eq!(budget.peek_vlc(255), 1);
    assert_eq!(
        (
            budget.vlc.bits_read,
            budget.work_units,
            budget.vlc_last_byte
        ),
        (0, 0, None)
    );
}

#[test]
fn ht_cleanup_mel_events_have_exact_run_suffix_and_cache_transitions() {
    let mut run = ht_cleanup_readers_from_inputs(&[0xff, 0], &[0, 0, 0], 100).unwrap();
    for _ in 0..5 {
        assert_eq!(run.mel_event(), Ok(false));
    }
    assert_eq!(
        (
            run.mel_state,
            run.mel_zero_events,
            run.mel_terminating_one,
            run.mel_events,
            run.mel.next_bit,
            run.mel.bits_read,
            run.work_units
        ),
        (4, 0, false, 5, 3, 4, 4)
    );

    let mut suffix = ht_cleanup_readers_from_inputs(&[0x40, 0], &[0, 0, 0], 100).unwrap();
    suffix.mel_state = 3;
    assert_eq!(suffix.mel_event(), Ok(false));
    assert_eq!(
        (
            suffix.mel_state,
            suffix.mel_zero_events,
            suffix.mel_terminating_one,
            suffix.mel_events,
            suffix.mel.next_bit,
            suffix.mel.bits_read,
            suffix.work_units
        ),
        (2, 0, true, 1, 5, 2, 2)
    );
    assert_eq!(suffix.mel_event(), Ok(true));
    assert_eq!(
        (
            suffix.mel_state,
            suffix.mel_zero_events,
            suffix.mel_terminating_one,
            suffix.mel_events,
            suffix.mel.next_bit,
            suffix.mel.bits_read,
            suffix.work_units
        ),
        (2, 0, false, 2, 5, 2, 2)
    );

    let mut maximum = ht_cleanup_readers_from_inputs(&[0x54, 0], &[0, 0, 0], 100).unwrap();
    maximum.mel_state = 12;
    assert_eq!(maximum.mel_event(), Ok(false));
    assert_eq!(
        (
            maximum.mel_state,
            maximum.mel_zero_events,
            maximum.mel_terminating_one,
            maximum.mel_events,
            maximum.mel.next_bit,
            maximum.mel.bits_read,
            maximum.work_units
        ),
        (11, 20, true, 1, 1, 6, 6)
    );
    for _ in 0..20 {
        assert_eq!(maximum.mel_event(), Ok(false));
    }
    assert_eq!(maximum.mel_event(), Ok(true));
    assert_eq!(
        (
            maximum.mel_zero_events,
            maximum.mel_terminating_one,
            maximum.mel_events,
            maximum.mel.bits_read,
            maximum.work_units
        ),
        (0, false, 22, 6, 6)
    );
}

#[test]
fn ht_cleanup_mel_event_overflow_and_partial_suffix_failure_keep_actual_state() {
    let mut cached = ht_cleanup_readers_from_inputs(&[0x40, 0], &[0, 0, 0], 100).unwrap();
    cached.mel_state = 255;
    cached.mel_zero_events = 2;
    cached.mel_events = u32::MAX;
    let mel = cached.mel;
    let vlc = cached.vlc;
    assert_eq!(cached.mel_event(), Err(arithmetic_overflow()));
    assert_eq!(
        (
            cached.mel_state,
            cached.mel_zero_events,
            cached.mel_terminating_one,
            cached.mel_events,
            cached.work_units
        ),
        (255, 1, false, u32::MAX, 0)
    );
    assert_eq!(cached.mel, mel);
    assert_eq!(cached.vlc, vlc);
    cached.mel_zero_events = 0;
    cached.mel_terminating_one = true;
    assert_eq!(cached.mel_event(), Err(arithmetic_overflow()));
    assert!(!cached.mel_terminating_one);
    assert_eq!(cached.mel_event(), Err(invalid_code_block()));
    assert_eq!(cached.mel, mel);
    assert_eq!(cached.vlc, vlc);

    let mut suffix = ht_cleanup_readers_from_inputs(&[0x40, 0], &[0, 0, 0], 1).unwrap();
    suffix.mel_state = 3;
    suffix.mel_events = u32::MAX;
    let vlc = suffix.vlc;
    assert_eq!(
        suffix.mel_event(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2,
        })
    );
    assert_eq!(
        (
            suffix.mel_state,
            suffix.mel_zero_events,
            suffix.mel_terminating_one,
            suffix.mel_events,
            suffix.mel.next_bit,
            suffix.mel.bits_read,
            suffix.work_units,
            suffix.mel_last_byte
        ),
        (3, 0, false, u32::MAX, 5, 2, 1, Some(0))
    );
    assert_eq!(suffix.vlc, vlc);
}

#[test]
fn ht_cleanup_pair_collision_precedes_bit_and_outer_budget_follows_claim() {
    let mut readers = ht_cleanup_readers_from_inputs(&[0x21, 0], &[0x7f, 0x90, 0], 20).unwrap();
    readers.mel_last_byte = Some(1);
    let before_mel = readers.mel;
    let before_vlc = readers.vlc;
    assert_eq!(readers.read_vlc_bit(), Err(invalid_code_block()));
    assert_eq!(readers.mel, before_mel);
    assert_eq!(readers.vlc, before_vlc);
    assert_eq!(
        (
            readers.mel_last_byte,
            readers.vlc_last_byte,
            readers.terminal_byte,
            readers.work_units,
            readers.maximum_work_units,
            readers.mel_state,
            readers.mel_zero_events,
            readers.mel_terminating_one,
            readers.mel_events
        ),
        (Some(1), None, 1, 0, 20, 0, 0, false, 0),
    );

    let mut readers = ht_cleanup_readers_from_inputs(&[0x21, 0], &[0x7f, 0x90, 0], 1).unwrap();
    readers.work_units = 1;
    let before_mel = readers.mel;
    assert_eq!(
        readers.read_vlc_bit(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2,
        })
    );
    assert_eq!(readers.mel, before_mel);
    assert_eq!(
        (
            readers.vlc.current_byte,
            readers.vlc.value,
            readers.vlc.next_bit,
            readers.vlc.last_bit,
            readers.vlc.has_byte,
            readers.vlc.later_byte_requires_unstuffing,
            readers.vlc.bits_read,
            readers.vlc.maximum_work_units
        ),
        (1, 0x90, 5, 7, true, true, 1, 1),
    );
    assert_eq!(
        (
            readers.mel_last_byte,
            readers.vlc_last_byte,
            readers.terminal_byte,
            readers.work_units,
            readers.maximum_work_units,
            readers.mel_state,
            readers.mel_zero_events,
            readers.mel_terminating_one,
            readers.mel_events
        ),
        (None, Some(1), 1, 2, 1, 0, 0, false, 0),
    );
}

#[test]
fn ht_cleanup_pair_inner_failure_preserves_claims_and_outer_counter() {
    let mut readers = ht_cleanup_readers_from_inputs(&[0xff, 0x90], &[0x7f, 0x90, 0], 20).unwrap();
    for _ in 0..8 {
        assert_eq!(readers.read_mel_bit(), Ok(true));
    }
    let before_mel = readers.mel;
    let before_vlc = readers.vlc;
    assert_eq!(
        readers.read_mel_bit(),
        Err(DecodeError::MalformedInput {
            offset: 1,
            kind: MalformedKind::InvalidBitStuffing,
        })
    );
    assert_eq!(readers.mel, before_mel);
    assert_eq!(readers.vlc, before_vlc);
    assert_eq!(
        (
            readers.mel_last_byte,
            readers.vlc_last_byte,
            readers.terminal_byte,
            readers.work_units,
            readers.maximum_work_units,
            readers.mel_state,
            readers.mel_zero_events,
            readers.mel_terminating_one,
            readers.mel_events
        ),
        (Some(0), None, 1, 8, 20, 0, 0, false, 0),
    );

    let mut readers = ht_cleanup_readers_from_inputs(&[0x21, 0], &[0x7f, 0x90, 0], 1).unwrap();
    assert_eq!(readers.read_vlc_bit(), Ok(true));
    assert_eq!(
        readers.read_vlc_bit(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2,
        })
    );
    assert_eq!(
        (
            readers.vlc.next_bit,
            readers.vlc.bits_read,
            readers.vlc_last_byte,
            readers.work_units
        ),
        (6, 2, Some(1), 1)
    );
}

#[test]
fn ht_reverse_vlc_fixed_stream_has_exact_terminal_and_stuffed_cursors() {
    let mut reader =
        HtReverseVlcReader::new(&[0x7f, 0x90, 0x00], &ResourceLimits::default()).unwrap();
    for (index, expected) in [
        true, false, false, true, true, true, true, true, true, true, true,
    ]
    .into_iter()
    .enumerate()
    {
        assert_eq!(reader.read_bit(), Ok(expected));
        assert_eq!(reader.bits_read(), index as u64 + 1);
        if index == 3 {
            assert_eq!(
                (
                    reader.current_byte,
                    reader.value,
                    reader.next_bit,
                    reader.last_bit,
                    reader.has_byte,
                    reader.later_byte_requires_unstuffing
                ),
                (0, 0x7f, 0, 6, true, false),
            );
        }
    }
    assert_eq!(
        (
            reader.current_byte,
            reader.value,
            reader.next_bit,
            reader.last_bit,
            reader.has_byte,
            reader.later_byte_requires_unstuffing,
            reader.bits_read,
            reader.maximum_work_units
        ),
        (0, 0x7f, 7, 6, false, false, 11, 1_000_000_000),
    );
    let exhausted = reader;
    assert_eq!(reader.next_position(), None);
    assert_eq!(reader.read_bit(), Err(invalid_code_block()));
    assert_eq!(reader, exhausted);

    let mut terminal = HtReverseVlcReader::new(&[0x70, 0], &ResourceLimits::default()).unwrap();
    assert_eq!(terminal.last_bit, 6);
    assert_eq!(terminal.read_bit(), Ok(true));
    assert_eq!(terminal.read_bit(), Ok(true));
    assert_eq!(terminal.read_bit(), Ok(true));
    assert_eq!(
        (terminal.next_bit, terminal.has_byte, terminal.bits_read),
        (7, false, 3)
    );
}

#[test]
fn ht_reverse_vlc_first_budget_error_does_not_eagerly_load() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(3)
        .unwrap();
    let mut reader = HtReverseVlcReader::new(&[0x7f, 0x90, 0], &limits).unwrap();
    assert_eq!(reader.read_bit(), Ok(true));
    assert_eq!(reader.read_bit(), Ok(false));
    assert_eq!(reader.read_bit(), Ok(false));
    assert_eq!(
        reader.read_bit(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 3,
            actual: 4,
        })
    );
    assert_eq!(
        (
            reader.current_byte,
            reader.value,
            reader.next_bit,
            reader.last_bit,
            reader.has_byte,
            reader.later_byte_requires_unstuffing,
            reader.bits_read,
            reader.maximum_work_units
        ),
        (1, 0x90, 8, 7, true, true, 4, 3),
    );
    assert_eq!(
        reader.next_position(),
        Some(HtBitPosition { byte: 1, bit: 8 })
    );
    let failed = reader;
    assert_eq!(reader.read_bit(), Err(invalid_code_block()));
    assert_eq!(reader, failed);
}

#[test]
fn ht_cleanup_reader_overflow_keeps_the_exact_partial_cursor_update() {
    let limits = ResourceLimits::default();
    let mut reverse = HtReverseVlcReader::new(&[0x90, 0], &limits).unwrap();
    reverse.bits_read = u64::MAX;
    let mut expected = reverse;
    expected.next_bit = 5;
    assert_eq!(reverse.read_bit(), Err(arithmetic_overflow()));
    assert_eq!(reverse, expected);

    let mut mel = HtMelBitReader::new(&[0x20], &limits).unwrap();
    mel.bits_read = u64::MAX;
    let mut expected = mel;
    expected.next_bit = 6;
    assert_eq!(mel.read_bit(), Err(arithmetic_overflow()));
    assert_eq!(mel, expected);
}

#[test]
fn ht_mel_fixed_stream_covers_terminal_nibble_stuffing_and_exhaustion() {
    let limits = ResourceLimits::default();
    let mut reader = HtMelBitReader::new(&[0x21], &limits).unwrap();
    for expected in [false, false, true, false, true, true, true, true] {
        assert_eq!(reader.read_bit(), Ok(expected));
    }
    assert_eq!(
        (
            reader.next_byte,
            reader.current_byte,
            reader.value,
            reader.next_bit,
            reader.previous_was_ff,
            reader.bits_read,
            reader.maximum_work_units
        ),
        (1, 0, 0x2f, -1, false, 8, 1_000_000_000),
    );
    let exhausted = reader;
    assert_eq!(reader.next_position(), None);
    assert_eq!(reader.read_bit(), Err(invalid_code_block()));
    assert_eq!(reader, exhausted);

    let mut stuffed = HtMelBitReader::new(&[0xff, 0x80], &limits).unwrap();
    for expected in [
        true, true, true, true, true, true, true, true, false, false, false, true, true, true, true,
    ] {
        assert_eq!(stuffed.read_bit(), Ok(expected));
    }
    assert_eq!(
        (
            stuffed.next_byte,
            stuffed.current_byte,
            stuffed.value,
            stuffed.next_bit,
            stuffed.previous_was_ff,
            stuffed.bits_read
        ),
        (2, 1, 0x8f, -1, false, 15),
    );
}

#[test]
fn ht_mel_first_stuffing_and_budget_errors_preserve_full_state() {
    let mut malformed = HtMelBitReader::new(&[0xff, 0x90], &ResourceLimits::default()).unwrap();
    for _ in 0..8 {
        assert_eq!(malformed.read_bit(), Ok(true));
    }
    let failed = malformed;
    assert_eq!(
        malformed.read_bit(),
        Err(DecodeError::MalformedInput {
            offset: 1,
            kind: MalformedKind::InvalidBitStuffing,
        })
    );
    assert_eq!(malformed, failed);

    let limits = ResourceLimits::default()
        .with_maximum_work_units(1)
        .unwrap();
    let mut reader = HtMelBitReader::new(&[0x21], &limits).unwrap();
    assert_eq!(reader.read_bit(), Ok(false));
    assert_eq!(
        reader.read_bit(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2,
        })
    );
    assert_eq!(
        (
            reader.next_byte,
            reader.current_byte,
            reader.value,
            reader.next_bit,
            reader.previous_was_ff,
            reader.bits_read,
            reader.maximum_work_units
        ),
        (1, 0, 0x2f, 5, false, 2, 1),
    );
}

#[test]
fn ht_cleanup_reader_length_boundaries_are_typed() {
    let limits = ResourceLimits::default();
    for length in [0, 1, 4080] {
        assert_eq!(
            HtReverseVlcReader::new(&vec![0; length], &limits),
            Err(invalid_code_block()),
        );
    }
    for length in [0, 4079] {
        assert_eq!(
            HtMelBitReader::new(&vec![0; length], &limits),
            Err(invalid_code_block())
        );
    }
    assert!(HtReverseVlcReader::new(&vec![0; 4079], &limits).is_ok());
    assert!(HtMelBitReader::new(&vec![0; 4078], &limits).is_ok());
}

#[test]
fn ht_readers_apply_directional_stuffing_and_reject_bad_mel_sequences() {
    let limits = ResourceLimits::default();
    let mut mel = HtMelBitReader::new(&[0xff, 0x8f], &limits).unwrap();
    for _ in 0..8 {
        let _ = mel.read_bit().unwrap();
    }
    let _ = mel.read_bit().unwrap();
    assert_eq!(mel.next_position().unwrap().bit, 5);
    let mut malformed = HtMelBitReader::new(&[0xff, 0x90], &limits).unwrap();
    for _ in 0..8 {
        assert!(malformed.read_bit().unwrap());
    }
    assert!(malformed.read_bit().is_err());

    let mut reverse = HtReverseVlcReader::new(&[0x7f, 0x90, 0x00], &limits).unwrap();
    for _ in 0..4 {
        let _ = reverse.read_bit().unwrap();
    }
    assert_eq!(
        reverse.next_position(),
        Some(HtBitPosition { byte: 0, bit: 0 })
    );
    for _ in 0..7 {
        let _ = reverse.read_bit().unwrap();
    }
    assert_eq!(reverse.bits_read(), 11);
    assert!(reverse.next_position().is_none());
}

#[test]
fn ht_magsgn_words_have_exact_fill_and_physical_state() {
    let limits = ResourceLimits::default();
    let mut empty = HtForwardMagSgnReader::new(&[], &limits).unwrap();
    let initial = empty;
    assert_eq!(empty.read_bits(0), Ok(0));
    assert_eq!(empty, initial);
    assert_eq!(empty.read_bits(40), Err(invalid_code_block()));
    assert_eq!(empty, initial);
    assert_eq!(empty.read_bits(39), Ok(0x7f_ffff_ffff));
    assert_eq!(
        (
            empty.next_byte,
            empty.value,
            empty.next_bit,
            empty.last_bit,
            empty.has_byte,
            empty.current_is_physical,
            empty.previous_was_ff,
            empty.physical_bits_read,
            empty.fill_bits_read,
            empty.work_units
        ),
        (0, 0xff, 3, 6, true, false, true, 0, 39, 39),
    );
    let filled = empty;
    assert_eq!(empty.finish(), Ok(()));
    assert_eq!(empty, filled);

    let mut physical = HtForwardMagSgnReader::new(&[0xff, 0x7f], &limits).unwrap();
    assert_eq!(physical.read_bits(20), Ok(0x0f_ffff));
    assert_eq!(
        (
            physical.next_byte,
            physical.value,
            physical.next_bit,
            physical.last_bit,
            physical.has_byte,
            physical.current_is_physical,
            physical.previous_was_ff,
            physical.physical_bits_read,
            physical.fill_bits_read,
            physical.work_units
        ),
        (2, 0xff, 5, 7, true, false, true, 15, 5, 20),
    );
    assert!(matches!(
        HtForwardMagSgnReader::new(&vec![0; 65535], &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock
        })
    ));
    assert!(HtForwardMagSgnReader::new(&vec![0; 65534], &limits).is_ok());
}

#[test]
fn ht_magsgn_word_and_finish_fail_at_the_first_actual_bit() {
    let limits = ResourceLimits::default();
    let mut stuffed = HtForwardMagSgnReader::new(&[0xff, 0x80], &limits).unwrap();
    assert_eq!(
        stuffed.read_bits(9),
        Err(DecodeError::MalformedInput {
            offset: 1,
            kind: MalformedKind::InvalidBitStuffing,
        })
    );
    assert_eq!(
        (
            stuffed.next_byte,
            stuffed.value,
            stuffed.next_bit,
            stuffed.last_bit,
            stuffed.current_is_physical,
            stuffed.physical_bits_read,
            stuffed.fill_bits_read,
            stuffed.work_units
        ),
        (1, 0xff, 8, 7, true, 8, 0, 8),
    );
    let failed = stuffed;
    assert_eq!(
        stuffed.finish(),
        Err(DecodeError::MalformedInput {
            offset: 1,
            kind: MalformedKind::InvalidBitStuffing,
        })
    );
    assert_eq!(stuffed, failed);

    let mut padding = HtForwardMagSgnReader::new(&[0xfe], &limits).unwrap();
    assert_eq!(padding.finish(), Err(invalid_code_block()));
    assert_eq!(
        (
            padding.next_byte,
            padding.value,
            padding.next_bit,
            padding.last_bit,
            padding.physical_bits_read,
            padding.fill_bits_read,
            padding.work_units
        ),
        (1, 0xfe, 1, 7, 1, 0, 1),
    );
    assert_eq!(padding.finish(), Ok(()));
    assert_eq!(
        (
            padding.next_bit,
            padding.physical_bits_read,
            padding.work_units
        ),
        (8, 8, 8)
    );

    let limits = limits.with_maximum_work_units(1).unwrap();
    let mut budget = HtForwardMagSgnReader::new(&[0xff], &limits).unwrap();
    assert_eq!(
        budget.finish(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2,
        })
    );
    assert_eq!(
        (
            budget.next_bit,
            budget.physical_bits_read,
            budget.work_units
        ),
        (2, 2, 2)
    );
}

#[test]
fn ht_magsgn_overflow_keeps_each_ordered_partial_update() {
    let limits = ResourceLimits::default();
    let mut physical = HtForwardMagSgnReader::new(&[0xff], &limits).unwrap();
    assert_eq!(physical.read_bits(1), Ok(1));
    physical.physical_bits_read = u64::MAX;
    let mut expected = physical;
    expected.next_bit = 2;
    assert_eq!(physical.read_bits(1), Err(arithmetic_overflow()));
    assert_eq!(physical, expected);

    let mut work = HtForwardMagSgnReader::new(&[0xff], &limits).unwrap();
    assert_eq!(work.read_bits(1), Ok(1));
    work.work_units = u64::MAX;
    let mut expected = work;
    expected.next_bit = 2;
    expected.physical_bits_read = 2;
    assert_eq!(work.read_bits(1), Err(arithmetic_overflow()));
    assert_eq!(work, expected);

    let mut fill = HtForwardMagSgnReader::new(&[], &limits).unwrap();
    assert_eq!(fill.read_bits(1), Ok(1));
    fill.fill_bits_read = u64::MAX;
    let mut expected = fill;
    expected.next_bit = 2;
    assert_eq!(fill.read_bits(1), Err(arithmetic_overflow()));
    assert_eq!(fill, expected);

    let mut zero_fuel = HtForwardMagSgnReader::new(&[], &limits).unwrap();
    zero_fuel.has_byte = true;
    zero_fuel.current_is_physical = true;
    let expected = zero_fuel;
    assert_eq!(zero_fuel.finish(), Err(invalid_code_block()));
    assert_eq!(zero_fuel, expected);
}

#[test]
fn ht_magsgn_reader_is_bounded_stuffed_and_termination_checked() {
    let limits = ResourceLimits::default();
    let mut reader = HtForwardMagSgnReader::new(&[0xff, 0x7f], &limits).unwrap();
    assert_eq!(reader.read_bits(15).unwrap(), 0x7fff);
    assert_eq!(reader.physical_bits_read(), 15);
    assert_eq!(reader.fill_bits_read(), 0);
    assert_eq!(reader.read_bits(3).unwrap(), 7);
    assert_eq!(reader.fill_bits_read(), 3);
    reader.finish().unwrap();

    let mut bad_stuffing = HtForwardMagSgnReader::new(&[0xff, 0x80], &limits).unwrap();
    assert_eq!(bad_stuffing.read_bits(8).unwrap(), 0xff);
    assert!(matches!(
        bad_stuffing.read_bits(1),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBitStuffing,
            ..
        })
    ));

    let mut bad_termination = HtForwardMagSgnReader::new(&[0xfc], &limits).unwrap();
    assert_eq!(bad_termination.read_bits(1).unwrap(), 0);
    assert!(bad_termination.finish().is_err());
}

#[test]
fn ht_refinement_fixed_bytes_return_exact_directional_positions_and_fill() {
    let limits = ResourceLimits::default();
    let mut forward = HtForwardRefinementReader::new(&[0xff, 0x7f], &limits).unwrap();
    for (byte, bit) in [
        (0, 0),
        (0, 1),
        (0, 2),
        (0, 3),
        (0, 4),
        (0, 5),
        (0, 6),
        (0, 7),
        (1, 0),
        (1, 1),
        (1, 2),
        (1, 3),
        (1, 4),
        (1, 5),
        (1, 6),
    ] {
        assert_eq!(
            forward.read_positioned_bit(),
            Ok((true, Some(HtBitPosition { byte, bit })))
        );
    }
    assert_eq!(forward.read_positioned_bit(), Ok((false, None)));
    assert_eq!(
        (
            forward.next_byte,
            forward.current_byte,
            forward.value,
            forward.next_bit,
            forward.last_bit,
            forward.has_byte,
            forward.previous_was_ff,
            forward.physical_bits_read,
            forward.fill_bits_read
        ),
        (2, 2, 0, 1, 7, true, false, 15, 1),
    );

    let mut reverse = HtReverseRefinementReader::new(&[0x7f, 0x90], &limits).unwrap();
    for (value, byte, bit) in [
        (false, 1, 0),
        (false, 1, 1),
        (false, 1, 2),
        (false, 1, 3),
        (true, 1, 4),
        (false, 1, 5),
        (false, 1, 6),
        (true, 1, 7),
        (true, 0, 0),
        (true, 0, 1),
        (true, 0, 2),
        (true, 0, 3),
        (true, 0, 4),
        (true, 0, 5),
        (true, 0, 6),
    ] {
        assert_eq!(
            reverse.read_positioned_bit(),
            Ok((value, Some(HtBitPosition { byte, bit })))
        );
    }
    assert_eq!(reverse.read_positioned_bit(), Ok((false, None)));
    assert_eq!(
        (
            reverse.current_byte,
            reverse.value,
            reverse.next_bit,
            reverse.last_bit,
            reverse.has_byte,
            reverse.later_requires_unstuffing,
            reverse.physical_bits_read,
            reverse.fill_bits_read
        ),
        (0, 0, 0, 7, false, false, 15, 1),
    );
}

#[test]
fn ht_refinement_counter_and_sum_overflow_preserve_ordered_cursor_updates() {
    let limits = ResourceLimits::default();
    let mut forward = HtForwardRefinementReader::new(&[0xff], &limits).unwrap();
    assert!(forward.read_bit().unwrap());
    forward.fill_bits_read = u64::MAX;
    let mut expected = forward;
    expected.next_bit = 2;
    expected.physical_bits_read = 2;
    assert_eq!(forward.read_positioned_bit(), Err(arithmetic_overflow()));
    assert_eq!(forward, expected);
    forward.physical_bits_read = u64::MAX;
    let mut expected = forward;
    expected.next_bit = 3;
    assert_eq!(forward.read_bit(), Err(arithmetic_overflow()));
    assert_eq!(forward, expected);

    let mut reverse = HtReverseRefinementReader::new(&[0xff], &limits).unwrap();
    assert!(reverse.read_bit().unwrap());
    reverse.fill_bits_read = u64::MAX;
    let mut expected = reverse;
    expected.next_bit = 2;
    expected.physical_bits_read = 2;
    assert_eq!(reverse.read_positioned_bit(), Err(arithmetic_overflow()));
    assert_eq!(reverse, expected);
    reverse.physical_bits_read = u64::MAX;
    let mut expected = reverse;
    expected.next_bit = 3;
    assert_eq!(reverse.read_bit(), Err(arithmetic_overflow()));
    assert_eq!(reverse, expected);

    let mut forward_fill = HtForwardRefinementReader::new(&[], &limits).unwrap();
    assert!(!forward_fill.read_bit().unwrap());
    forward_fill.fill_bits_read = u64::MAX;
    let mut expected = forward_fill;
    expected.next_bit = 2;
    assert_eq!(forward_fill.read_bit(), Err(arithmetic_overflow()));
    assert_eq!(forward_fill, expected);
    let mut reverse_fill = HtReverseRefinementReader::new(&[], &limits).unwrap();
    reverse_fill.fill_bits_read = u64::MAX;
    let expected = reverse_fill;
    assert_eq!(reverse_fill.read_bit(), Err(arithmetic_overflow()));
    assert_eq!(reverse_fill, expected);
}

#[test]
fn ht_refinement_budget_boundaries_and_constructor_capacities_are_exact() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(1)
        .unwrap();
    let mut forward = HtForwardRefinementReader::new(&[0x03], &limits).unwrap();
    let mut reverse = HtReverseRefinementReader::new(&[0x03], &limits).unwrap();
    assert_eq!(forward.read_bit(), Ok(true));
    assert_eq!(reverse.read_bit(), Ok(true));
    let mut expected_forward = forward;
    expected_forward.next_bit = 2;
    expected_forward.physical_bits_read = 2;
    let mut expected_reverse = reverse;
    expected_reverse.next_bit = 2;
    expected_reverse.physical_bits_read = 2;
    let error = DecodeError::LimitExceeded {
        resource: Resource::WorkUnits,
        limit: 1,
        actual: 2,
    };
    assert_eq!(forward.read_bit(), Err(error));
    assert_eq!(reverse.read_bit(), Err(error));
    assert_eq!(forward, expected_forward);
    assert_eq!(reverse, expected_reverse);
    assert_eq!(
        HtForwardRefinementReader::new(&vec![0; 2047], &limits),
        Err(invalid_code_block())
    );
    assert_eq!(
        HtReverseRefinementReader::new(&vec![0; 2047], &limits),
        Err(invalid_code_block())
    );
    assert!(HtForwardRefinementReader::new(&vec![0; 2046], &limits).is_ok());
    assert!(HtReverseRefinementReader::new(&vec![0; 2046], &limits).is_ok());
}

#[test]
fn ht_refinement_collision_retains_consumption_and_reverse_stuffed_mask() {
    let mut readers = ht_refinement_readers_from_inputs(&[0xff], &[0xff], 1, true, 100).unwrap();
    assert_eq!(readers.read_forward(), Ok(true));
    let forward = readers.forward;
    assert_eq!(readers.read_reverse(), Err(invalid_code_block()));
    assert_eq!(readers.forward, forward);
    let reverse = readers.reverse.unwrap();
    assert_eq!(
        (
            reverse.current_byte,
            reverse.value,
            reverse.next_bit,
            reverse.last_bit,
            reverse.has_byte,
            reverse.later_requires_unstuffing,
            reverse.physical_bits_read,
            reverse.fill_bits_read
        ),
        (0, 0xff, 1, 6, true, true, 1, 0),
    );
    assert_eq!(
        (readers.claimed.as_slice(), readers.stuffed.as_slice()),
        (&[1][..], &[0x80][..])
    );
    assert_eq!(readers.finish(&[0xff]), Err(invalid_code_block()));
    for _ in 0..6 {
        assert_eq!(readers.read_reverse(), Ok(true));
    }
    assert_eq!(
        (readers.claimed.as_slice(), readers.stuffed.as_slice()),
        (&[0x7f][..], &[0x80][..])
    );
    assert_eq!(readers.finish(&[0xff]), Ok(()));
    assert_eq!(readers.read_forward(), Err(invalid_code_block()));
    assert_eq!(
        (readers.forward.next_bit, readers.forward.physical_bits_read),
        (2, 2)
    );
    assert_eq!(
        (readers.claimed.as_slice(), readers.stuffed.as_slice()),
        (&[0x7f][..], &[0x80][..])
    );
}

#[test]
fn ht_refinement_missing_claim_storage_and_reverse_absence_have_exact_effects() {
    let mut readers = ht_refinement_readers_from_inputs(&[1], &[], 0, false, 100).unwrap();
    let forward = readers.forward;
    assert_eq!(readers.read_reverse(), Err(invalid_code_block()));
    assert_eq!(readers.forward, forward);
    assert!(readers.reverse.is_none());
    assert_eq!(readers.read_forward(), Err(invalid_code_block()));
    assert_eq!(
        (readers.forward.next_bit, readers.forward.physical_bits_read),
        (1, 1)
    );
    assert!(readers.claimed.is_empty() && readers.stuffed.is_empty());
    assert_eq!(readers.claim(None), Ok(()));
    assert_eq!(
        readers.claim(Some(HtBitPosition { byte: 0, bit: 8 })),
        Err(invalid_code_block())
    );
    assert_eq!(readers.finish(&[]), Ok(()));
    assert_eq!(readers.finish(&[0]), Err(invalid_code_block()));

    let mut short = ht_refinement_readers_from_inputs(&[], &[0xff], 1, true, 100).unwrap();
    short.stuffed.clear();
    let forward = short.forward;
    assert_eq!(short.read_reverse(), Err(invalid_code_block()));
    assert_eq!(short.forward, forward);
    let reverse = short.reverse.unwrap();
    assert_eq!((reverse.next_bit, reverse.physical_bits_read), (1, 1));
    assert_eq!(short.claimed, [0]);
    assert!(short.stuffed.is_empty());
}

#[test]
fn ht_refinement_readers_are_stuffed_bounded_and_collision_checked() {
    let limits = ResourceLimits::default();
    let mut forward = HtForwardRefinementReader::new(&[0xff, 0x7f], &limits).unwrap();
    for _ in 0..15 {
        assert!(forward.read_bit().unwrap());
    }
    assert_eq!(forward.physical_bits_read(), 15);
    assert!(!forward.read_bit().unwrap());
    assert_eq!(forward.fill_bits_read(), 1);

    let mut malformed = HtForwardRefinementReader::new(&[0xff, 0x80], &limits).unwrap();
    for _ in 0..8 {
        let _ = malformed.read_bit().unwrap();
    }
    assert!(matches!(
        malformed.read_bit(),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBitStuffing,
            ..
        })
    ));

    let segment = HtRefinementSegment {
        encoded: &[1],
        significance_propagation: HtSubstreamView {
            bytes: &[1],
            offset: 0,
            direction: HtStreamDirection::Forward,
        },
        magnitude_refinement: HtSubstreamView {
            bytes: &[1],
            offset: 0,
            direction: HtStreamDirection::Reverse,
        },
    };
    let mut readers = ht_refinement_readers_from_inputs(
        segment.significance_propagation().bytes(),
        segment.magnitude_refinement().bytes(),
        segment.encoded().len(),
        true,
        limits.maximum_work_units(),
    )
    .unwrap();
    assert!(readers.read_forward().unwrap());
    assert!(readers.read_reverse().is_err());
}

#[test]
fn ht_refinement_applies_new_signs_and_magnitude_bits_transactionally() {
    let limits = ResourceLimits::default();
    let mut cleanup = CodeBlockPlane::new(2, 1).unwrap();
    cleanup.mark_significant(0, 0, 3, false).unwrap();

    let spp_bytes = [0x01];
    let spp = HtRefinementSegment {
        encoded: &spp_bytes,
        significance_propagation: HtSubstreamView {
            bytes: &spp_bytes,
            offset: 0,
            direction: HtStreamDirection::Forward,
        },
        magnitude_refinement: HtSubstreamView {
            bytes: &spp_bytes,
            offset: 0,
            direction: HtStreamDirection::Reverse,
        },
    };
    let (spp_plane, statistics) =
        decode_ht_refinement_plane(&cleanup, spp, 1, 2, false, &limits).unwrap();
    assert_eq!(statistics.newly_significant, 1);
    assert_eq!(spp_plane.signed_coefficient(1, 0).unwrap(), 1);

    let both_bytes = [0x01, 0x01];
    let both = HtRefinementSegment {
        encoded: &both_bytes,
        significance_propagation: HtSubstreamView {
            bytes: &both_bytes,
            offset: 0,
            direction: HtStreamDirection::Forward,
        },
        magnitude_refinement: HtSubstreamView {
            bytes: &both_bytes,
            offset: 0,
            direction: HtStreamDirection::Reverse,
        },
    };
    let (both_plane, statistics) =
        decode_ht_refinement_plane(&cleanup, both, 2, 2, false, &limits).unwrap();
    assert_eq!(statistics.refined_coefficients, 1);
    assert_eq!(statistics.newly_significant, 1);
    assert_eq!(both_plane.signed_coefficient(0, 0).unwrap(), 3);
    assert_eq!(both_plane.signed_coefficient(1, 0).unwrap(), 1);

    let bad_bytes = [0xff];
    let bad = HtRefinementSegment {
        encoded: &bad_bytes,
        significance_propagation: HtSubstreamView {
            bytes: &bad_bytes,
            offset: 0,
            direction: HtStreamDirection::Forward,
        },
        magnitude_refinement: HtSubstreamView {
            bytes: &bad_bytes,
            offset: 0,
            direction: HtStreamDirection::Reverse,
        },
    };
    assert!(decode_ht_refinement_plane(&cleanup, bad, 2, 2, false, &limits).is_err());
    assert_eq!(cleanup.signed_coefficient(0, 0).unwrap(), 3);
    assert_eq!(cleanup.signed_coefficient(1, 0).unwrap(), 0);
}

#[test]
fn completes_non_initial_ht_kappa_from_north_exponents() {
    assert_eq!(complete_ht_kappa(2, 0x1, 7, 3, 8).unwrap(), 2);
    assert_eq!(complete_ht_kappa(2, 0x3, 7, 3, 8).unwrap(), 7);
    assert!(complete_ht_kappa(2, 0x3, 9, 3, 8).is_err());
    assert!(complete_ht_kappa(0, 0x3, 1, 1, 8).is_err());
}

#[test]
fn reconstructs_positive_ht_cleanup_magnitude_from_physical_bits() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut decoder = Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
    let decoded = decoder
        .decode_high_throughput_segments(&[0xfe, 0x00, 0x63, 0x00], 1, None, 0, &limits)
        .unwrap();
    assert_eq!(decoded.statistics.coefficients_scanned, 1);
    assert_eq!(decoded.statistics.coding_symbols, 1);
    assert_eq!(decoded.statistics.newly_significant, 1);
    assert_eq!(decoder.plane().signed_coefficient(0, 0).unwrap(), 1);
    assert!(decoder.is_complete());
    assert_eq!(decoder.decoded_segments(), 1);
    assert_eq!(decoder.decoded_bytes(), 4);
}

#[test]
fn ht_embedded_zero_bit_still_reduces_payload_precision() {
    let mut reader = HtForwardMagSgnReader::new(&[0x04], &ResourceLimits::default()).unwrap();
    let (magnitude, negative, exponent) =
        reconstruct_ht_magnitude(&mut reader, 3, true, false, 1).unwrap();
    assert_eq!(magnitude.to_u64(), Some(1));
    assert!(!negative);
    assert_eq!(exponent, 1);
    assert_eq!(reader.physical_bits_read(), 2);
}

#[test]
fn reconstructs_capability_b74_magnitude_without_narrowing() {
    let mut bytes = [0_u8; 10];
    bytes[9] = 0x04;
    let mut reader = HtForwardMagSgnReader::new(&bytes, &ResourceLimits::default()).unwrap();
    let (magnitude, negative, exponent) =
        reconstruct_ht_magnitude(&mut reader, 75, false, false, 1).unwrap();
    assert!(!negative);
    assert_eq!(exponent, 75);
    assert_eq!(magnitude.low_u64(), 1);
    assert_eq!(magnitude.limb(1), Some(512));
    assert_eq!(magnitude.to_u64(), None);
    assert_eq!(reader.physical_bits_read(), 75);
    assert!(complete_ht_kappa(1, 1, 0, 0, 76).is_err());
    assert!(reconstruct_ht_magnitude(&mut reader, 76, false, false, 1).is_err());
    let mut decoder =
        Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, Tier1CodingStyle::default())
            .unwrap();
    assert!(decoder.set_ht_magnitude_bound(75).is_err());
}

#[test]
fn ht_noninitial_context_uses_the_northern_boundary_stencil() {
    assert_eq!(crate::refinement::ht_noninitial_vlc_context(2, 0, 0, 0), 2);
    assert_eq!(crate::refinement::ht_noninitial_vlc_context(0, 8, 0, 0), 1);
    assert_eq!(crate::refinement::ht_noninitial_vlc_context(0, 0, 2, 0), 1);
    assert_eq!(crate::refinement::ht_noninitial_vlc_context(0, 0, 8, 0), 4);
    assert_eq!(crate::refinement::ht_noninitial_vlc_context(0, 0, 0, 2), 4);
    assert_eq!(
        crate::refinement::ht_noninitial_vlc_context(2, 15, 15, 15),
        7
    );
    assert_eq!(crate::refinement::ht_noninitial_vlc_context(0, 0, 5, 0), 0);
}

#[test]
fn ht_cleanup_context_preserves_both_northern_columns() {
    let metadata = decode_ht_cleanup_metadata(
        &[0x00, 0x00, 0xd5, 0xb4, 0x00],
        2,
        4,
        8,
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(metadata.significant_samples, 8, "{metadata:?}");
    assert_eq!(metadata.quads[0].significance, 15);
    assert_eq!(metadata.quads[1].context, 5);
    assert_eq!(metadata.quads[1].significance, 15);
}

#[test]
fn ht_cleanup_accepts_fused_mel_vlc_final_byte() {
    let metadata = decode_ht_cleanup_metadata(
        &[0xf0, 0x0c, 0xe3, 0x00],
        4,
        1,
        8,
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(metadata.quads.len(), 2);
    assert_eq!(metadata.quads[0].significance, 5);
    assert_eq!(metadata.quads[1].significance, 5);
}

#[test]
fn ht_cleanup_fusion_does_not_cross_bytes() {
    let limits = ResourceLimits::default();
    let segments = parse_ht_block_segments(&[0x00, 0x00, 0x04, 0x00], None, &limits).unwrap();
    let mut readers = ht_cleanup_readers_from_inputs(
        segments.cleanup().mel().bytes(),
        segments.cleanup().vlc().bytes(),
        limits.maximum_work_units(),
    )
    .unwrap();
    for _ in 0..4 {
        readers.read_vlc_bit().unwrap();
    }
    for _ in 0..8 {
        readers.read_mel_bit().unwrap();
    }
    for _ in 0..8 {
        readers.read_vlc_bit().unwrap();
    }
    for _ in 0..8 {
        readers.read_mel_bit().unwrap();
    }
    readers.finish().unwrap();
    assert!(readers.read_mel_bit().is_err());
    assert!(readers.read_vlc_bit().is_err());
}

#[test]
fn ht_cleanup_fusion_excludes_ff() {
    let limits = ResourceLimits::default();
    let segments = parse_ht_block_segments(&[0x00, 0xff, 0x04, 0x00], None, &limits).unwrap();
    let mut readers = ht_cleanup_readers_from_inputs(
        segments.cleanup().mel().bytes(),
        segments.cleanup().vlc().bytes(),
        limits.maximum_work_units(),
    )
    .unwrap();
    for _ in 0..4 {
        readers.read_vlc_bit().unwrap();
    }
    for _ in 0..8 {
        readers.read_mel_bit().unwrap();
    }
    readers.read_vlc_bit().unwrap();
    assert!(readers.read_mel_bit().is_err());
}

#[test]
fn legacy_partial_quality_reconstructs_signed_midpoints_without_changing_prefixes() {
    for negative in [false, true] {
        let mut plane = CodeBlockPlane::new(1, 1).unwrap();
        plane
            .mark_significant_at_bitplane(0, 0, 4, negative)
            .unwrap();
        assert_eq!(plane.coefficient(0, 0).unwrap().magnitude, 16);
        let sign = if negative { -1 } else { 1 };
        assert_eq!(plane.signed_coefficient(0, 0).unwrap(), sign * 24);
        for (bitplane, bit, expected) in
            [(3, false, 20), (2, true, 22), (1, true, 23), (0, true, 23)]
        {
            plane.apply_refinement_bit(0, 0, bitplane, bit).unwrap();
            assert_eq!(plane.signed_coefficient(0, 0).unwrap(), sign * expected);
        }
        assert_eq!(plane.coefficient(0, 0).unwrap().magnitude, 23);
    }
}

#[test]
fn zero_byte_mq_continuation_replays_the_buffered_prefix() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(1).unwrap();
    let mut whole = Tier1CodeBlockDecoder::new(1, 1, 4, SubbandOrientation::Ll, style).unwrap();
    let mut split = Tier1CodeBlockDecoder::new(1, 1, 4, SubbandOrientation::Ll, style).unwrap();
    whole.decode_legacy_contribution(&[0], 10, &limits).unwrap();
    split.decode_legacy_contribution(&[0], 9, &limits).unwrap();
    assert!(split.legacy_segment.is_some());
    split.decode_legacy_contribution(&[], 1, &limits).unwrap();
    assert_eq!(split.plane(), whole.plane());
    assert_eq!(split.next_pass(), whole.next_pass());
    assert_eq!(split.decoded_bytes(), whole.decoded_bytes());
    assert!(split.legacy_segment.is_none());
    let mut empty = Tier1CodeBlockDecoder::new(1, 1, 4, SubbandOrientation::Ll, style).unwrap();
    assert!(empty.decode_legacy_contribution(&[], 1, &limits).is_err());
}

#[test]
fn legacy_input_extension_refusal_preserves_pending_prefix_and_retries_once() {
    let limits = ResourceLimits::default();
    for prefix in [vec![0], vec![0; 9]] {
        let mut decoder = Tier1CodeBlockDecoder::new(
            1,
            1,
            4,
            SubbandOrientation::Ll,
            Tier1CodingStyle::default(),
        )
        .unwrap();
        decoder
            .decode_legacy_contribution(&prefix, 1, &limits)
            .unwrap();
        let pending = decoder.legacy_segment.as_ref().unwrap();
        let incoming = vec![0; pending.input.capacity() + 1];
        let before_pending = format!("{pending:?}");
        let before_plane = decoder.plane().clone();
        let before_pass = decoder.next_pass();
        let before_bytes = decoder.decoded_bytes();
        let mut expected = decoder.clone();
        expected
            .decode_legacy_contribution(&incoming, 1, &limits)
            .unwrap();

        assert_eq!(
            crate::allocation::with_refusal(0, || {
                decoder.decode_legacy_contribution(&incoming, 1, &limits)
            }),
            Err(DecodeError::AllocationFailed),
        );
        assert_eq!(
            format!("{:?}", decoder.legacy_segment.as_ref().unwrap()),
            before_pending,
        );
        assert_eq!(decoder.plane(), &before_plane);
        assert_eq!(decoder.next_pass(), before_pass);
        assert_eq!(decoder.decoded_bytes(), before_bytes);

        decoder
            .decode_legacy_contribution(&incoming, 1, &limits)
            .unwrap();
        assert_eq!(decoder.plane(), expected.plane());
        assert_eq!(decoder.next_pass(), expected.next_pass());
        assert_eq!(decoder.decoded_bytes(), expected.decoded_bytes());
        assert_eq!(
            format!("{:?}", decoder.legacy_segment),
            format!("{:?}", expected.legacy_segment),
        );
        assert!(decoder.legacy_decode_work > expected.legacy_decode_work);
    }
}

#[test]
fn legacy_partial_pass_midpoints_are_coefficient_local() {
    let mut plane = CodeBlockPlane::new(2, 1).unwrap();
    plane.mark_significant_at_bitplane(0, 0, 3, false).unwrap();
    plane.mark_significant_at_bitplane(1, 0, 2, false).unwrap();
    assert_eq!(plane.signed_coefficient(0, 0).unwrap(), 12);
    assert_eq!(plane.signed_coefficient(1, 0).unwrap(), 6);
    plane.apply_refinement_bit(0, 0, 2, false).unwrap();
    assert_eq!(plane.signed_coefficient(0, 0).unwrap(), 10);
    assert_eq!(plane.signed_coefficient(1, 0).unwrap(), 6);
}

#[test]
fn legacy_midpoint_reconstruction_preserves_wide_magnitudes() {
    for (bitplane, low, high) in [(64, 1_u64 << 63, 1), (65, 0, 3), (74, 0, 1536)] {
        let mut plane = CodeBlockPlane::new(1, 1).unwrap();
        plane
            .mark_significant_at_bitplane(0, 0, bitplane, false)
            .unwrap();
        let reconstructed = plane.coefficient(0, 0).unwrap().signed_magnitude().unwrap();
        assert_eq!(reconstructed.magnitude.limb(0), Some(low));
        assert_eq!(reconstructed.magnitude.limb(1), Some(high));
    }
}

#[test]
fn ht_cleanup_rejects_cursor_collision_and_out_of_bounds_significance() {
    let limits = ResourceLimits::default();
    assert!(decode_ht_cleanup_metadata(&[0x02, 0x00], 1, 1, 1, &limits).is_err());
    assert!(decode_ht_cleanup_metadata(&[0x00, 0x03, 0x00], 1, 1, 1, &limits).is_err());
    let work_limited = limits.with_maximum_work_units(4).unwrap();
    assert!(matches!(
        decode_ht_cleanup_metadata(&[0x00, 0x63, 0x00], 1, 1, 1, &work_limited),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            ..
        })
    ));
}

#[test]
fn rejects_invalid_ht_cleanup_termination_and_limits() {
    let limits = ResourceLimits::default();
    assert!(parse_ht_block_segments(&[0x01], None, &limits).is_err());
    assert!(parse_ht_block_segments(&[0x01, 0x00], None, &limits).is_err());
    assert!(parse_ht_block_segments(&[0xff, 0xff], None, &limits).is_err());
    let byte_limited = limits.with_maximum_code_block_bytes(2).unwrap();
    assert!(matches!(
        parse_ht_block_segments(&[0x02, 0x00], Some(&[0]), &byte_limited),
        Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlockBytes,
            limit: 2,
            actual: 3,
        })
    ));

    let ht = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut pass_limited_decoder =
        Tier1CodeBlockDecoder::new(1, 1, 2, SubbandOrientation::Ll, ht).unwrap();
    let pass_limited = limits.with_maximum_code_block_passes(1).unwrap();
    assert!(matches!(
        pass_limited_decoder.decode_high_throughput_segments(
            &[0x02, 0x00],
            1,
            Some(&[]),
            1,
            &pass_limited,
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlockPasses,
            ..
        })
    ));
    let mut work_limited_decoder =
        Tier1CodeBlockDecoder::new(2, 2, 1, SubbandOrientation::Ll, ht).unwrap();
    let work_limited = limits.with_maximum_work_units(1).unwrap();
    assert!(matches!(
        work_limited_decoder.decode_high_throughput_segments(
            &[0x02, 0x00],
            1,
            None,
            0,
            &work_limited,
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            ..
        })
    ));
}

#[test]
fn segment_accounting_is_failure_atomic() {
    let mut accounting = CodeBlockSegmentAccounting::new(4, &ResourceLimits::default()).unwrap();
    assert_eq!(
        accounting.add_segment(1, 5).unwrap(),
        Tier1PassKind::Cleanup
    );
    assert_eq!(
        accounting.add_segment(2, 7).unwrap(),
        Tier1PassKind::SignificancePropagation
    );
    let previous = accounting;
    assert!(accounting.add_segment(2, 1).is_err());
    assert_eq!(accounting, previous);
    assert_eq!(accounting.total_passes(), 3);
    assert_eq!(accounting.total_bytes(), 12);
    assert_eq!(accounting.segments(), 2);
}

#[test]
fn coefficient_state_and_neighbor_access_are_bounded() {
    let mut plane = CodeBlockPlane::new(3, 3).unwrap();
    plane.mark_significant(0, 1, 8, false).unwrap();
    plane.mark_significant(1, 0, 8, true).unwrap();
    plane.mark_significant(2, 2, 8, false).unwrap();
    let summary = plane.neighbor_summary(1, 1).unwrap();
    assert_eq!(summary.horizontal_significant, 1);
    assert_eq!(summary.vertical_significant, 1);
    assert_eq!(summary.diagonal_significant, 1);
    assert_eq!(summary.horizontal_sign_balance, 1);
    assert_eq!(summary.vertical_sign_balance, -1);

    plane.refine(0, 1, 4).unwrap();
    assert_eq!(plane.coefficient(0, 1).unwrap().magnitude, 12);
    assert!(plane.coefficient(0, 1).unwrap().refined);
    assert!(plane.coefficient(3, 0).is_err());
}

#[test]
fn neighbor_summaries_match_all_local_sign_states_and_stripe_boundaries() {
    let mut patterns_checked = 0;
    for (width, height, x, y) in [
        (1_u16, 1_u16, 0_u16, 0_u16),
        (1, 5, 0, 3),
        (5, 1, 3, 0),
        (3, 5, 0, 0),
        (3, 5, 2, 4),
        (3, 5, 0, 3),
        (3, 5, 2, 3),
        (3, 5, 1, 2),
        (3, 5, 1, 3),
    ] {
        let mut neighbors = Vec::new();
        for dy in -1..=1 {
            for dx in -1..=1 {
                if dx == 0 && dy == 0 {
                    continue;
                }
                let nx = i32::from(x) + dx;
                let ny = i32::from(y) + dy;
                if (0..i32::from(width)).contains(&nx) && (0..i32::from(height)).contains(&ny) {
                    neighbors.push((
                        u16::try_from(nx).unwrap(),
                        u16::try_from(ny).unwrap(),
                        dx,
                        dy,
                    ));
                }
            }
        }
        let patterns = 3_u32.pow(u32::try_from(neighbors.len()).unwrap());
        for pattern in 0..patterns {
            patterns_checked += 1;
            let mut plane = CodeBlockPlane::new(width, height).unwrap();
            let mut remaining = pattern;
            let mut full = NeighborSummary::default();
            let mut causal = NeighborSummary::default();
            for &(nx, ny, dx, dy) in &neighbors {
                let state = remaining % 3;
                remaining /= 3;
                if state == 0 {
                    continue;
                }
                let negative = state == 2;
                plane.mark_significant(nx, ny, 1, negative).unwrap();
                for (vertical_causal, summary) in [(false, &mut full), (true, &mut causal)] {
                    if vertical_causal && y % 4 == 3 && dy == 1 {
                        continue;
                    }
                    let sign = if negative { -1 } else { 1 };
                    if dy == 0 {
                        summary.horizontal_significant += 1;
                        summary.horizontal_sign_balance += sign;
                    } else if dx == 0 {
                        summary.vertical_significant += 1;
                        summary.vertical_sign_balance += sign;
                    } else {
                        summary.diagonal_significant += 1;
                    }
                }
            }
            assert_eq!(plane.neighbor_summary(x, y).unwrap(), full);
            assert_eq!(
                plane.neighbor_summary_with_causality(x, y, true).unwrap(),
                causal,
            );
        }
    }
    assert_eq!(patterns_checked, 13_681);
}

#[test]
fn forms_tier_one_contexts_from_neighbors() {
    let summary = NeighborSummary {
        horizontal_significant: 1,
        vertical_significant: 0,
        diagonal_significant: 1,
        horizontal_sign_balance: -1,
        vertical_sign_balance: 1,
    };
    assert_eq!(zero_coding_context(summary, SubbandOrientation::Lh), 6);
    assert_eq!(zero_coding_context(summary, SubbandOrientation::Hl), 3);
    assert_eq!(zero_coding_context(summary, SubbandOrientation::Hh), 4);
    assert_eq!(
        sign_context(summary),
        SignContext {
            context: 11,
            predicted_negative: true,
        }
    );
    assert_eq!(
        magnitude_refinement_context(CoefficientState::default(), summary),
        15
    );
    assert_eq!(
        magnitude_refinement_context(
            CoefficientState {
                refined: true,
                ..CoefficientState::default()
            },
            NeighborSummary::default(),
        ),
        16
    );
}

#[test]
fn applies_significance_and_predicted_sign_atomically() {
    let mut plane = CodeBlockPlane::new(2, 1).unwrap();
    plane.mark_significant(0, 0, 8, true).unwrap();
    let step =
        apply_significance_decision(&mut plane, 1, 0, 4, SubbandOrientation::Lh, true, false)
            .unwrap();
    assert!(step.became_significant);
    assert_eq!(step.sign_context, Some(12));
    assert!(plane.coefficient(1, 0).unwrap().negative);
    let previous = plane.coefficient(1, 0).unwrap();
    assert!(
        apply_significance_decision(&mut plane, 1, 0, 2, SubbandOrientation::Lh, true, false,)
            .is_err()
    );
    assert_eq!(plane.coefficient(1, 0).unwrap(), previous);
}

#[test]
fn refinement_records_zero_decisions_without_changing_magnitude() {
    let mut plane = CodeBlockPlane::new(1, 1).unwrap();
    plane.mark_significant(0, 0, 8, false).unwrap();
    plane.apply_refinement_decision(0, 0, 4, false).unwrap();
    assert_eq!(
        plane.coefficient(0, 0).unwrap(),
        CoefficientState {
            magnitude: 8,
            magnitude_high: [0; 5],
            legacy_bitplane: None,
            negative: false,
            significant: true,
            refined: true,
        }
    );
    assert!(plane.apply_refinement_decision(0, 0, 3, true).is_err());
}

#[test]
fn tier_one_context_initialization_sets_normative_nonzero_states() {
    let limits = ResourceLimits::default();
    let baseline = MqDecoder::new(&[0], &limits).unwrap();
    let mut initialized = MqDecoder::new(&[0], &limits).unwrap();
    initialize_tier1_contexts(&mut initialized).unwrap();
    assert_ne!(
        initialized.context(0).unwrap(),
        baseline.context(0).unwrap()
    );
    assert_ne!(
        initialized.context(RUN_LENGTH_CONTEXT).unwrap(),
        baseline.context(RUN_LENGTH_CONTEXT).unwrap()
    );
    assert_ne!(
        initialized.context(UNIFORM_CONTEXT).unwrap(),
        baseline.context(UNIFORM_CONTEXT).unwrap()
    );
    assert_eq!(
        initialized.context(1).unwrap(),
        baseline.context(1).unwrap()
    );

    let expected_zero = initialized.context(0).unwrap();
    let expected_run = initialized.context(RUN_LENGTH_CONTEXT).unwrap();
    let _ = initialized.decode(0).unwrap();
    reset_tier1_contexts_after_pass(
        &mut initialized,
        Tier1CodingStyle::from_code_block_style(0x02).unwrap(),
    )
    .unwrap();
    assert_eq!(initialized.context(0).unwrap(), expected_zero);
    assert_eq!(
        initialized.context(RUN_LENGTH_CONTEXT).unwrap(),
        expected_run
    );
}

#[test]
fn vertical_causal_context_ignores_the_next_stripe() {
    let mut plane = CodeBlockPlane::new(1, 5).unwrap();
    plane.mark_significant(0, 3, 8, false).unwrap();
    plane.mark_significant(0, 4, 8, false).unwrap();
    assert_eq!(
        plane
            .neighbor_summary_with_causality(0, 3, false)
            .unwrap()
            .vertical_significant,
        1
    );
    assert_eq!(
        plane
            .neighbor_summary_with_causality(0, 3, true)
            .unwrap()
            .vertical_significant,
        0
    );
    assert_eq!(
        plane
            .neighbor_summary_with_causality(0, 2, true)
            .unwrap()
            .vertical_significant,
        1
    );
}

#[test]
fn raw_bypass_sign_bits_do_not_use_mq_sign_prediction() {
    let limits = ResourceLimits::default();
    for neighbor_negative in [false, true] {
        for negative in [false, true] {
            let mut plane = CodeBlockPlane::new(2, 1).unwrap();
            plane.mark_significant(0, 0, 8, neighbor_negative).unwrap();
            let mut state = Tier1BitplaneState::new(&plane, 4).unwrap();
            let bytes = [if negative { 0xc0 } else { 0x80 }];
            let mut reader = RawBitReader::new(&bytes, &limits).unwrap();
            decode_raw_significance_propagation_pass(
                &mut plane,
                &mut state,
                &mut reader,
                SubbandOrientation::Ll,
                Tier1CodingStyle::from_code_block_style(0x01).unwrap(),
            )
            .unwrap();
            assert_eq!(plane.coefficient(1, 0).unwrap().negative, negative);
        }
    }
}

#[test]
fn raw_bypass_decodes_significance_and_refinement_passes() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x01).unwrap();
    let mut plane = CodeBlockPlane::new(2, 1).unwrap();
    plane.mark_significant(0, 0, 8, false).unwrap();
    let mut state = Tier1BitplaneState::new(&plane, 4).unwrap();
    let mut reader = RawBitReader::new(&[0x80], &limits).unwrap();

    let significance = decode_raw_significance_propagation_pass(
        &mut plane,
        &mut state,
        &mut reader,
        SubbandOrientation::Ll,
        style,
    )
    .unwrap();
    assert_eq!(significance.coefficients_scanned, 2);
    assert_eq!(significance.coding_symbols, 2);
    assert_eq!(significance.newly_significant, 1);

    let refinement =
        decode_raw_magnitude_refinement_pass(&mut plane, &mut state, &mut reader, style).unwrap();
    assert_eq!(refinement.coefficients_scanned, 2);
    assert_eq!(refinement.coding_symbols, 1);
    assert_eq!(refinement.refined_coefficients, 1);
    assert_eq!(plane.coefficient(0, 0).unwrap().magnitude, 8);
    assert!(plane.coefficient(0, 0).unwrap().refined);
    assert_eq!(plane.coefficient(1, 0).unwrap().magnitude, 4);
    assert_eq!(reader.bytes_consumed(), 1);
}

#[test]
fn traverses_all_three_passes_and_preserves_bitplane_eligibility() {
    let limits = ResourceLimits::default();
    let mut plane = CodeBlockPlane::new(3, 2).unwrap();
    plane.mark_significant(0, 0, 8, false).unwrap();
    let mut state = Tier1BitplaneState::new(&plane, 4).unwrap();
    let mut decoder = MqDecoder::new(&[0, 0, 0, 0], &limits).unwrap();
    initialize_tier1_contexts(&mut decoder).unwrap();

    let significance = decode_significance_propagation_pass(
        &mut plane,
        &mut state,
        &mut decoder,
        SubbandOrientation::Lh,
    )
    .unwrap();
    assert_eq!(significance.coefficients_scanned, 6);
    assert!(state.significance_propagation_complete());
    assert!(
        state
            .was_visited_by_significance_propagation(&plane, 1, 0)
            .unwrap()
    );

    let refinement =
        decode_magnitude_refinement_pass(&mut plane, &mut state, &mut decoder).unwrap();
    assert_eq!(refinement.coefficients_scanned, 6);
    assert_eq!(refinement.refined_coefficients, 1);
    assert!(plane.coefficient(0, 0).unwrap().refined);
    assert!(state.magnitude_refinement_complete());

    let cleanup =
        decode_cleanup_pass(&mut plane, &mut state, &mut decoder, SubbandOrientation::Lh).unwrap();
    assert_eq!(cleanup.coefficients_scanned, 6);
    assert!(state.cleanup_complete());
    assert!(
        decode_cleanup_pass(&mut plane, &mut state, &mut decoder, SubbandOrientation::Lh,).is_err()
    );
}

#[test]
fn cleanup_uses_run_mode_only_for_complete_four_row_stripes() {
    let limits = ResourceLimits::default();
    let mut plane = CodeBlockPlane::new(1, 5).unwrap();
    let mut state = Tier1BitplaneState::new(&plane, 8).unwrap();
    let mut decoder = MqDecoder::new(&[0, 0, 0, 0], &limits).unwrap();
    initialize_tier1_contexts(&mut decoder).unwrap();

    let cleanup =
        decode_cleanup_pass(&mut plane, &mut state, &mut decoder, SubbandOrientation::Ll).unwrap();
    assert_eq!(cleanup.coefficients_scanned, 5);
    assert_eq!(cleanup.run_mode_columns, 1);
    assert!(cleanup.coding_symbols >= 2);
    assert!(state.cleanup_complete());
    assert!(
        decode_significance_propagation_pass(
            &mut plane,
            &mut state,
            &mut decoder,
            SubbandOrientation::Ll,
        )
        .is_err()
    );
}

#[test]
fn bitplane_state_rejects_invalid_masks_and_mismatched_planes() {
    let plane = CodeBlockPlane::new(2, 2).unwrap();
    assert!(Tier1BitplaneState::new(&plane, 0).is_err());
    assert!(Tier1BitplaneState::new(&plane, 3).is_err());

    let state = Tier1BitplaneState::new(&plane, 4).unwrap();
    let other_plane = CodeBlockPlane::new(1, 4).unwrap();
    assert!(
        state
            .was_visited_by_significance_propagation(&other_plane, 0, 0)
            .is_err()
    );
}

#[test]
fn cleanup_validates_segmentation_symbols() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x20).unwrap();
    let mut valid_plane = CodeBlockPlane::new(1, 1).unwrap();
    let mut valid_state = Tier1BitplaneState::new(&valid_plane, 8).unwrap();
    let mut valid_decoder = MqDecoder::new(&[0x01, 0xae], &limits).unwrap();
    initialize_tier1_contexts(&mut valid_decoder).unwrap();
    let statistics = decode_cleanup_pass_with_style(
        &mut valid_plane,
        &mut valid_state,
        &mut valid_decoder,
        SubbandOrientation::Ll,
        style,
    )
    .unwrap();
    assert!(statistics.coding_symbols >= 5);
    assert!(valid_state.cleanup_complete());

    let mut invalid_plane = CodeBlockPlane::new(1, 1).unwrap();
    let mut invalid_state = Tier1BitplaneState::new(&invalid_plane, 8).unwrap();
    let mut invalid_decoder = MqDecoder::new(&[0, 0], &limits).unwrap();
    initialize_tier1_contexts(&mut invalid_decoder).unwrap();
    assert!(
        decode_cleanup_pass_with_style(
            &mut invalid_plane,
            &mut invalid_state,
            &mut invalid_decoder,
            SubbandOrientation::Ll,
            style,
        )
        .is_err()
    );
    assert!(!invalid_state.cleanup_complete());
}

#[test]
fn reconstructs_code_block_across_mq_and_raw_segments() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x01).unwrap();
    let mut decoder = Tier1CodeBlockDecoder::new(1, 1, 5, SubbandOrientation::Ll, style).unwrap();

    let mq = decoder.decode_segment(&[0; 16], 10, &limits).unwrap();
    assert_eq!(mq.passes, 10);
    assert_eq!(decoder.next_pass(), 10);
    assert_eq!(decoder.decoded_segments(), 1);

    let raw = decoder.decode_segment(&[0], 2, &limits).unwrap();
    assert_eq!(raw.passes, 2);
    assert_eq!(decoder.next_pass(), 12);

    decoder.decode_segment(&[0; 4], 1, &limits).unwrap();
    assert!(decoder.is_complete());
    assert_eq!(decoder.maximum_passes(), 13);
    assert_eq!(decoder.decoded_segments(), 3);
    assert_eq!(decoder.decoded_bytes(), 21);
    assert_eq!(decoder.plane().coefficients().len(), 1);
    let coefficient = decoder.plane().coefficient(0, 0).unwrap();
    assert_eq!(
        decoder.plane().signed_coefficient(0, 0).unwrap(),
        if coefficient.negative {
            -(coefficient.magnitude as i64)
        } else {
            coefficient.magnitude as i64
        }
    );
    assert!(decoder.decode_segment(&[0], 1, &limits).is_err());
}

#[test]
fn supports_sample_and_roi_adjusted_coefficient_bitplanes() {
    let decoder = Tier1CodeBlockDecoder::new(
        1,
        1,
        38,
        SubbandOrientation::Ll,
        Tier1CodingStyle::default(),
    )
    .unwrap();
    assert_eq!(decoder.maximum_passes(), 112);
    assert_eq!(decoder.bitplane, 37);

    let roi_decoder = Tier1CodeBlockDecoder::new(
        1,
        1,
        292,
        SubbandOrientation::Ll,
        Tier1CodingStyle::default(),
    )
    .unwrap();
    assert_eq!(roi_decoder.maximum_passes(), 874);
    assert_eq!(roi_decoder.bitplane, 291);
    assert!(
        Tier1CodeBlockDecoder::new(
            1,
            1,
            293,
            SubbandOrientation::Ll,
            Tier1CodingStyle::default(),
        )
        .is_err()
    );

    let mut plane = CodeBlockPlane::new(1, 1).unwrap();
    plane
        .mark_significant_magnitude(0, 0, Magnitude::single_bit(291).unwrap(), false)
        .unwrap();
    assert_eq!(
        plane.coefficient(0, 0).unwrap().magnitude_limb(4),
        Some(1_u64 << 35)
    );
    plane.apply_refinement_bit(0, 0, 255, true).unwrap();
    assert_eq!(
        plane.coefficient(0, 0).unwrap().magnitude_limb(3),
        Some(1_u64 << 63)
    );
}
#[test]
fn ht_metadata_storage_quad_previous_and_fresh_first_later_rows_restore_actual_metadata() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(24)
        .unwrap();
    let bytes = [0xff, 3, 0];
    let expected = decode_ht_cleanup_metadata(&bytes, 5, 5, 1, &limits).unwrap();
    for after in [0, 1, 2, 4] {
        assert_eq!(
            crate::allocation::with_refusal(after, || decode_ht_cleanup_metadata(
                &bytes, 5, 5, 1, &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(
            decode_ht_cleanup_metadata(&bytes, 5, 5, 1, &limits).unwrap(),
            expected
        );
    }
    assert_eq!(expected.quads.len(), 9);
}

#[test]
fn ht_metadata_storage_current_row_refusal_preserves_actual_prior_rows_and_empty_skips_request() {
    let limits = ResourceLimits::default();
    let segments = parse_ht_block_segments(&[0xff, 3, 0], None, &limits).unwrap();
    let cleanup = segments.cleanup();
    let mut readers = ht_cleanup_readers_from_inputs(
        cleanup.mel().bytes(),
        cleanup.vlc().bytes(),
        limits.maximum_work_units(),
    )
    .unwrap();
    let mut quads = Vec::new();
    let mut previous = vec![0; 3];
    let mut significant = 0;
    decode_ht_metadata_row(
        &mut readers,
        &mut quads,
        &mut previous,
        &mut significant,
        3,
        0,
        5,
        5,
        1,
    )
    .unwrap();
    let observe = |r: &HtCleanupReaders<'_>| {
        format!(
            "{:?}",
            (
                r.mel,
                r.vlc,
                (
                    r.mel_last_byte,
                    r.vlc_last_byte,
                    r.terminal_byte,
                    r.mel_state,
                    r.mel_zero_events,
                    r.mel_terminating_one,
                    r.mel_events,
                    r.work_units,
                    r.maximum_work_units,
                ),
            )
        )
    };
    let before = format!(
        "{:?} {quads:?} {previous:?} {significant}",
        observe(&readers)
    );
    let owner = previous.as_ptr();
    assert_eq!(
        crate::allocation::with_refusal(0, || decode_ht_metadata_row(
            &mut readers,
            &mut quads,
            &mut previous,
            &mut significant,
            3,
            1,
            5,
            5,
            1
        )),
        Err(DecodeError::AllocationFailed)
    );
    assert_eq!(
        format!(
            "{:?} {quads:?} {previous:?} {significant}",
            observe(&readers)
        ),
        before
    );
    assert_eq!(previous.as_ptr(), owner);
    decode_ht_metadata_row(
        &mut readers,
        &mut quads,
        &mut previous,
        &mut significant,
        3,
        1,
        5,
        5,
        1,
    )
    .unwrap();
    assert_eq!(quads.len(), 6);
    let mut empty = Vec::new();
    crate::allocation::with_refusal(0, || {
        decode_ht_metadata_row(
            &mut readers,
            &mut quads,
            &mut empty,
            &mut significant,
            0,
            2,
            5,
            5,
            1,
        )
        .unwrap();
        assert!(empty.is_empty());
        assert_eq!(
            decode_ht_cleanup_metadata(&[0xff, 3, 0], 5, 5, 1, &limits),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn ht_metadata_storage_original_parse_header_reader_and_late_work_error_order() {
    let limits = ResourceLimits::default();
    let small = limits.with_maximum_code_block_bytes(2).unwrap();
    let segments = parse_ht_block_segments(&[0xff, 3, 0], None, &limits).unwrap();
    let mut empty = segments.cleanup();
    empty.mel.bytes = &[];
    crate::allocation::with_refusal(0, || {
        assert!(matches!(
            decode_ht_cleanup_metadata(&[0xff, 3, 0], 0, 0, 0, &small),
            Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlockBytes,
                ..
            })
        ));
        assert_eq!(
            decode_ht_cleanup_segment_metadata(segments.cleanup(), 0, 1, 1, &limits),
            Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock))
        );
        assert_eq!(
            decode_ht_cleanup_segment_metadata(empty, 1, 1, 1, &limits),
            Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock))
        );
        assert_eq!(
            decode_ht_cleanup_metadata(&[0xff, 3, 0], 5, 5, 1, &limits),
            Err(DecodeError::AllocationFailed)
        );
    });
    let work = limits.with_maximum_work_units(1).unwrap();
    let expected = decode_ht_cleanup_metadata(&[0xff, 3, 0], 5, 5, 1, &work);
    assert!(matches!(
        expected,
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            ..
        })
    ));
    assert_eq!(
        crate::allocation::with_refusal(0, || decode_ht_cleanup_metadata(
            &[0xff, 3, 0],
            5,
            5,
            1,
            &work
        )),
        Err(DecodeError::AllocationFailed)
    );
    assert_eq!(
        decode_ht_cleanup_metadata(&[0xff, 3, 0], 5, 5, 1, &work),
        expected
    );
}
#[test]
fn ht_refinement_scratch_storage_first_later_masks_restore_real_readers_and_stuffing() {
    let observe = |r: &HtRefinementReaders<'_>| {
        format!(
            "{:?} {:?} {:?} {:?}",
            r.forward, r.reverse, r.claimed, r.stuffed
        )
    };
    let expected = ht_refinement_readers_from_inputs(&[0xff], &[0xff], 1, true, 100).unwrap();
    let before = observe(&expected);
    for after in [0, 1] {
        assert_eq!(
            crate::allocation::with_refusal(after, || ht_refinement_readers_from_inputs(
                &[0xff],
                &[0xff],
                1,
                true,
                100
            ))
            .err(),
            Some(DecodeError::AllocationFailed)
        );
        let mut actual = ht_refinement_readers_from_inputs(&[0xff], &[0xff], 1, true, 100).unwrap();
        assert_eq!(observe(&actual), before);
        assert_eq!(actual.read_forward(), Ok(true));
        assert_eq!(actual.read_reverse(), Err(invalid_code_block()));
        assert_eq!(actual.claimed, [1]);
        assert_eq!(actual.stuffed, [0x80]);
        for _ in 0..6 {
            assert_eq!(actual.read_reverse(), Ok(true));
        }
        assert_eq!(actual.finish(&[0xff]), Ok(()));
    }
}

#[test]
fn ht_refinement_scratch_storage_raw_counts_empty_reverse_and_prior_admission_order() {
    let oversized = vec![0; MAX_HT_REFINEMENT_BYTES + 1];
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            ht_refinement_readers_from_inputs(&oversized, &oversized, 1, true, 100).err(),
            Some(invalid_code_block())
        );
        assert_eq!(
            ht_refinement_readers_from_inputs(&[], &oversized, 1, true, 100).err(),
            Some(invalid_code_block())
        );
        let empty = ht_refinement_readers_from_inputs(&[1], &oversized, 0, false, 100).unwrap();
        assert!(empty.reverse.is_none() && empty.claimed.is_empty() && empty.stuffed.is_empty());
        assert_eq!(
            ht_refinement_readers_from_inputs(&[], &[], 3, false, 100).err(),
            Some(DecodeError::AllocationFailed)
        );
    });
    for after in [0, 1] {
        assert_eq!(
            crate::allocation::with_refusal(after, || ht_refinement_readers_from_inputs(
                &[],
                &[],
                3,
                true,
                100
            ))
            .err(),
            Some(DecodeError::AllocationFailed)
        );
    }
    let actual = ht_refinement_readers_from_inputs(&[], &[], 3, true, 100).unwrap();
    assert_eq!(actual.claimed, [0, 0, 0]);
    assert_eq!(actual.stuffed, [0, 0, 0]);
    assert!(actual.reverse.is_some());
    let mut work = ht_refinement_readers_from_inputs(&[0], &[], 1, false, 0).unwrap();
    assert!(matches!(
        work.read_forward(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            ..
        })
    ));
    assert_eq!(work.forward.physical_bits_read, 1);
    assert_eq!(work.claimed, [0]);
}

#[test]
fn ht_refinement_scratch_storage_actual_replay_refusals_preserve_decoder_then_restore() {
    let limits = ResourceLimits::default();
    let mut base = retained_refinement_decoder();
    base.next_pass = 2;
    base.ht_refinement_passes = 1;
    base.ht_refinement_data = vec![1];
    let before = format!("{base:?}");
    let mut expected = base.clone();
    let result = expected
        .decode_high_throughput_refinement(&[1], 1, &limits)
        .unwrap();
    for after in [2, 3] {
        let mut actual = base.clone();
        assert_eq!(
            crate::allocation::with_refusal(after, || actual.decode_high_throughput_refinement(
                &[1],
                1,
                &limits
            )),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(format!("{actual:?}"), before);
        assert_eq!(
            actual
                .decode_high_throughput_refinement(&[1], 1, &limits)
                .unwrap(),
            result
        );
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }
}

#[test]
fn ht_cleanup_significance_storage_raw_flags_empty_first_later_refusal_and_restore() {
    let input = [
        raw_refinement_coefficient(u64::MAX, [7, 11, 13, 17, 19], true, true, true),
        raw_refinement_coefficient(0, [0; 5], false, false, false),
        raw_refinement_coefficient(31, [2, 3, 5, 7, 11], true, false, false),
    ];
    let expected = vec![true, false, true];
    crate::allocation::with_refusal(0, || {
        assert!(ht_collect_cleanup_significance(&[]).unwrap().is_empty());
        assert_eq!(
            ht_collect_cleanup_significance(&input),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(ht_collect_cleanup_significance(&input).unwrap(), expected);
    });
    crate::allocation::with_refusal(1, || {
        let prior = ht_collect_cleanup_significance(&input).unwrap();
        assert_eq!(
            ht_collect_cleanup_significance(&input),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(prior, expected);
        assert_eq!(ht_collect_cleanup_significance(&input).unwrap(), expected);
    });
    assert_eq!(
        input[0],
        raw_refinement_coefficient(u64::MAX, [7, 11, 13, 17, 19], true, true, true)
    );
}

#[test]
fn ht_cleanup_significance_storage_output_readers_admission_and_numeric_error_order() {
    let limits = ResourceLimits::default();
    let source = CodeBlockPlane {
        width: 2,
        height: 1,
        coefficients: vec![
            raw_refinement_coefficient(3, [0; 5], true, true, false),
            raw_refinement_coefficient(17, [2, 3, 5, 7, 11], false, true, true),
        ],
    };
    let before = format!("{source:?}");
    let decode = |bits, cap: &ResourceLimits| {
        decode_ht_refinement_plane(&source, refinement_segment(&[1]), 1, bits, false, cap)
    };
    let expected = decode(2, &limits).unwrap();
    for after in [0, 3] {
        assert_eq!(
            crate::allocation::with_refusal(after, || decode(2, &limits)),
            Err(DecodeError::AllocationFailed)
        );
        let restored = decode(2, &limits).unwrap();
        assert_eq!(restored.0.coefficients(), expected.0.coefficients());
        assert_eq!(restored.1, expected.1);
        assert_eq!(format!("{source:?}"), before);
    }
    let ordinary = decode(MAX_TIER1_BITPLANES + 1, &limits).unwrap_err();
    assert_eq!(ordinary, invalid_code_block());
    assert_eq!(
        crate::allocation::with_refusal(3, || decode(MAX_TIER1_BITPLANES + 1, &limits)),
        Err(DecodeError::AllocationFailed)
    );
    assert_eq!(
        decode(MAX_TIER1_BITPLANES + 1, &limits).unwrap_err(),
        ordinary
    );
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            decode_ht_refinement_plane(&source, refinement_segment(&[1]), 0, 2, false, &limits),
            Err(invalid_code_block())
        );
        assert_eq!(
            crate::allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
    let zero_work = limits.with_maximum_work_units(0).unwrap();
    let work_error = decode(2, &zero_work).unwrap_err();
    assert_eq!(
        crate::allocation::with_refusal(3, || decode(2, &zero_work)),
        Err(DecodeError::AllocationFailed)
    );
    assert_eq!(decode(2, &zero_work).unwrap_err(), work_error);
    let oversized = vec![0; MAX_HT_REFINEMENT_BYTES + 1];
    let rejected_reader = || {
        decode_ht_refinement_plane(
            &source,
            refinement_segment(&oversized),
            1,
            2,
            false,
            &limits,
        )
    };
    let reader_error = rejected_reader().unwrap_err();
    crate::allocation::with_refusal(1, || {
        assert_eq!(rejected_reader().unwrap_err(), reader_error);
        assert_eq!(
            crate::allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn ht_cleanup_significance_storage_actual_replay_prior_decoder_and_exact_restore() {
    let limits = ResourceLimits::default();
    let mut source = retained_refinement_decoder();
    source.next_pass = 2;
    source.ht_refinement_passes = 1;
    source.ht_refinement_data = vec![1];
    let before = format!("{source:?}");
    let mut expected = source.clone();
    let result = expected
        .decode_high_throughput_refinement(&[1], 1, &limits)
        .unwrap();
    let mut actual = source.clone();
    assert_eq!(
        crate::allocation::with_refusal(4, || actual.decode_high_throughput_refinement(
            &[1],
            1,
            &limits
        )),
        Err(DecodeError::AllocationFailed)
    );
    assert_eq!(format!("{actual:?}"), before);
    assert_eq!(
        actual
            .decode_high_throughput_refinement(&[1], 1, &limits)
            .unwrap(),
        result
    );
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
}
