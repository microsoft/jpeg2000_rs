use super::*;
use crate::{TypedSamples, allocation};

// Independently encoded with OpenJPEG 2.5.0: 1x1 gray0 PGM, -n 1 -r 2,1.
const GRAY0: &[u8] = &[
    0xff, 0x4f, 0xff, 0x51, 0x00, 0x29, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x07, 0x01, 0x01, 0xff, 0x52, 0x00,
    0x0c, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x04, 0x04, 0x00, 0x01, 0xff, 0x5c, 0x00, 0x04, 0x40,
    0x40, 0xff, 0x64, 0x00, 0x25, 0x00, 0x01, 0x43, 0x72, 0x65, 0x61, 0x74, 0x65, 0x64, 0x20, 0x62,
    0x79, 0x20, 0x4f, 0x70, 0x65, 0x6e, 0x4a, 0x50, 0x45, 0x47, 0x20, 0x76, 0x65, 0x72, 0x73, 0x69,
    0x6f, 0x6e, 0x20, 0x32, 0x2e, 0x35, 0x2e, 0x30, 0xff, 0x90, 0x00, 0x0a, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x13, 0x00, 0x01, 0xff, 0x93, 0xdf, 0x78, 0x08, 0x07, 0xc0, 0xff, 0xd9,
];

// 2x2 PGM [0,64,128,255], same encoder plus -d 5,7 -T 5,7 -SOP -EPH.
const OFFSET: &[u8] = &[
    0xff, 0x4f, 0xff, 0x51, 0x00, 0x29, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x09,
    0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x02,
    0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x07, 0x00, 0x01, 0x07, 0x01, 0x01, 0xff, 0x52, 0x00,
    0x0c, 0x06, 0x00, 0x00, 0x02, 0x00, 0x00, 0x04, 0x04, 0x00, 0x01, 0xff, 0x5c, 0x00, 0x04, 0x40,
    0x40, 0xff, 0x64, 0x00, 0x25, 0x00, 0x01, 0x43, 0x72, 0x65, 0x61, 0x74, 0x65, 0x64, 0x20, 0x62,
    0x79, 0x20, 0x4f, 0x70, 0x65, 0x6e, 0x4a, 0x50, 0x45, 0x47, 0x20, 0x76, 0x65, 0x72, 0x73, 0x69,
    0x6f, 0x6e, 0x20, 0x32, 0x2e, 0x35, 0x2e, 0x30, 0xff, 0x90, 0x00, 0x0a, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x28, 0x00, 0x01, 0xff, 0x93, 0xff, 0x91, 0x00, 0x04, 0x00, 0x00, 0xdf, 0x78, 0x30, 0xff,
    0x92, 0x07, 0xa3, 0x75, 0x1b, 0x50, 0x7f, 0xff, 0x91, 0x00, 0x04, 0x00, 0x01, 0xc0, 0xff, 0x92,
    0xff, 0xd9,
];

const SOT: usize = 104;
const BODY: usize = SOT + 14;

fn damaged(original: &[u8]) -> Vec<u8> {
    assert_eq!(&original[SOT..SOT + 2], &[0xff, 0x90]);
    assert_eq!(&original[original.len() - 2..], &[0xff, 0xd9]);
    let mut bytes = original[..original.len() - 2].to_vec();
    bytes[SOT + 6..SOT + 10].fill(0);
    bytes
}

fn decode(bytes: &[u8]) -> Result<RawRecoveredImage, DecodeError> {
    decode_codestream_recover_missing_eoc(bytes, &DecodeOptions::default())
}

fn refuses_without_reservation(bytes: &[u8]) {
    allocation::with_refusal(0, || {
        assert!(decode(bytes).is_err());
        assert_eq!(
            allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn only_open_ended_eoc_loss_is_repaired_and_strict_stays_strict() {
    for (original, samples, geometry) in [
        (GRAY0, vec![0], (1, 1, 0, 0)),
        (OFFSET, vec![0, 64, 128, 255], (2, 2, 5, 7)),
    ] {
        let strict = crate::decode_codestream(original, &DecodeOptions::default()).unwrap();
        let bytes = damaged(original);
        assert!(crate::decode_codestream(&bytes, &DecodeOptions::default()).is_err());
        let repaired = decode(&bytes).unwrap();
        assert_eq!(repaired.image, strict);
        assert_eq!(
            repaired.image.components()[0].samples(),
            &TypedSamples::Unsigned(samples)
        );
        let report = repaired.report;
        assert!(report.appended_eoc);
        assert_eq!(
            (report.original_bytes, report.effective_bytes),
            (bytes.len() as u64, original.len() as u64)
        );
        assert_eq!(
            (
                report.width,
                report.height,
                report.x_origin,
                report.y_origin
            ),
            geometry
        );
        assert_eq!(report.repair_copy_bytes, original.len() as u64);
        let intact = decode(original).unwrap();
        assert_eq!(intact.image, strict);
        assert!(!intact.report.appended_eoc);
        assert_eq!(intact.report.original_bytes, intact.report.effective_bytes);
        assert_eq!(intact.report.repair_copy_bytes, 0);
        assert!(crate::decode_codestream(&bytes, &DecodeOptions::default()).is_err());
    }
    let mut unknown_count = damaged(GRAY0);
    unknown_count[SOT + 11] = 0;
    assert!(decode(&unknown_count).unwrap().report.appended_eoc);
}

#[test]
fn finite_other_tiles_parts_and_existing_eoc_trailers_never_reserve_a_repair() {
    let missing = damaged(GRAY0);
    let mut finite = missing.clone();
    finite[SOT + 6..SOT + 10].copy_from_slice(&19u32.to_be_bytes());
    refuses_without_reservation(&finite);
    for (part, count) in [(0, 2), (1, 2)] {
        let mut bytes = missing.clone();
        bytes[SOT + 10] = part;
        bytes[SOT + 11] = count;
        refuses_without_reservation(&bytes);
    }
    let mut tiles = missing.clone();
    tiles[8..12].copy_from_slice(&2u32.to_be_bytes());
    refuses_without_reservation(&tiles);
    let mut invalid_tile = missing.clone();
    invalid_tile[SOT + 5] = 1;
    refuses_without_reservation(&invalid_tile);
    let mut another_part = missing.clone();
    another_part.extend_from_slice(&GRAY0[SOT..GRAY0.len() - 2]);
    refuses_without_reservation(&another_part);
    let mut trailer = GRAY0.to_vec();
    trailer.extend_from_slice(&[0x01, 0x02, 0xff]);
    refuses_without_reservation(&trailer);
    assert_eq!(
        decode(&trailer).unwrap_err(),
        crate::decode_codestream(&trailer, &DecodeOptions::default()).unwrap_err()
    );
}

#[test]
fn incomplete_headers_and_sop_framing_reject_without_repair() {
    let bytes = damaged(GRAY0);
    for end in 0..BODY {
        refuses_without_reservation(&bytes[..end]);
    }
    let mut missing_qcd = bytes.clone();
    missing_qcd.drain(59..65);
    refuses_without_reservation(&missing_qcd);
    let mut malformed_sop = damaged(OFFSET);
    malformed_sop[BODY + 3] = 3;
    refuses_without_reservation(&malformed_sop);
    refuses_without_reservation(&damaged(OFFSET)[..BODY + 4]);
    refuses_without_reservation(b"\0\0\0\x0cjP  \r\n\x87\n");
}

#[test]
fn header_payload_marker_bytes_are_not_mistaken_for_tile_parts_or_eoc() {
    let mut bytes = damaged(GRAY0);
    bytes.splice(
        SOT..SOT,
        [
            0xff, 0x64, 0x00, 0x0a, 0x00, 0x01, 0xff, 0x90, 0xff, 0xd9, 0xff, 0x93,
        ],
    );
    let repaired = decode(&bytes).unwrap();
    assert!(repaired.report.appended_eoc);
    assert_eq!(
        repaired.image,
        crate::decode_codestream(GRAY0, &DecodeOptions::default()).unwrap()
    );
}

#[test]
fn genuine_entropy_and_output_limit_errors_are_forwarded_without_retry() {
    let mut corrupt = damaged(GRAY0);
    corrupt.truncate(BODY + 2);
    let mut effective = corrupt.clone();
    effective.extend_from_slice(&[0xff, 0xd9]);
    let strict_error = crate::decode_codestream(&effective, &DecodeOptions::default()).unwrap_err();
    assert_eq!(decode(&corrupt).unwrap_err(), strict_error);
    let mut trailer = damaged(GRAY0);
    trailer.extend_from_slice(&[0x01, 0x02]);
    let mut effective = trailer.clone();
    effective.extend_from_slice(&[0xff, 0xd9]);
    assert_eq!(
        decode(&trailer).unwrap_err(),
        crate::decode_codestream(&effective, &DecodeOptions::default()).unwrap_err(),
    );
    let bytes = damaged(GRAY0);
    let options = DecodeOptions::new(
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
    );
    let error = decode_codestream_recover_missing_eoc(&bytes, &options).unwrap_err();
    assert!(matches!(
        error,
        DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            ..
        }
    ));
    assert!(decode(&bytes).unwrap().report.appended_eoc);
}

#[test]
fn input_and_joint_preflight_copy_work_limits_precede_reservation() {
    let bytes = damaged(GRAY0);
    let frame = crate::codestream::recovery_framing(&bytes, &ResourceLimits::HARDENED).unwrap();
    let total = bytes.len() as u64 + 2;
    let combined = frame.work_units + total;
    for (limits, expected) in [
        (
            ResourceLimits::HARDENED
                .with_maximum_input_bytes(bytes.len() as u64 - 1)
                .unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::InputBytes,
                limit: bytes.len() as u64 - 1,
                actual: bytes.len() as u64,
            },
        ),
        (
            ResourceLimits::HARDENED
                .with_maximum_input_bytes(bytes.len() as u64)
                .unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::InputBytes,
                limit: bytes.len() as u64,
                actual: total,
            },
        ),
        (
            ResourceLimits::HARDENED
                .with_maximum_work_units(frame.work_units - 1)
                .unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: frame.work_units - 1,
                actual: frame.work_units,
            },
        ),
        (
            ResourceLimits::HARDENED
                .with_maximum_work_units(combined - 1)
                .unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: combined - 1,
                actual: combined,
            },
        ),
        (
            ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 0,
                actual: 1,
            },
        ),
    ] {
        allocation::with_refusal(0, || {
            assert_eq!(
                decode_codestream_recover_missing_eoc(&bytes, &DecodeOptions::new(limits))
                    .unwrap_err(),
                expected
            );
            assert_eq!(
                allocation::empty_with_capacity::<u8>(1),
                Err(DecodeError::AllocationFailed)
            );
        });
    }
    let boundary = DecodeOptions::new(
        ResourceLimits::HARDENED
            .with_maximum_work_units(combined)
            .unwrap(),
    );
    assert_eq!(
        decode_codestream_recover_missing_eoc(&bytes, &boundary)
            .unwrap()
            .image,
        decode(&bytes).unwrap().image
    );
}

#[test]
fn one_atomic_reservation_refusal_and_unwind_leave_exact_same_process_success() {
    let bytes = damaged(GRAY0);
    let expected = decode(&bytes).unwrap();
    allocation::with_refusal(1, || {
        assert_eq!(decode(&bytes).unwrap(), expected);
        assert_eq!(
            allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
    allocation::with_refusal(0, || {
        assert_eq!(decode(&bytes).unwrap_err(), DecodeError::AllocationFailed);
        assert_eq!(decode(&bytes).unwrap(), expected);
    });
    let unwind = std::panic::catch_unwind(|| {
        allocation::with_refusal(0, || {
            assert_eq!(decode(&bytes).unwrap_err(), DecodeError::AllocationFailed);
            panic!("test-only unwind after refused repair");
        })
    });
    assert!(unwind.is_err());
    assert_eq!(decode(&bytes).unwrap(), expected);
    assert!(crate::decode_codestream(&bytes, &DecodeOptions::default()).is_err());
}
