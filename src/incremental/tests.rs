use super::*;
use crate::{ResourceLimits, TypedSamples, allocation};

const JP2: &[u8] = &[
    0x00, 0x00, 0x00, 0x0c, 0x6a, 0x50, 0x20, 0x20, 0x0d, 0x0a, 0x87, 0x0a, 0x00, 0x00, 0x00, 0x14,
    0x66, 0x74, 0x79, 0x70, 0x6a, 0x70, 0x32, 0x20, 0x00, 0x00, 0x00, 0x00, 0x6a, 0x70, 0x32, 0x20,
    0x00, 0x00, 0x00, 0x2d, 0x6a, 0x70, 0x32, 0x68, 0x00, 0x00, 0x00, 0x16, 0x69, 0x68, 0x64, 0x72,
    0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x07, 0x07, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x0f, 0x63, 0x6f, 0x6c, 0x72, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x11, 0x00, 0x00, 0x00,
    0x5e, 0x6a, 0x70, 0x32, 0x63, 0xff, 0x4f, 0xff, 0x51, 0x00, 0x29, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x07,
    0x01, 0x01, 0xff, 0x52, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x04, 0x04, 0x00, 0x01,
    0xff, 0x5c, 0x00, 0x04, 0x40, 0x40, 0xff, 0x90, 0x00, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x13,
    0x00, 0x01, 0xff, 0x93, 0xdf, 0x80, 0x08, 0x07, 0x80, 0xff, 0xd9,
];

#[test]
fn incremental_arbitrary_raw_jp2_cuts_preserve_exact_final_outputs_and_identity() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    for (bytes, format) in [
        (&JP2[85..], IncrementalFormat::Codestream),
        (JP2, IncrementalFormat::Jp2),
    ] {
        let expected = typed(bytes, format, false, &options, &selection).unwrap().0;
        let wide = reconstructed(bytes, format, false, &options, &selection)
            .unwrap()
            .0;
        for split in 0..=bytes.len() {
            let mut decoder = IncrementalDecoder::new(format, &options, &selection);
            assert_eq!(decoder.feed(&bytes[..split]).unwrap().consumed, split);
            decoder.feed(&bytes[split..]).unwrap();
            assert_eq!(decoder.contiguous_input(), bytes);
            assert_eq!(decoder.progress().decode_attempts, 0);
            decoder.finish().unwrap();
            match decoder.decode().unwrap() {
                IncrementalUpdate::Complete {
                    image,
                    recovery,
                    progress,
                } => {
                    assert_eq!(image, expected);
                    assert!(recovery.is_none());
                    assert_eq!(progress.committed_bytes, bytes.len() as u64);
                }
                result => panic!("missing completed image: {result:?}"),
            }
            match decoder.decode_reconstructed().unwrap() {
                IncrementalUpdate::Complete { image, .. } => assert_eq!(image, wide),
                result => panic!("missing centered image: {result:?}"),
            }
            let before = decoder.progress();
            assert!(matches!(
                decoder.decode().unwrap(),
                IncrementalUpdate::Unchanged { .. }
            ));
            assert_eq!(decoder.progress(), before);
            assert!(matches!(
                decoder.feed(&[0]),
                Err(IncrementalError::InputClosed)
            ));
        }
    }
}

#[test]
fn incremental_partial_packets_commit_only_complete_snapshots_and_final_eof_is_explicit() {
    let raw = &JP2[85..];
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let expected = crate::decode_codestream(raw, &options).unwrap();
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Codestream, &options, &selection);
    for end in 1..=raw.len() {
        decoder.feed(&raw[end - 1..end]).unwrap();
        let committed = decoder.progress().committed_bytes;
        match decoder.decode().unwrap() {
            IncrementalUpdate::NeedMoreData { .. } => {
                assert_eq!(decoder.progress().committed_bytes, committed)
            }
            IncrementalUpdate::Preview {
                image, snapshot, ..
            } => {
                assert_eq!(image, expected);
                assert_eq!(snapshot.source_bytes, end as u64);
                assert_eq!(snapshot.synthetic_eoc, end < raw.len());
            }
            result => panic!("open input must not complete: {result:?}"),
        }
        let attempts = decoder.progress().decode_attempts;
        let work = decoder.progress().wrapper_work_units;
        decoder.feed(&[]).unwrap();
        decoder.decode().unwrap();
        assert_eq!(decoder.progress().decode_attempts, attempts);
        assert_eq!(decoder.progress().wrapper_work_units, work);
    }
    assert!(decoder.progress().committed_bytes >= 83);
    decoder.finish().unwrap();
    assert!(matches!(
        decoder.decode().unwrap(),
        IncrementalUpdate::Complete { .. }
    ));
}

#[test]
fn incremental_suffix_first_gaps_duplicates_overlap_and_conflicts_are_transactional() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Jp2, &options, &selection);
    decoder.feed_at(80, &JP2[80..]).unwrap();
    assert!(matches!(
        decoder.decode().unwrap(),
        IncrementalUpdate::NeedMoreData {
            reason: IncrementalNeed::Gap {
                offset: 0,
                length: 80
            },
            ..
        }
    ));
    allocation::with_refusal(0, || {
        decoder.feed_at(90, &JP2[90..100]).unwrap();
        assert_eq!(
            allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
    decoder.feed(&JP2[..20]).unwrap();
    assert!(matches!(
        decoder.decode().unwrap(),
        IncrementalUpdate::NeedMoreData {
            reason: IncrementalNeed::Gap {
                offset: 20,
                length: 60
            },
            ..
        }
    ));
    decoder.feed_at(30, &JP2[30..90]).unwrap();
    assert_eq!(decoder.progress().retained_bytes, (JP2.len() - 10) as u64);
    assert!(matches!(
        decoder.decode().unwrap(),
        IncrementalUpdate::NeedMoreData {
            reason: IncrementalNeed::Gap {
                offset: 20,
                length: 10
            },
            ..
        }
    ));
    let before = decoder.progress();
    assert_eq!(
        decoder.feed_at(40, &[0xff]).unwrap_err(),
        IncrementalError::ConflictingInput { offset: 40 },
    );
    assert_eq!(decoder.progress().retained_bytes, before.retained_bytes);
    decoder.feed_at(0, &JP2[..40]).unwrap();
    assert_eq!(decoder.contiguous_input(), JP2);
    assert_eq!(decoder.progress().pending_fragments, 0);
    decoder.finish().unwrap();
    assert!(matches!(
        decoder.decode().unwrap(),
        IncrementalUpdate::Complete { .. }
    ));
}

#[test]
fn incremental_refused_storage_and_decode_retain_source_for_exact_retry() {
    let raw = &JP2[85..];
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    for refusal in [0, 2] {
        let mut decoder =
            IncrementalDecoder::new(IncrementalFormat::Codestream, &options, &selection);
        decoder.feed(&raw[..20]).unwrap();
        assert_eq!(
            allocation::with_refusal(refusal, || decoder.feed_at(40, &raw[40..60])).unwrap_err(),
            IncrementalError::Decode(DecodeError::AllocationFailed),
        );
        assert_eq!(decoder.contiguous_input(), &raw[..20]);
        assert_eq!(decoder.progress().retained_bytes, 20);
        assert_eq!(decoder.progress().pending_fragments, 0);
        decoder.feed_at(40, &raw[40..60]).unwrap();
        decoder.feed_at(20, &raw[20..]).unwrap();
        assert_eq!(decoder.contiguous_input(), raw);
        decoder.finish().unwrap();
        assert_eq!(
            allocation::with_refusal(0, || decoder.decode()).unwrap_err(),
            IncrementalError::Decode(DecodeError::AllocationFailed),
        );
        match decoder.decode().unwrap() {
            IncrementalUpdate::Complete { image, .. } => assert_eq!(
                image.component(0).unwrap().samples(),
                &TypedSamples::Unsigned(vec![0]),
            ),
            result => panic!("retry did not complete: {result:?}"),
        }
        assert_eq!(decoder.progress().decode_attempts, 2);
    }
}

#[test]
fn incremental_late_typed_storage_refusal_retains_input_preview_final_and_retry() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    for (bytes, format) in [
        (&JP2[85..], IncrementalFormat::Codestream),
        (JP2, IncrementalFormat::Jp2),
    ] {
        let expected = typed(bytes, format, false, &options, &selection).unwrap().0;
        for final_input in [false, true] {
            let mut completed_after = None;
            for after in 0..256 {
                let mut decoder = IncrementalDecoder::new(format, &options, &selection);
                decoder.feed(bytes).unwrap();
                if final_input {
                    decoder.finish().unwrap();
                }
                let before = decoder.progress();
                let source = decoder.contiguous_input().as_ptr();
                match allocation::with_refusal(after, || decoder.decode()) {
                    Err(IncrementalError::Decode(DecodeError::AllocationFailed)) => {
                        assert_eq!(decoder.contiguous_input(), bytes);
                        assert_eq!(decoder.contiguous_input().as_ptr(), source);
                        let refused = decoder.progress();
                        assert_eq!(refused.retained_bytes, before.retained_bytes);
                        assert_eq!(refused.retained_end, before.retained_end);
                        assert_eq!(refused.pending_fragments, before.pending_fragments);
                        assert_eq!(refused.final_length, before.final_length);
                        assert_eq!(refused.committed_bytes, before.committed_bytes);
                        match decoder.decode().unwrap() {
                            IncrementalUpdate::Complete { image, .. } if final_input => {
                                assert_eq!(image, expected);
                            }
                            IncrementalUpdate::Preview { image, .. } if !final_input => {
                                assert_eq!(image, expected);
                            }
                            result => panic!("late storage retry did not publish: {result:?}"),
                        }
                        assert_eq!(
                            decoder.progress().decode_attempts,
                            refused.decode_attempts + 1
                        );
                        if final_input {
                            assert_eq!(
                                decoder.progress().replayed_input_bytes,
                                refused.replayed_input_bytes + bytes.len() as u64
                            );
                        }
                        let published = decoder.progress();
                        assert!(matches!(
                            decoder.decode().unwrap(),
                            IncrementalUpdate::Unchanged { .. }
                        ));
                        assert_eq!(decoder.progress(), published);
                    }
                    Ok(IncrementalUpdate::Complete { image, .. }) if final_input => {
                        assert_eq!(image, expected);
                        completed_after = Some(after);
                        break;
                    }
                    Ok(IncrementalUpdate::Preview { image, .. }) if !final_input => {
                        assert_eq!(image, expected);
                        completed_after = Some(after);
                        break;
                    }
                    result => panic!("unexpected storage sweep result: {result:?}"),
                }
            }
            assert!(completed_after.is_some_and(|count| count >= 2));
        }
    }
}

#[test]
fn incremental_final_truncation_limits_and_actual_malformed_errors_are_not_waiting() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let mut missing = IncrementalDecoder::new(IncrementalFormat::Jp2, &options, &selection);
    missing.feed_at(20, &JP2[20..]).unwrap();
    missing.finish_at(JP2.len() as u64).unwrap();
    assert!(matches!(
        missing.decode(),
        Err(IncrementalError::Decode(DecodeError::MalformedInput {
            kind: MalformedKind::Truncated,
            ..
        }))
    ));
    assert!(matches!(
        missing.feed(&JP2[..20]),
        Err(IncrementalError::InputClosed)
    ));

    let mut malformed =
        IncrementalDecoder::new(IncrementalFormat::Codestream, &options, &selection);
    malformed.feed(&[0xff, 0x4f, 0xff, 0x51, 0, 1]).unwrap();
    assert!(matches!(
        malformed.decode(),
        Err(IncrementalError::Decode(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerLength,
            ..
        }))
    ));
    let limited = DecodeOptions::new(
        ResourceLimits::default()
            .with_maximum_input_bytes(16)
            .unwrap(),
    );
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Jp2, &limited, &selection);
    assert!(matches!(
        decoder.feed(JP2),
        Err(IncrementalError::Decode(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            ..
        }))
    ));
    assert!(decoder.contiguous_input().is_empty());
    let limited = DecodeOptions::new(
        ResourceLimits::default()
            .with_maximum_work_units(10)
            .unwrap(),
    );
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Jp2, &limited, &selection);
    assert!(matches!(
        decoder.feed(&JP2[..10]),
        Err(IncrementalError::Decode(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            ..
        }))
    ));
    assert!(decoder.contiguous_input().is_empty());
}

#[test]
fn incremental_previews_never_turn_network_pause_into_final_eoc_repair() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let mut raw = JP2[85..JP2.len() - 2].to_vec();
    raw[71..75].copy_from_slice(&0_u32.to_be_bytes());
    let mut strict = IncrementalDecoder::new(IncrementalFormat::Codestream, &options, &selection);
    strict.feed(&raw).unwrap();
    assert!(matches!(
        strict.decode().unwrap(),
        IncrementalUpdate::Preview {
            snapshot: IncrementalSnapshot {
                synthetic_eoc: true,
                ..
            },
            ..
        }
    ));
    assert_eq!(strict.contiguous_input(), raw);
    strict.finish().unwrap();
    assert!(matches!(
        strict.decode(),
        Err(IncrementalError::Decode(DecodeError::MalformedInput {
            kind: MalformedKind::Truncated,
            ..
        }))
    ));
    let mut compatible = IncrementalDecoder::new_pdf_compatible(&options, &selection);
    compatible.feed(&raw).unwrap();
    assert!(matches!(
        compatible.decode().unwrap(),
        IncrementalUpdate::Preview { .. }
    ));
    compatible.finish().unwrap();
    match compatible.decode().unwrap() {
        IncrementalUpdate::Complete {
            recovery: Some(recovery),
            ..
        } => {
            assert!(recovery.appended_eoc);
            assert_eq!(recovery.original_codestream_bytes, raw.len() as u64);
        }
        result => panic!("explicit final recovery missing: {result:?}"),
    }
}

#[test]
fn incremental_waiting_header_cost_does_not_replay_the_buffer_on_every_byte() {
    let options = DecodeOptions::new(
        ResourceLimits::default()
            .with_maximum_work_units(1_000_000)
            .unwrap(),
    );
    let selection = DecodeSelection::full_image();
    let original = &JP2[85..];
    let mut raw = original[..65].to_vec();
    raw.extend_from_slice(&[0xff, 0x64]);
    raw.extend_from_slice(&8196_u16.to_be_bytes());
    raw.extend_from_slice(&[0, 1]);
    raw.extend_from_slice(&[0x11; 8192]);
    raw.extend_from_slice(&original[65..]);
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Codestream, &options, &selection);
    for byte in &raw {
        decoder.feed(std::slice::from_ref(byte)).unwrap();
        decoder.decode().unwrap();
    }
    decoder.finish().unwrap();
    assert!(matches!(
        decoder.decode().unwrap(),
        IncrementalUpdate::Complete { .. }
    ));
    assert!(decoder.progress().decode_attempts < 16);
    assert!(decoder.progress().wrapper_work_units < 1_000_000);
    assert_eq!(decoder.contiguous_input(), raw);
}

#[test]
fn incremental_extended_and_zero_jp2_boxes_preserve_source_and_footer_boundaries() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let expected = crate::decode_jp2(JP2, &options).unwrap();
    for extended in [false, true] {
        let mut bytes = JP2[..77].to_vec();
        bytes.extend_from_slice(&u32::from(extended).to_be_bytes());
        bytes.extend_from_slice(b"jp2c");
        if extended {
            bytes.extend_from_slice(&102_u64.to_be_bytes());
        }
        bytes.extend_from_slice(&JP2[85..]);
        if extended {
            bytes.extend_from_slice(&[0, 0, 0, 8, b'f', b'r', b'e', b'e']);
        }
        let mut decoder = IncrementalDecoder::new(IncrementalFormat::Jp2, &options, &selection);
        for byte in &bytes {
            decoder.feed(std::slice::from_ref(byte)).unwrap();
            if let IncrementalUpdate::Preview { image, .. } = decoder.decode().unwrap() {
                assert_eq!(image, expected);
            }
        }
        assert_eq!(decoder.contiguous_input(), bytes);
        decoder.finish().unwrap();
        match decoder.decode().unwrap() {
            IncrementalUpdate::Complete { image, .. } => assert_eq!(image, expected),
            result => panic!("extended/zero box final decoding changed: {result:?}"),
        }
    }
}

#[test]
fn incremental_jp2_preview_preserves_received_footer_and_known_malformed_suffixes() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let mut bytes = JP2[..JP2.len() - 2].to_vec();
    bytes[77..81].copy_from_slice(&92_u32.to_be_bytes());
    bytes[85 + 71..85 + 75].copy_from_slice(&0_u32.to_be_bytes());
    let footer = [0, 0, 0, 8, b'f', b'r', b'e', b'e'];
    bytes.extend_from_slice(&footer);
    let mut work = 0;
    let framing::Preview::Ready(snapshot) =
        framing::snapshot(&bytes, IncrementalFormat::Jp2, options.limits(), &mut work).unwrap()
    else {
        panic!("complete header/body must provide a provisional preview");
    };
    assert!(snapshot.bytes.ends_with(&footer));
    assert_eq!(snapshot.bytes.len(), bytes.len() + 2);
    assert_eq!(
        u32::from_be_bytes(snapshot.bytes[77..81].try_into().unwrap()),
        94
    );
    assert!(crate::decode_jp2(&snapshot.bytes, &options).is_ok());
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Jp2, &options, &selection);
    decoder.feed(&bytes).unwrap();
    assert!(matches!(
        decoder.decode().unwrap(),
        IncrementalUpdate::Preview { .. }
    ));
    assert_eq!(decoder.contiguous_input(), bytes);

    let mut trailing = JP2[85..].to_vec();
    trailing.push(0x11);
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Codestream, &options, &selection);
    decoder.feed(&trailing).unwrap();
    assert!(matches!(
        decoder.decode(),
        Err(IncrementalError::Decode(DecodeError::MalformedInput {
            kind: MalformedKind::TrailingData,
            ..
        }))
    ));
}

#[test]
fn incremental_later_partial_contributions_preserve_the_committed_packet() {
    // OpenJPEG 2.4.0, 8x8 P5 sample (37*x+19*y+3*x*y)&255, -n 1 -r 4,1.
    const RAW: &[u8] = &[
        0xff, 0x4f, 0xff, 0x51, 0x00, 0x29, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00,
        0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00,
        0x00, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x07, 0x01, 0x01,
        0xff, 0x52, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x04, 0x04, 0x00, 0x01, 0xff,
        0x5c, 0x00, 0x04, 0x40, 0x40, 0xff, 0x64, 0x00, 0x25, 0x00, 0x01, 0x43, 0x72, 0x65, 0x61,
        0x74, 0x65, 0x64, 0x20, 0x62, 0x79, 0x20, 0x4f, 0x70, 0x65, 0x6e, 0x4a, 0x50, 0x45, 0x47,
        0x20, 0x76, 0x65, 0x72, 0x73, 0x69, 0x6f, 0x6e, 0x20, 0x32, 0x2e, 0x34, 0x2e, 0x30, 0xff,
        0x90, 0x00, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x54, 0x00, 0x01, 0xff, 0x93, 0xdf, 0x11,
        0xa0, 0x12, 0x2b, 0x64, 0x75, 0x12, 0x99, 0x74, 0xe3, 0xd6, 0x36, 0xeb, 0x3e, 0xf5, 0x31,
        0xc5, 0x11, 0xd9, 0x1f, 0xbd, 0xe1, 0xaa, 0x5c, 0xf1, 0xaf, 0x5e, 0x2d, 0xfd, 0x09, 0x80,
        0xcf, 0xee, 0x7c, 0x3c, 0x45, 0x71, 0x8c, 0xee, 0x3e, 0x66, 0x22, 0x6e, 0x29, 0x27, 0x26,
        0x37, 0xd7, 0xa7, 0x63, 0xcf, 0x97, 0x50, 0x96, 0x7d, 0x45, 0x91, 0x25, 0xa4, 0x78, 0x4f,
        0x2e, 0xbb, 0x9b, 0x06, 0xcd, 0x26, 0xce, 0x31, 0xff, 0xd9,
    ];
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let expected = crate::decode_codestream(RAW, &options).unwrap();
    let samples = (0..8)
        .flat_map(|y| (0..8).map(move |x| (37 * x + 19 * y + 3 * x * y) & 255))
        .collect();
    assert_eq!(
        expected.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(samples)
    );
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Codestream, &options, &selection);
    let mut partial_after_commit = false;
    for (index, byte) in RAW.iter().enumerate() {
        decoder.feed(std::slice::from_ref(byte)).unwrap();
        let committed = decoder.progress().committed_bytes;
        if matches!(
            decoder.decode().unwrap(),
            IncrementalUpdate::NeedMoreData { .. }
        ) {
            assert_eq!(decoder.progress().committed_bytes, committed);
            partial_after_commit |= committed > 0 && index + 1 < RAW.len() - 2;
        }
    }
    assert!(partial_after_commit);
    decoder.finish().unwrap();
    match decoder.decode().unwrap() {
        IncrementalUpdate::Complete { image, .. } => assert_eq!(image, expected),
        result => panic!("later real contribution was not completed exactly: {result:?}"),
    }
}

#[test]
fn incremental_complete_container_and_bad_tile_header_do_not_wait_indefinitely() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let mut duplicate = JP2.to_vec();
    duplicate.extend_from_slice(&JP2[77..]);
    let expected = crate::decode_jp2(&duplicate, &options).unwrap();
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Jp2, &options, &selection);
    decoder.feed(&duplicate).unwrap();
    match decoder.decode().unwrap() {
        IncrementalUpdate::Preview { image, .. } => assert_eq!(image, expected),
        result => panic!("complete container lost ordinary decoder semantics: {result:?}"),
    }

    let mut bad = JP2[85..].to_vec();
    bad[67..69].copy_from_slice(&8_u16.to_be_bytes());
    let expected = crate::decode_codestream(&bad, &options).unwrap_err();
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Codestream, &options, &selection);
    decoder.feed(&bad[..79]).unwrap();
    assert_eq!(
        decoder.decode().err(),
        Some(IncrementalError::Decode(expected))
    );
}

#[cfg(feature = "cooperative-deadlines")]
#[test]
fn incremental_absolute_deadline_cannot_reset_across_feeds_and_cancels_the_owner() {
    use std::time::{Duration, Instant};
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Jp2, &options, &selection);
    decoder.feed(&JP2[..12]).unwrap();
    let mut decoder = decoder.with_deadline(Instant::now() + Duration::from_millis(5));
    std::thread::sleep(Duration::from_millis(15));
    assert!(matches!(
        decoder.feed(&JP2[12..]),
        Err(IncrementalError::Decode(DecodeError::DeadlineExceeded))
    ));
    let mut decoder = decoder.with_deadline(Instant::now() + Duration::from_secs(60));
    assert!(matches!(
        decoder.decode(),
        Err(IncrementalError::Decode(DecodeError::DeadlineExceeded))
    ));
    let mut fresh = IncrementalDecoder::new(IncrementalFormat::Jp2, &options, &selection);
    fresh.feed(JP2).unwrap();
    fresh.finish().unwrap();
    assert!(matches!(
        fresh.decode().unwrap(),
        IncrementalUpdate::Complete { .. }
    ));

    let mut ambient = IncrementalDecoder::new(IncrementalFormat::Jp2, &options, &selection);
    let result = crate::with_decode_deadline(Instant::now() + Duration::from_millis(5), || {
        std::thread::sleep(Duration::from_millis(15));
        assert!(matches!(
            ambient.feed(JP2),
            Err(IncrementalError::Decode(DecodeError::DeadlineExceeded))
        ));
        Ok(())
    });
    assert_eq!(result, Err(DecodeError::DeadlineExceeded));
    assert!(matches!(
        ambient.feed(JP2),
        Err(IncrementalError::Decode(DecodeError::DeadlineExceeded))
    ));
}

#[cfg(feature = "cooperative-deadlines")]
#[test]
fn incremental_exit_expiry_does_not_publish_a_completed_backend_result() {
    use std::time::{Duration, Instant};
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let mut decoder = IncrementalDecoder::new(IncrementalFormat::Jp2, &options, &selection);
    decoder.feed(JP2).unwrap();
    decoder.finish().unwrap();
    let mut decoder = decoder.with_deadline(Instant::now() + Duration::from_millis(500));
    let result = decoder.run(|decoder| {
        let output = decoder.decode_inner(0, typed)?;
        assert!(matches!(output, IncrementalUpdate::Complete { .. }));
        std::thread::sleep(Duration::from_millis(600));
        Ok(output)
    });
    assert!(matches!(
        result,
        Err(IncrementalError::Decode(DecodeError::DeadlineExceeded))
    ));
    assert_eq!(decoder.progress().committed_bytes, 0);
    assert_eq!(decoder.progress().decode_attempts, 1);
    assert_eq!(decoder.contiguous_input(), JP2);
}
