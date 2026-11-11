use super::cache_layout_result_tests::{bin, frame, id, storage};
use super::*;

pub(super) fn data(
    form: u8,
    last: bool,
    bin: u8,
    class: u8,
    stream: u8,
    offset: u8,
    bytes: &[u8],
) -> Vec<u8> {
    let mut output = vec![(form << 5) | if last { 0x10 } else { 0 } | bin];
    if form >= 2 {
        output.push(class);
    }
    if form == 3 {
        output.push(stream);
    }
    output.extend_from_slice(&[offset, u8::try_from(bytes.len()).unwrap()]);
    if class & 1 != 0 {
        output.push(9);
    }
    output.extend_from_slice(bytes);
    output
}

fn state(limit: u64, fragments: u64, stored_bytes: u64, accepted_fragments: u64) -> DatabinCache {
    DatabinCache {
        limits: ResourceLimits::HARDENED
            .with_maximum_input_bytes(limit)
            .unwrap()
            .with_maximum_jpip_fragments(fragments)
            .unwrap(),
        databins: vec![bin(id(8, 9, 9), &[(0, b"unrelated")], Some(9))],
        stored_bytes,
        accepted_fragments,
    }
}

fn assert_target(
    cache: &DatabinCache,
    databin: DatabinId,
    bytes: &[u8],
    final_length: Option<u64>,
) {
    let target = &cache.databins[1];
    assert_eq!(target.id, databin);
    assert_eq!(target.final_length, final_length);
    assert_eq!(target.fragments.len(), 1);
    assert_eq!(target.fragments[0].offset, 0);
    assert_eq!(target.fragments[0].bytes, bytes);
}

fn complete_response() -> Vec<u8> {
    let mut input = data(3, false, 0, 6, 3, 0, b"A");
    input.extend(data(1, true, 0, 6, 3, 1, b"B"));
    input.extend_from_slice(&[0, 7, 2, 0xfe, 0xff]);
    input
}

#[test]
fn actual_jpip_response_derives_full_summary_and_cache_from_raw_header_forms_and_eor() {
    let payloads: &[&[u8]] = &[b"ab", b"abcd", &[0xff, 0x4f, 0xff, 0xd9], &[0, 0x80]];
    let mut cases = 0;
    for class in 0..=8 {
        for stream in 0..4 {
            for bin in 0..4 {
                for payload in payloads {
                    for form in [1, 2] {
                        for reason in [None, Some(0), Some(255)] {
                            let mut cache = state(128, 16, 9, 0);
                            let untouched_fragments = storage(&cache.databins[0].fragments);
                            let untouched_bytes = storage(&cache.databins[0].fragments[0].bytes);
                            let split = payload.len() / 2;
                            let mut input =
                                data(3, false, bin, class, stream, 0, &payload[..split]);
                            input.extend(data(
                                form,
                                true,
                                bin,
                                class,
                                stream,
                                u8::try_from(split).unwrap(),
                                &payload[split..],
                            ));
                            if let Some(reason) = reason {
                                input.extend_from_slice(&[0, reason, 2, 0xfe, 0xff]);
                            }
                            let summary = ingest_jpip_response(&input, &mut cache).unwrap();
                            assert_eq!(summary.messages(), 2);
                            assert_eq!(summary.end_of_response_reason(), reason);
                            assert_eq!(cache.accepted_fragments, 2);
                            assert_eq!(cache.stored_bytes, 9 + payload.len() as u64);
                            assert_eq!(cache.databins.len(), 2);
                            assert_target(
                                &cache,
                                id(u64::from(class), u64::from(stream), u64::from(bin)),
                                payload,
                                Some(payload.len() as u64),
                            );
                            assert_eq!(storage(&cache.databins[0].fragments), untouched_fragments);
                            assert_eq!(
                                storage(&cache.databins[0].fragments[0].bytes),
                                untouched_bytes
                            );
                            assert_eq!(cache.databins[0].fragments[0].bytes, b"unrelated");
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 3456);
}

#[test]
fn actual_jpip_response_retains_exact_prior_commits_and_relative_errors_at_every_raw_cut() {
    let mut input = complete_response();
    input.push(0x99);
    let mut cases = 0;
    for length in 0..=input.len() {
        let mut cache = state(128, 16, 9, 0);
        let before = frame(&cache);
        let untouched_fragments = storage(&cache.databins[0].fragments);
        let untouched_bytes = storage(&cache.databins[0].fragments[0].bytes);
        let output = ingest_jpip_response(&input[..length], &mut cache);
        let committed = if length < 6 {
            0
        } else if length < 10 {
            1
        } else {
            2
        };
        assert_eq!(cache.accepted_fragments, committed);
        assert_eq!(cache.stored_bytes, 9 + committed);
        if committed == 0 {
            assert_eq!(frame(&cache), before);
        } else {
            assert_target(
                &cache,
                id(6, 3, 0),
                if committed == 1 { b"A" } else { b"AB" },
                if committed == 1 { None } else { Some(2) },
            );
        }
        assert_eq!(storage(&cache.databins[0].fragments), untouched_fragments);
        assert_eq!(
            storage(&cache.databins[0].fragments[0].bytes),
            untouched_bytes
        );
        match length {
            0 | 6 | 10 | 15 => {
                let summary = output.unwrap();
                assert_eq!(summary.messages(), committed);
                assert_eq!(
                    summary.end_of_response_reason(),
                    if length == 15 { Some(7) } else { None }
                );
            }
            16 => assert_eq!(
                output,
                Err(DecodeError::malformed(15, MalformedKind::TrailingData))
            ),
            _ => {
                let offset = if length < 6 {
                    length
                } else if length < 10 {
                    length - 6
                } else if length < 13 {
                    length - 10
                } else {
                    3
                };
                assert_eq!(
                    output,
                    Err(DecodeError::malformed(
                        offset as u64,
                        MalformedKind::Truncated
                    )),
                    "raw cut {length}"
                );
            }
        }
        cases += 1;
    }
    assert_eq!(cases, 17);
    let mut cache = state(128, 16, 9, 0);
    let empty = ingest_jpip_response(&[], &mut cache).unwrap();
    assert_eq!(empty.messages(), 0);
    let before = frame(&cache);
    assert_eq!(
        ingest_jpip_response(&[0x20], &mut cache),
        Err(DecodeError::malformed(1, MalformedKind::Truncated))
    );
    assert_eq!(frame(&cache), before);
}

#[test]
fn actual_jpip_response_preserves_first_limit_overflow_error_and_native_cache_frames() {
    let input = complete_response();
    let mut cases = 0;
    for limit in [0_u64, 1, 4, 16, 128] {
        for cap in [1_u64, 2, 4] {
            for initial_count in [0_u64, u64::MAX - 1, u64::MAX] {
                for initial_bytes in [0_u64, limit.saturating_sub(1), u64::MAX] {
                    let mut cache = state(limit, cap, initial_bytes, initial_count);
                    let limits = cache.limits;
                    let before = frame(&cache);
                    let untouched_fragments = storage(&cache.databins[0].fragments);
                    let untouched_bytes = storage(&cache.databins[0].fragments[0].bytes);
                    let mut committed = 0_u64;
                    let mut count = initial_count;
                    let mut bytes = initial_bytes;
                    let mut expected = None;
                    if input.len() as u64 > limit {
                        expected = Some(DecodeError::limit(
                            Resource::InputBytes,
                            limit,
                            input.len() as u64,
                        ));
                    } else {
                        for offset in 0..2 {
                            let Some(next_count) = count.checked_add(1) else {
                                expected = Some(DecodeError::malformed(
                                    offset,
                                    MalformedKind::ArithmeticOverflow,
                                ));
                                break;
                            };
                            if next_count > cap {
                                expected = Some(DecodeError::limit(
                                    Resource::JpipFragments,
                                    cap,
                                    next_count,
                                ));
                                break;
                            }
                            let Some(next_bytes) = bytes.checked_add(1) else {
                                expected = Some(DecodeError::malformed(
                                    offset,
                                    MalformedKind::ArithmeticOverflow,
                                ));
                                break;
                            };
                            if next_bytes > limit {
                                expected = Some(DecodeError::limit(
                                    Resource::InputBytes,
                                    limit,
                                    next_bytes,
                                ));
                                break;
                            }
                            count = next_count;
                            bytes = next_bytes;
                            committed += 1;
                        }
                    }
                    let result = ingest_jpip_response(&input, &mut cache);
                    match expected {
                        Some(error) => assert_eq!(result, Err(error)),
                        None => {
                            let summary = result.unwrap();
                            assert_eq!(summary.messages(), 2);
                            assert_eq!(summary.end_of_response_reason(), Some(7));
                        }
                    }
                    assert_eq!(cache.limits, limits);
                    assert_eq!(cache.accepted_fragments, count);
                    assert_eq!(cache.stored_bytes, bytes);
                    assert_eq!(cache.databins.len(), if committed == 0 { 1 } else { 2 });
                    if committed == 0 {
                        assert_eq!(frame(&cache), before);
                    } else {
                        assert_target(
                            &cache,
                            id(6, 3, 0),
                            if committed == 1 { b"A" } else { b"AB" },
                            if committed == 1 { None } else { Some(2) },
                        );
                    }
                    assert_eq!(storage(&cache.databins[0].fragments), untouched_fragments);
                    assert_eq!(
                        storage(&cache.databins[0].fragments[0].bytes),
                        untouched_bytes
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 135);
}
