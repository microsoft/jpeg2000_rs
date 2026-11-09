use super::cache_layout_result_tests::{bin, frame, id};
use super::*;

fn state(databins: Vec<Databin>, input: u64, packets: u64, work: u64) -> DatabinCache {
    DatabinCache {
        limits: ResourceLimits::HARDENED
            .with_maximum_input_bytes(input)
            .unwrap()
            .with_maximum_packets(packets)
            .unwrap()
            .with_maximum_work_units(work)
            .unwrap(),
        databins,
        stored_bytes: u64::MAX,
        accepted_fragments: u64::MAX,
    }
}

fn range(databin: DatabinId, offset: u64, length: u64) -> JpipDatabinRange {
    JpipDatabinRange {
        databin,
        offset,
        length,
    }
}

fn overflow(offset: u64) -> DecodeError {
    DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow)
}

fn missing(offset: u64) -> DecodeError {
    DecodeError::malformed(offset, MalformedKind::MissingRequiredStructure)
}

fn selected(cache: &DatabinCache, requested: DatabinId) -> Option<&Databin> {
    cache.databins.iter().find(|bin| {
        bin.id.class_identifier / 2 == requested.class_identifier / 2
            && bin.id.codestream == requested.codestream
            && bin.id.in_class == requested.in_class
    })
}

fn expected_availability(
    cache: &DatabinCache,
    ranges: &[JpipDatabinRange],
) -> Result<JpipAvailabilityReport, DecodeError> {
    let packets = cache.limits.maximum_packets();
    let input = cache.limits.maximum_input_bytes();
    let work_limit = cache.limits.maximum_work_units();
    if ranges.len() as u64 > packets {
        return Err(DecodeError::limit(
            Resource::Packets,
            packets,
            ranges.len() as u64,
        ));
    }
    let mut required = 0_u128;
    let mut work = 0_u128;
    let mut absent = Vec::new();
    for request in ranges {
        let end = u128::from(request.offset) + u128::from(request.length);
        if end > u128::from(u64::MAX) {
            return Err(overflow(request.offset));
        }
        if end > u128::from(input) {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                input,
                u64::try_from(end).unwrap(),
            ));
        }
        required += u128::from(request.length);
        if required > u128::from(u64::MAX) {
            return Err(overflow(request.offset));
        }
        if required > u128::from(input) {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                input,
                u64::try_from(required).unwrap(),
            ));
        }
        let mut cursor = u128::from(request.offset);
        if selected(cache, request.databin).is_none() {
            absent.push(JpipMissingRange {
                databin: request.databin,
                offset: request.offset,
                length: Some(request.length),
            });
            continue;
        }
        if let Some(bin) = selected(cache, request.databin) {
            for fragment in &bin.fragments {
                if cursor >= end {
                    break;
                }
                work += 1;
                if work > u128::from(u64::MAX) {
                    return Err(overflow(u64::try_from(cursor).unwrap()));
                }
                if work > u128::from(work_limit) {
                    return Err(DecodeError::limit(
                        Resource::WorkUnits,
                        work_limit,
                        u64::try_from(work).unwrap(),
                    ));
                }
                let begin = u128::from(fragment.offset);
                let stop = (begin + fragment.bytes.len() as u128).min(u128::from(u64::MAX));
                if stop <= cursor {
                    continue;
                }
                if begin >= end {
                    break;
                }
                if begin > cursor {
                    absent.push(JpipMissingRange {
                        databin: request.databin,
                        offset: u64::try_from(cursor).unwrap(),
                        length: Some(u64::try_from(begin.min(end) - cursor).unwrap()),
                    });
                    cursor = begin.min(end);
                }
                cursor = cursor.max(stop.min(end));
            }
        }
        if cursor < end {
            absent.push(JpipMissingRange {
                databin: request.databin,
                offset: u64::try_from(cursor).unwrap(),
                length: Some(u64::try_from(end - cursor).unwrap()),
            });
        }
    }
    let missing: u128 = absent
        .iter()
        .map(|range| u128::from(range.length.unwrap_or(0)))
        .sum();
    if missing > u128::from(u64::MAX) || missing > required {
        return Err(overflow(0));
    }
    let available = required - missing;
    Ok(JpipAvailabilityReport {
        status: if available == required {
            JpipAvailability::Available
        } else if available == 0 {
            JpipAvailability::Missing
        } else {
            JpipAvailability::Partial
        },
        required_bytes: u64::try_from(required).unwrap(),
        available_bytes: u64::try_from(available).unwrap(),
        missing: absent,
    })
}

fn expected_packets(
    cache: &DatabinCache,
    packets: &[JpipPrecinctPacket],
) -> Result<Vec<u8>, DecodeError> {
    let total: u128 = packets
        .iter()
        .map(|packet| u128::from(packet.range.length))
        .sum();
    if total > u128::from(u64::MAX) {
        return Err(overflow(0));
    }
    if total > u128::from(cache.limits.maximum_input_bytes()) {
        return Err(DecodeError::limit(
            Resource::InputBytes,
            cache.limits.maximum_input_bytes(),
            u64::try_from(total).unwrap(),
        ));
    }
    if usize::try_from(total).is_err() {
        return Err(overflow(0));
    }
    let mut bytes = Vec::new();
    for packet in packets {
        let request = packet.range;
        let bin = selected(cache, request.databin).ok_or_else(|| missing(request.offset))?;
        let end = u128::from(request.offset) + u128::from(request.length);
        if end > u128::from(u64::MAX) {
            return Err(overflow(request.offset));
        }
        let mut cursor = u128::from(request.offset);
        for fragment in &bin.fragments {
            if cursor >= end {
                break;
            }
            let begin = u128::from(fragment.offset);
            let stop = (begin + fragment.bytes.len() as u128).min(u128::from(u64::MAX));
            if stop <= cursor {
                continue;
            }
            if begin > cursor {
                return Err(missing(u64::try_from(cursor).unwrap()));
            }
            let next = stop.min(end);
            let start = usize::try_from(cursor - begin)
                .map_err(|_| overflow(u64::try_from(cursor).unwrap()))?;
            let finish = usize::try_from(next - begin)
                .map_err(|_| overflow(u64::try_from(cursor).unwrap()))?;
            let part = fragment
                .bytes
                .get(start..finish)
                .ok_or_else(|| overflow(u64::try_from(cursor).unwrap()))?;
            bytes.extend_from_slice(part);
            cursor = next;
        }
        if cursor != end {
            return Err(missing(u64::try_from(cursor).unwrap()));
        }
    }
    Ok(bytes)
}

#[test]
fn actual_jpip_range_entries_missing_tails_and_getters_retain_exact_native_fields() {
    let mut cases = 0;
    for class in [0, 1, 6, 7, 8] {
        let databin = id(class, 3, 9);
        for offset in [0, 1, u64::MAX - 1, u64::MAX] {
            for length in [0, 1, 2, u64::MAX] {
                let expected = if length == 0 {
                    Err(DecodeError::malformed(
                        offset,
                        MalformedKind::InvalidJpipFragment,
                    ))
                } else if u128::from(offset) + u128::from(length) > u128::from(u64::MAX) {
                    Err(overflow(offset))
                } else {
                    Ok(range(databin, offset, length))
                };
                let result = JpipDatabinRange::new(databin, offset, length);
                assert_eq!(result, expected);
                if let Ok(value) = result {
                    assert_eq!(value.databin(), databin);
                    assert_eq!(value.offset(), offset);
                    assert_eq!(value.length(), length);
                }
                cases += 1;
            }
        }
        for length in [None, Some(0), Some(7), Some(u64::MAX)] {
            let value = JpipMissingRange {
                databin,
                offset: 7,
                length,
            };
            assert_eq!(value.databin(), databin);
            assert_eq!(value.offset(), 7);
            assert_eq!(value.length(), length);
            let mut output = vec![value];
            let additions = [value, value];
            let pointer = additions.as_ptr();
            append_missing_ranges(&mut output, &additions);
            assert_eq!(output, vec![value, value, value]);
            assert_eq!(additions.as_ptr(), pointer);
            for status in [
                JpipAvailability::Missing,
                JpipAvailability::Partial,
                JpipAvailability::Available,
            ] {
                let report = JpipAvailabilityReport {
                    status,
                    required_bytes: 19,
                    available_bytes: 23,
                    missing: output.clone(),
                };
                assert_eq!(report.status(), status);
                assert_eq!(report.required_bytes(), 19);
                assert_eq!(report.available_bytes(), 23);
                assert_eq!(report.missing_ranges(), output);
                assert_eq!(report.missing_ranges().as_ptr(), report.missing.as_ptr());
                assert_eq!(
                    report.is_available(),
                    matches!(status, JpipAvailability::Available)
                );
            }
        }
    }
    assert_eq!(cases, 80);
    let main = id(6, 3, 0);
    let cache = state(
        vec![
            bin(main, &[(0, b"ab"), (2, b"cd")], Some(4)),
            bin(id(2, 3, 0), &[(0, b"ab")], None),
            bin(id(4, 3, 0), &[], Some(0)),
        ],
        16,
        8,
        8,
    );
    let before = frame(&cache);
    for (query, offset, length) in [
        (id(7, 3, 0), 4, Some(0)),
        (id(3, 3, 0), 2, None),
        (id(5, 3, 0), 0, Some(0)),
        (id(6, 4, 0), 0, None),
    ] {
        assert_eq!(
            cache.complete_databin_missing(query),
            vec![JpipMissingRange {
                databin: query,
                offset,
                length
            }]
        );
    }
    assert_eq!(frame(&cache), before);
}

#[test]
fn actual_jpip_availability_derives_ordered_missing_work_and_all_error_frontiers_without_cache_premises()
 {
    let fragments: [(u64, &[u8]); 4] = [(0, b"ab"), (2, b"cd"), (1, b"x"), (u64::MAX, b"overflow")];
    let first = id(0, 3, 9);
    let alias = id(1, 3, 9);
    let absent = id(0, 4, 9);
    let requests = [
        vec![],
        vec![range(alias, 0, 4)],
        vec![range(first, 1, 2)],
        vec![range(absent, 0, 2)],
        vec![range(alias, 0, 3), range(first, 0, 3)],
        vec![range(absent, 0, 1), range(alias, 1, 3)],
        vec![range(alias, 0, 0)],
        vec![range(absent, 0, 0)],
        vec![range(first, u64::MAX, 1)],
    ];
    let mut cases = 0;
    for code in 0..65 {
        let parts = if code == 64 {
            Vec::new()
        } else {
            vec![
                fragments[code % 4],
                fragments[code / 4 % 4],
                fragments[code / 16 % 4],
            ]
        };
        for limit in [0, 2, 4, 8] {
            for packets in [0, 1, 4] {
                for work in [0, 1, 3, 8] {
                    let cache = state(
                        vec![
                            bin(first, &parts, Some(u64::MAX)),
                            bin(alias, &[(0, b"later")], Some(5)),
                        ],
                        limit,
                        packets,
                        work,
                    );
                    let before = frame(&cache);
                    for ranges in &requests {
                        assert_eq!(
                            cache.availability(ranges),
                            expected_availability(&cache, ranges),
                            "physical case {code}, input {limit}, packets {packets}, work {work}, ranges {ranges:?}"
                        );
                        assert_eq!(frame(&cache), before);
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 28080);
}

#[test]
fn actual_jpip_packet_bytes_keep_raw_order_repetition_saturation_priorities_and_original_cache_storage()
 {
    let fragments: [(u64, &[u8]); 4] = [(0, b"ab"), (2, b"cd"), (1, b"x"), (u64::MAX - 1, b"qr")];
    let first = id(0, 3, 9);
    let alias = id(1, 3, 9);
    let absent = id(0, 4, 9);
    let requests = [
        vec![],
        vec![range(alias, 0, 4)],
        vec![range(first, 1, 2), range(alias, 0, 2)],
        vec![range(absent, 7, 1)],
        vec![range(first, 0, 0)],
        vec![range(absent, 0, 0)],
        vec![range(alias, u64::MAX - 1, 1)],
        vec![range(alias, u64::MAX, 1)],
        vec![range(alias, 0, u64::MAX), range(absent, 0, 1)],
    ];
    let mut cases = 0;
    for code in 0..65 {
        let parts = if code == 64 {
            Vec::new()
        } else {
            vec![
                fragments[code % 4],
                fragments[code / 4 % 4],
                fragments[code / 16 % 4],
            ]
        };
        for limit in [0, 1, 4, 8] {
            let cache = state(
                vec![
                    bin(first, &parts, None),
                    bin(alias, &[(0, b"later")], Some(5)),
                ],
                limit,
                0,
                0,
            );
            let before = frame(&cache);
            for ranges in &requests {
                let packets: Vec<_> = ranges
                    .iter()
                    .map(|range| JpipPrecinctPacket {
                        range: *range,
                        layer: u16::MAX,
                    })
                    .collect();
                let result = cache.read_packet_ranges(&packets);
                assert_eq!(
                    result,
                    expected_packets(&cache, &packets),
                    "physical case {code}, limit {limit}, ranges {ranges:?}"
                );
                if let Ok(mut bytes) = result
                    && !bytes.is_empty()
                {
                    for bin in &cache.databins {
                        for fragment in &bin.fragments {
                            assert_ne!(bytes.as_ptr(), fragment.bytes.as_ptr());
                        }
                    }
                    bytes[0] ^= 0xff;
                }
                assert_eq!(frame(&cache), before);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 2340);
}
