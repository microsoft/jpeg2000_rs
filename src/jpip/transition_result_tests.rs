use super::super::cache_layout_result_tests::{bin, frame, id, storage};
use super::*;

fn error(offset: usize, kind: MalformedKind) -> DecodeError {
    DecodeError::malformed(offset as u64, kind)
}

fn word(input: &[u8], position: usize, width: usize) -> Result<&[u8], DecodeError> {
    input
        .get(position..)
        .and_then(|tail| tail.get(..width))
        .ok_or_else(|| error(position, MalformedKind::Truncated))
}

fn expected_marker(input: &[u8], position: usize) -> Result<(u16, usize, usize), DecodeError> {
    let bytes = word(input, position, 2)?;
    let marker = u16::from_be_bytes([bytes[0], bytes[1]]);
    let after_marker = position
        .checked_add(2)
        .ok_or_else(|| error(position, MalformedKind::ArithmeticOverflow))?;
    if [0xff4f, 0xff93, 0xffd9].contains(&marker) {
        return Ok((marker, after_marker, after_marker));
    }
    let bytes = word(input, after_marker, 2)?;
    let length = usize::from(u16::from_be_bytes([bytes[0], bytes[1]]));
    if length < 2 {
        return Err(error(position, MalformedKind::InvalidMarkerLength));
    }
    let end = usize::try_from(position as u128 + 2 + length as u128)
        .map_err(|_| error(0, MalformedKind::ArithmeticOverflow))?;
    if end > input.len() {
        return Err(error(position, MalformedKind::Truncated));
    }
    Ok((marker, position + 4, end))
}

#[test]
fn actual_jpip_transition_words_markers_and_plt_match_independent_extents_and_counts() {
    for high in 0..=255 {
        for low in 0..=255 {
            let input = [high, low];
            assert_eq!(read_u16_be(&input, 0), Ok(u16::from_be_bytes(input)));
        }
    }
    let inputs = [
        vec![],
        vec![0],
        vec![0xff],
        vec![0xff, 0xff],
        vec![0, 1, 0x80, 0xff],
        vec![0xff; 8],
    ];
    for input in inputs {
        let owner = storage(&input);
        for position in [
            0,
            1,
            2,
            4,
            input.len(),
            usize::MAX - 3,
            usize::MAX - 1,
            usize::MAX,
        ] {
            let expected =
                word(&input, position, 2).map(|bytes| u16::from_be_bytes([bytes[0], bytes[1]]));
            assert_eq!(read_u16_be(&input, position), expected);
            let expected = word(&input, position, 4)
                .map(|bytes| u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]));
            assert_eq!(read_u32_be(&input, position), expected);
            assert_eq!(
                marker_segment(&input, position),
                expected_marker(&input, position)
            );
        }
        assert_eq!(storage(&input), owner);
    }
    for marker in [
        0xff4f_u16, 0xff93, 0xffd9, 0xff90, 0xff58, 0xff61, 0xff64, 0, 0xabcd,
    ] {
        for length in (0..=10).chain([u16::MAX]) {
            for prefix in [0, 3] {
                let mut input = vec![0x55; prefix];
                input.extend_from_slice(&marker.to_be_bytes());
                input.extend_from_slice(&length.to_be_bytes());
                input.extend_from_slice(b"abcdefg");
                for cut in 0..=input.len() {
                    assert_eq!(
                        marker_segment(&input[..cut], prefix),
                        expected_marker(&input[..cut], prefix)
                    );
                }
            }
        }
    }
    for index in [0, 1, 127, 255] {
        for first in 0..=255 {
            for last in [None, Some(0), Some(1), Some(0x7f), Some(0x80), Some(0xff)] {
                let mut payload = vec![index, first];
                payload.extend(last);
                let expected = if payload.last().unwrap() & 0x80 != 0 {
                    Err(error(0, MalformedKind::InvalidPacketLength))
                } else {
                    Ok(
                        u64::try_from(payload[1..].iter().filter(|&&byte| byte < 128).count())
                            .unwrap(),
                    )
                };
                assert_eq!(count_plt_packets(&payload), expected);
            }
        }
    }
    assert_eq!(
        count_plt_packets(&[]),
        Err(error(0, MalformedKind::InvalidPacketLength))
    );
    assert_eq!(count_plt_packets(&[255]), Ok(0));
}

fn segment(marker: u16, payload: &[u8]) -> Vec<u8> {
    let mut bytes = marker.to_be_bytes().to_vec();
    bytes.extend_from_slice(&u16::try_from(payload.len() + 2).unwrap().to_be_bytes());
    bytes.extend_from_slice(payload);
    bytes
}

fn part(tile: u16, number: u8, declared: u32, segments: &[Vec<u8>]) -> Vec<u8> {
    let mut bytes = vec![0xff, 0x90, 0, 10];
    bytes.extend_from_slice(&tile.to_be_bytes());
    bytes.extend_from_slice(&declared.to_be_bytes());
    bytes.extend_from_slice(&[number, 99]);
    for segment in segments {
        bytes.extend_from_slice(segment);
    }
    bytes.extend_from_slice(&[0xff, 0x93]);
    bytes
}

fn transition(
    tile: u16,
    number: u8,
    packets: Option<u64>,
    functional: bool,
    declared: u32,
    bytes: &[u8],
) -> JpipTilePartTransition {
    JpipTilePartTransition {
        tile,
        tile_part: number,
        packet_count: packets,
        data_length: if declared == 0 {
            None
        } else {
            u64::from(declared).checked_sub(bytes.len() as u64)
        },
        functional,
        header: bytes.to_vec(),
    }
}

#[test]
fn actual_jpip_raw_transitions_derive_all_fields_owned_headers_and_exact_emitted_cut_errors() {
    let variants = [
        (vec![], None, false),
        (
            vec![segment(0xff64, b"comment"), segment(0xff61, &[4])],
            None,
            false,
        ),
        (vec![segment(0xff52, &[9])], None, true),
        (vec![segment(0xff58, &[0, 0, 0x80, 1])], Some(2), false),
        (
            vec![segment(0xff58, &[0, 1]), segment(0xff58, &[1, 0, 0])],
            Some(3),
            false,
        ),
        (
            vec![
                segment(0xff58, &[0, 1]),
                segment(0xff52, &[7]),
                segment(0xff64, &[8]),
            ],
            Some(1),
            true,
        ),
    ];
    for tile in [0, 1, 255, 256, u16::MAX] {
        for number in [0, 1, 255] {
            for declared in [0, 1, 13, 14, 1000, u32::MAX] {
                for (segments, packets, functional) in &variants {
                    let input = part(tile, number, declared, segments);
                    let owner = storage(&input);
                    let actual = parse_tile_part_transitions(&input, tile).unwrap();
                    assert_eq!(
                        actual,
                        vec![transition(
                            tile,
                            number,
                            *packets,
                            *functional,
                            declared,
                            &input
                        )]
                    );
                    let value = &actual[0];
                    assert_eq!(
                        (
                            value.tile(),
                            value.tile_part(),
                            value.packet_count(),
                            value.data_length(),
                            value.has_functional_change()
                        ),
                        (
                            tile,
                            number,
                            *packets,
                            transition(tile, number, *packets, *functional, declared, &input)
                                .data_length,
                            *functional
                        )
                    );
                    assert_eq!(value.header_bytes(), input);
                    assert_eq!(value.header_bytes().as_ptr(), value.header.as_ptr());
                    assert_ne!(value.header_bytes().as_ptr(), input.as_ptr());
                    assert_eq!(storage(&input), owner);
                }
            }
        }
    }
    let segments = [
        segment(0xff58, &[0, 0, 1]),
        segment(0xff64, b"x"),
        segment(0xff52, &[7]),
    ];
    let input = part(7, 9, 100, &segments);
    let mut spans = Vec::new();
    let mut start = 12;
    for segment in &segments {
        spans.push((start, start + segment.len()));
        start += segment.len();
    }
    for cut in 0..input.len() {
        let expected = if cut == 0 {
            Ok(vec![JpipTilePartTransition {
                tile: 7,
                tile_part: 0,
                packet_count: None,
                data_length: None,
                functional: false,
                header: Vec::new(),
            }])
        } else {
            let (offset, kind) = if cut == 1 {
                (0, MalformedKind::Truncated)
            } else if cut < 4 {
                (2, MalformedKind::Truncated)
            } else if cut < 12 {
                (0, MalformedKind::Truncated)
            } else if let Some(&(begin, _)) =
                spans.iter().find(|&&(begin, end)| begin < cut && cut < end)
            {
                (
                    if cut == begin + 2 || cut == begin + 3 {
                        begin + 2
                    } else {
                        begin
                    },
                    MalformedKind::Truncated,
                )
            } else if cut == input.len() - 1 {
                (start, MalformedKind::Truncated)
            } else {
                (cut, MalformedKind::MissingRequiredStructure)
            };
            Err(error(offset, kind))
        };
        assert_eq!(
            parse_tile_part_transitions(&input[..cut], 7),
            expected,
            "cut {cut}"
        );
    }
}

#[test]
fn actual_jpip_raw_transition_admission_keeps_native_plt_sod_psot_and_first_error_differences() {
    for input in [
        vec![],
        vec![0xff, 0x93, 0x7f],
        segment(0xff64, b"only comment"),
        segment(0xff58, &[255, 0]),
    ] {
        let (packets, functional) = if input.get(..2) == Some(&[0xff, 0x58]) {
            (Some(1), false)
        } else {
            (None, false)
        };
        assert_eq!(
            parse_tile_part_transitions(&input, 42),
            Ok(vec![JpipTilePartTransition {
                tile: 42,
                tile_part: 0,
                packet_count: packets,
                data_length: None,
                functional,
                header: input,
            }])
        );
    }
    assert_eq!(
        parse_tile_part_transitions(&segment(0xff58, &[]), 0),
        Err(error(0, MalformedKind::InvalidPacketLength))
    );
    for (payload, offset) in [(&[][..], 12), (&[1, 0x80][..], 12), (&[0, 0x80][..], 0)] {
        assert_eq!(
            parse_tile_part_transitions(&part(2, 0, 100, &[segment(0xff58, payload)]), 2),
            Err(error(offset, MalformedKind::InvalidPacketLength))
        );
    }
    let mut first = part(2, 7, 0, &[]);
    let second = part(2, 3, 1, &[segment(0xff52, &[])]);
    first.extend_from_slice(&second);
    assert_eq!(
        parse_tile_part_transitions(&first, 2),
        Err(error(0, MalformedKind::InvalidTilePart))
    );
    let first = part(2, 7, 1, &[]);
    let input = [first.clone(), second.clone()].concat();
    assert_eq!(
        parse_tile_part_transitions(&input, 2),
        Ok(vec![
            transition(2, 7, None, false, 1, &first),
            transition(2, 3, None, true, 1, &second),
        ])
    );
    assert_eq!(
        parse_tile_part_transitions(&input, 3),
        Err(error(0, MalformedKind::InvalidTilePart))
    );
    let segments: Vec<_> = (0..=255)
        .map(|index| segment(0xff58, &[index, 0]))
        .collect();
    let input = part(2, 0, 10000, &segments);
    assert_eq!(
        parse_tile_part_transitions(&input, 2).unwrap()[0].packet_count(),
        Some(256)
    );
    let mut repeated = segments;
    repeated.push(segment(0xff58, &[0, 0]));
    assert_eq!(
        parse_tile_part_transitions(&part(2, 0, 10000, &repeated), 2),
        Err(error(12 + 256 * 6, MalformedKind::InvalidPacketLength))
    );
}

#[test]
fn actual_jpip_public_transition_reports_preserve_physical_cache_needs_getters_and_native_storage()
{
    for stream in [0, 3, u64::MAX] {
        for tile in [0, 1, u16::MAX] {
            let requested = id(2, stream, u64::from(tile));
            let a = part(tile, 7, 1, &[]);
            let b = part(tile, 3, 1, &[segment(0xff52, &[7])]);
            let c = part(tile, 4, 100, &[segment(0xff52, &[8])]);
            let d = part(tile, 9, 1, &[segment(0xff52, &[9])]);
            let bytes = [a.clone(), b.clone(), c.clone(), d.clone()].concat();
            let expected_transitions = vec![
                transition(tile, 7, None, false, 1, &a),
                transition(tile, 3, None, true, 1, &b),
                transition(tile, 4, None, true, 100, &c),
                transition(tile, 9, None, true, 1, &d),
            ];
            let needs = vec![
                JpipSemanticNeed {
                    kind: JpipSemanticNeedKind::TilePartTransition,
                    identifier: (u64::from(tile) << 8) | 3,
                },
                JpipSemanticNeed {
                    kind: JpipSemanticNeedKind::TilePartTransition,
                    identifier: (u64::from(tile) << 8) | 9,
                },
            ];
            let partial = JpipTilePartTransitionReport {
                status: JpipAvailability::Partial,
                transitions: expected_transitions,
                needs,
                missing: Vec::new(),
            };
            let missing = |offset, length| JpipTilePartTransitionReport {
                status: JpipAvailability::Missing,
                transitions: Vec::new(),
                needs: vec![JpipSemanticNeed {
                    kind: JpipSemanticNeedKind::TilePartTransition,
                    identifier: u64::from(tile),
                }],
                missing: vec![JpipMissingRange {
                    databin: requested,
                    offset,
                    length,
                }],
            };
            let cases = [
                (vec![], Ok(missing(0, None))),
                (
                    vec![bin(requested, &[(0, &bytes)], None)],
                    Ok(missing(bytes.len() as u64, None)),
                ),
                (
                    vec![bin(requested, &[(0, &bytes)], Some(bytes.len() as u64 + 1))],
                    Ok(missing(bytes.len() as u64, Some(1))),
                ),
                (
                    vec![bin(requested, &[(0, &bytes)], Some(bytes.len() as u64))],
                    Ok(partial),
                ),
                (
                    vec![bin(
                        requested,
                        &[(0, &bytes[..2]), (2, &bytes[2..])],
                        Some(bytes.len() as u64),
                    )],
                    Err(error(2, MalformedKind::Truncated)),
                ),
                (
                    vec![bin(
                        requested,
                        &[(2, &bytes[2..]), (0, &bytes[..2])],
                        Some(bytes.len() as u64),
                    )],
                    Ok(missing(2, Some(bytes.len() as u64 - 2))),
                ),
                (
                    vec![bin(requested, &[], Some(0))],
                    Ok(JpipTilePartTransitionReport {
                        status: JpipAvailability::Available,
                        transitions: vec![JpipTilePartTransition {
                            tile,
                            tile_part: 0,
                            packet_count: None,
                            data_length: None,
                            functional: false,
                            header: Vec::new(),
                        }],
                        needs: Vec::new(),
                        missing: Vec::new(),
                    }),
                ),
                (
                    vec![
                        bin(
                            id(3, stream, u64::from(tile)),
                            &[(0, &a)],
                            Some(a.len() as u64),
                        ),
                        bin(requested, &[(0, &bytes)], Some(bytes.len() as u64)),
                    ],
                    Ok(JpipTilePartTransitionReport {
                        status: JpipAvailability::Available,
                        transitions: vec![transition(tile, 7, None, false, 1, &a)],
                        needs: Vec::new(),
                        missing: Vec::new(),
                    }),
                ),
            ];
            for (bins, expected) in cases {
                for input in [1, 128, 1 << 31] {
                    let cache = DatabinCache {
                        limits: ResourceLimits::HARDENED
                            .with_maximum_input_bytes(input)
                            .unwrap(),
                        databins: bins.clone(),
                        stored_bytes: u64::MAX,
                        accepted_fragments: u64::MAX,
                    };
                    let before = frame(&cache);
                    let actual = cache.tile_part_transitions(stream, tile);
                    assert_eq!(actual, expected);
                    if let Ok(report) = actual {
                        assert_eq!(report.status(), report.status);
                        assert_eq!(report.transitions(), report.transitions);
                        assert_eq!(report.transitions().as_ptr(), report.transitions.as_ptr());
                        assert_eq!(report.semantic_needs(), report.needs);
                        assert_eq!(report.semantic_needs().as_ptr(), report.needs.as_ptr());
                        assert_eq!(report.missing_ranges(), report.missing);
                        assert_eq!(report.missing_ranges().as_ptr(), report.missing.as_ptr());
                        for need in report.semantic_needs() {
                            assert_eq!(
                                (need.kind(), need.identifier()),
                                (need.kind, need.identifier)
                            );
                        }
                        for transition in report.transitions() {
                            assert_eq!(
                                transition.header_bytes().as_ptr(),
                                transition.header.as_ptr()
                            );
                        }
                    }
                    assert_eq!(frame(&cache), before);
                }
            }
        }
    }
}
