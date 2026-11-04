use super::image_header::component_depths_uniform;
use super::reader::{is_allowed_main_header, is_allowed_tile_header, is_known_segment_marker};
use super::*;
use crate::tier1::SubbandOrientation;

fn assert_tile_header_admission_case<'a>(
    input: &'a [u8],
    limits: &'a ResourceLimits,
    state: PacketAdmissionState,
) -> Result<Option<Segment<'a>>, DecodeError> {
    let raw = || Parser {
        input,
        limits,
        position: state.position,
        work_units: state.work,
        packet_length_bytes: state.header_bytes,
        packet_lengths: state.packet_count,
    };
    let mut reference = raw();
    // Replay the original tile loop prefix using its separately proved reader leaves.
    let expected = (|| {
        let marker = reference.peek_marker()?;
        if marker == SOD {
            reference.expect_standalone(SOD)?;
            return Ok(None);
        }
        if matches!(marker, SOC | SIZ | SOT | EOC) {
            return Err(reference.malformed_here(MalformedKind::InvalidMarkerOrder));
        }
        let segment = reference.read_segment()?;
        if !is_known_segment_marker(segment.marker) {
            return Err(reference.malformed_at(segment.offset, MalformedKind::InvalidMarker));
        }
        if !is_allowed_tile_header(segment.marker) {
            return Err(reference.malformed_at(segment.offset, MalformedKind::InvalidMarkerOrder));
        }
        Ok(Some(segment))
    })();
    let mut actual = raw();
    let result = actual.read_tile_header_segment();
    assert_eq!(result, expected);
    assert_packet_admission_state(
        &actual,
        PacketAdmissionState {
            position: reference.position,
            work: reference.work_units,
            header_bytes: state.header_bytes,
            packet_count: state.packet_count,
        },
        input,
        limits,
    );
    if let Ok(Some(segment)) = result {
        assert!(core::ptr::eq(
            segment.payload.as_ptr(),
            input[segment.offset + 4..].as_ptr(),
        ));
    }
    result
}

#[test]
fn actual_tile_header_admission_preserves_every_marker_and_length_word() {
    let base = ResourceLimits::HARDENED;
    let mut cases = 0;
    for limits in [
        base.with_maximum_work_units(0).unwrap(),
        base.with_maximum_work_units(1).unwrap(),
        base,
    ] {
        for field in [2, 4] {
            let mut input = [0x12, 0x34, 0xff, 0x52, 0, 4, 0x56, 0x78];
            for value in 0..=u16::MAX {
                input[field..field + 2].copy_from_slice(&value.to_be_bytes());
                let _ = assert_tile_header_admission_case(
                    &input,
                    &limits,
                    PacketAdmissionState {
                        position: 2,
                        work: 0,
                        header_bytes: u64::MAX,
                        packet_count: 31,
                    },
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 393_216);
}

#[test]
fn actual_tile_header_admission_preserves_raw_states_and_partial_reader_commits() {
    let base = ResourceLimits::HARDENED;
    let mut cases = 0;
    for limits in [
        base,
        base.with_maximum_work_units(0).unwrap(),
        base.with_maximum_work_units(1).unwrap(),
        base.with_maximum_input_bytes(0).unwrap(),
    ] {
        for marker in [
            SOC, SIZ, SOT, SOD, EOC, COD, COM, PLT, PPT, 0xff70, 0xff00, 0xffff,
        ] {
            let mut input = vec![0x31, 0x41];
            input.extend(marker.to_be_bytes());
            input.extend([0, 5, 0x59, 0x26, 0x53]);
            for end in 0..=input.len() {
                for position in [0, 2, end, end + 1, usize::MAX - 1, usize::MAX] {
                    for work in [0, 1, base.maximum_work_units(), u64::MAX - 1, u64::MAX] {
                        for (header_bytes, packet_count) in [(0, 0), (17, u64::MAX), (u64::MAX, 19)]
                        {
                            let _ = assert_tile_header_admission_case(
                                &input[..end],
                                &limits,
                                PacketAdmissionState {
                                    position,
                                    work,
                                    header_bytes,
                                    packet_count,
                                },
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 43_200);
}

#[test]
fn actual_tile_header_admission_keeps_sod_commit_and_boundary_error_priority() {
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let input = [0x31, 0x41, 0xff, 0x93, 0, 1];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = 2;
    assert_eq!(
        parser.read_tile_header_segment(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 0,
            actual: 1
        }),
    );
    assert_eq!((parser.position, parser.work_units), (4, 1));
    for marker in [SOC, SIZ, SOT, EOC] {
        let mut input = input;
        input[2..4].copy_from_slice(&marker.to_be_bytes());
        let mut parser = new_parser(&input, &limits).unwrap();
        parser.position = 2;
        assert_eq!(
            parser.read_tile_header_segment(),
            Err(input_error_literal(2, MalformedKind::InvalidMarkerOrder)),
        );
        assert_eq!((parser.position, parser.work_units), (2, 0));
    }
    let limits = ResourceLimits::HARDENED;
    for (marker, kind) in [
        (0xff70_u16, MalformedKind::InvalidMarker),
        (CAP, MalformedKind::InvalidMarkerOrder),
    ] {
        let mut input = vec![0x31, 0x41];
        input.extend(segment(marker, &[0x59, 0x26, 0x53]));
        let mut parser = new_parser(&input, &limits).unwrap();
        parser.position = 2;
        assert_eq!(
            parser.read_tile_header_segment(),
            Err(input_error_literal(2, kind))
        );
        assert_eq!((parser.position, parser.work_units), (9, 1));
    }
}

#[test]
fn actual_tile_header_admission_joins_reader_dispatch_and_pre_sod_metadata_windows() {
    let limits = ResourceLimits::HARDENED;
    let tile_headers = [
        segment(COM, &[0, 0, 0x59]),
        baseline_headers()[0].clone(),
        segment(COC, &[0, 0, 0, 2, 2, 0, 1]),
        baseline_headers()[1].clone(),
        segment(QCC, &[0, 0, 0]),
        segment(PLT, &[0, 3]),
        segment(PPT, &[0, 0xab]),
    ];
    let input = codestream_with_headers(1, &baseline_headers(), &tile_headers, &[0x12, 0x34]);
    let layout = parse_layout(&input, &limits).unwrap();
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.parse_layout_prologue().unwrap();
    let mut count = 1;
    while parser
        .read_main_header_segment(&mut count)
        .unwrap()
        .is_some()
    {}
    parser.read_sot(1).unwrap();
    let start = parser.position;
    let mut markers = Vec::new();
    let end = loop {
        let before = parser.position;
        let work = parser.work_units;
        match parser.read_tile_header_segment().unwrap() {
            Some(segment) => markers.push(segment.marker),
            None => {
                assert_eq!((parser.position, parser.work_units), (before + 2, work + 1));
                break before;
            }
        }
    };
    assert_eq!(markers, [COM, COD, COC, QCD, QCC, PLT, PPT]);
    assert_eq!(&input[end..end + 2], &SOD.to_be_bytes());
    let tile = &layout.tile_parts[0];
    assert_eq!(tile.data, &[0x12, 0x34]);
    assert!(tile.has_functional_header_marker);
    assert_eq!(
        tile.packet_lengths.source,
        PacketLengthSource::Plt(&input[start..end])
    );
    assert_eq!(
        tile.packed_packet_headers.source,
        PackedPacketHeaderSource::MarkerSegments {
            header: &input[start..end],
            marker: PPT,
            logical_start: 0,
        },
    );
    assert!(core::ptr::eq(tile.data.as_ptr(), input[end + 2..].as_ptr()));
}

fn assert_component_segment_admission_case(
    payload: &[u8],
    components: u16,
    invalid_kind: MalformedKind,
    occupied: bool,
) {
    let input = [0x31, 0x41];
    let limits = ResourceLimits::HARDENED;
    let parser = Parser {
        input: &input,
        limits: &limits,
        position: usize::MAX,
        work_units: u64::MAX,
        packet_length_bytes: 19,
        packet_lengths: u64::MAX - 1,
    };
    let value = Segment {
        marker: 0xff70,
        offset: usize::MAX,
        payload,
    };
    let mut actual = core::array::from_fn(|index| {
        (index % 3 == 0).then_some(Segment {
            marker: QCD,
            offset: index,
            payload: &input,
        })
    });
    let component = if components < 257 {
        payload.first().map(|byte| u16::from(*byte))
    } else {
        payload
            .get(..2)
            .map(|bytes| u16::from_be_bytes([bytes[0], bytes[1]]))
    };
    if let Some(component) = component
        && let Some(slot) = actual.get_mut(usize::from(component))
    {
        *slot = occupied.then_some(Segment {
            marker: COM,
            offset: 23,
            payload: &input,
        });
    }
    let mut expected = actual;
    let result = match component {
        None => Err(input_error_literal(
            value.offset,
            MalformedKind::InvalidMarkerLength,
        )),
        Some(component) if component >= components || usize::from(component) >= MAX_COMPONENTS => {
            Err(input_error_literal(value.offset, invalid_kind))
        }
        Some(component) if expected[usize::from(component)].is_some() => Err(input_error_literal(
            value.offset,
            MalformedKind::InvalidMarkerOrder,
        )),
        Some(component) => {
            expected[usize::from(component)] = Some(value);
            Ok(())
        }
    };
    assert_eq!(
        parser.record_component_segment(value, components, invalid_kind, &mut actual),
        result
    );
    assert_eq!(actual, expected);
    for (actual, expected) in actual.iter().zip(expected) {
        if let (Some(actual), Some(expected)) = (actual, expected) {
            assert!(core::ptr::eq(
                actual.payload.as_ptr(),
                expected.payload.as_ptr()
            ));
        }
    }
    assert_packet_admission_state(
        &parser,
        PacketAdmissionState {
            position: usize::MAX,
            work: u64::MAX,
            header_bytes: 19,
            packet_count: u64::MAX - 1,
        },
        &input,
        &limits,
    );
}

#[test]
fn actual_component_segment_admission_preserves_raw_indexes_slots_and_all_frames() {
    let mut cases = 0;
    for kind in [
        MalformedKind::InvalidCodingStyle,
        MalformedKind::InvalidQuantization,
    ] {
        for occupied in [false, true] {
            for components in [0, 1, 63, 64, 65, 255, 256, 257, 258, u16::MAX] {
                assert_component_segment_admission_case(&[], components, kind, occupied);
                cases += 1;
                for byte in 0..=u8::MAX {
                    assert_component_segment_admission_case(&[byte], components, kind, occupied);
                    cases += 1;
                }
            }
            for components in [257, u16::MAX] {
                for word in 0..=u16::MAX {
                    assert_component_segment_admission_case(
                        &word.to_be_bytes(),
                        components,
                        kind,
                        occupied,
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 534_568);
}

#[test]
fn actual_component_segment_admission_keeps_earlier_slots_and_first_error() {
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let first = Segment {
        marker: COC,
        offset: 17,
        payload: &[1, 0xff],
    };
    let mut slots = [None; MAX_COMPONENTS];
    let kind = MalformedKind::InvalidCodingStyle;
    assert_eq!(
        parser.record_component_segment(first, 2, kind, &mut slots),
        Ok(())
    );
    let committed = slots;
    for (payload, components, error) in [
        (&[][..], 2, MalformedKind::InvalidMarkerLength),
        (&[1][..], 1, kind),
        (&[1][..], 257, MalformedKind::InvalidMarkerLength),
        (&[64][..], 65, kind),
        (&[1][..], 2, MalformedKind::InvalidMarkerOrder),
    ] {
        let next = Segment {
            offset: 29,
            payload,
            ..first
        };
        assert_eq!(
            parser.record_component_segment(next, components, kind, &mut slots),
            Err(input_error_literal(29, error)),
        );
        assert_eq!(slots, committed);
    }
    let next = Segment {
        payload: &[0, 0xaa],
        ..first
    };
    assert_eq!(
        parser.record_component_segment(next, 2, kind, &mut slots),
        Ok(())
    );
    assert_eq!(slots[0], Some(next));
    assert_eq!(slots[1], Some(first));
    assert!(slots[2..].iter().all(Option::is_none));
}

#[test]
fn actual_component_segment_admission_joins_all_four_real_header_branches() {
    let limits = ResourceLimits::HARDENED;
    for (marker, payload, kind) in [
        (
            COC,
            &[0, 0, 0, 2, 2, 0, 1][..],
            MalformedKind::InvalidCodingStyle,
        ),
        (QCC, &[0, 0, 0][..], MalformedKind::InvalidQuantization),
    ] {
        for tile in [false, true] {
            let make = |segments: &[Vec<u8>]| {
                let mut main = baseline_headers().to_vec();
                if tile {
                    codestream_with_headers(1, &main, segments, &[])
                } else {
                    main.extend_from_slice(segments);
                    codestream_with_headers(1, &main, &[], &[])
                }
            };
            let valid = segment(marker, payload);
            let input = make(core::slice::from_ref(&valid));
            let layout = parse_layout(&input, &limits).unwrap();
            assert_eq!(layout.tile_parts.len(), 1);
            let duplicate = segment(marker, &[0]);
            let input = make(&[valid.clone(), duplicate]);
            let offset = input
                .windows(2)
                .enumerate()
                .filter(|(_, bytes)| *bytes == marker.to_be_bytes())
                .nth(1)
                .unwrap()
                .0;
            assert_eq!(
                parse_layout(&input, &limits),
                Err(input_error_literal(
                    offset,
                    MalformedKind::InvalidMarkerOrder
                )),
            );
            for (bytes, error) in [
                (&[][..], MalformedKind::InvalidMarkerLength),
                (&[1][..], kind),
            ] {
                let input = make(&[segment(marker, bytes)]);
                let offset = input
                    .windows(2)
                    .position(|bytes| bytes == marker.to_be_bytes())
                    .unwrap();
                assert_eq!(
                    parse_layout(&input, &limits),
                    Err(input_error_literal(offset, error)),
                );
            }
        }
    }
}

fn assert_main_header_admission_case<'a>(
    input: &'a [u8],
    limits: &'a ResourceLimits,
    state: PacketAdmissionState,
    count: u64,
) -> Result<Option<Segment<'a>>, DecodeError> {
    let raw = || Parser {
        input,
        limits,
        position: state.position,
        work_units: state.work,
        packet_length_bytes: state.header_bytes,
        packet_lengths: state.packet_count,
    };
    let mut reference = raw();
    let mut expected_count = count;
    // Replay the original loop prefix, including its fallible checked counter update.
    let expected = (|| {
        let marker = reference.peek_marker()?;
        if marker == SOT {
            return Ok(None);
        }
        if matches!(marker, SOC | SOD | EOC) {
            return Err(reference.malformed_here(MalformedKind::InvalidMarkerOrder));
        }
        let segment = reference.read_segment()?;
        expected_count = expected_count
            .checked_add(1)
            .ok_or_else(|| reference.malformed_here(MalformedKind::ArithmeticOverflow))?;
        if !is_known_segment_marker(segment.marker) {
            return Err(reference.malformed_at(segment.offset, MalformedKind::InvalidMarker));
        }
        if !is_allowed_main_header(segment.marker) {
            return Err(reference.malformed_at(segment.offset, MalformedKind::InvalidMarkerOrder));
        }
        Ok(Some(segment))
    })();
    let mut actual = raw();
    let mut actual_count = count;
    let result = actual.read_main_header_segment(&mut actual_count);
    assert_eq!(result, expected);
    assert_eq!(actual_count, expected_count);
    assert_packet_admission_state(
        &actual,
        PacketAdmissionState {
            position: reference.position,
            work: reference.work_units,
            header_bytes: state.header_bytes,
            packet_count: state.packet_count,
        },
        input,
        limits,
    );
    if let Ok(Some(segment)) = result {
        assert_eq!(
            segment.payload.as_ptr(),
            input[segment.offset + 4..].as_ptr()
        );
    }
    result
}

#[test]
fn actual_main_header_admission_preserves_every_marker_length_and_counter_order() {
    let base = ResourceLimits::HARDENED;
    let mut cases = 0;
    for limits in [
        base.with_maximum_work_units(0).unwrap(),
        base.with_maximum_work_units(1).unwrap(),
        base,
    ] {
        for count in [0, u64::MAX - 1, u64::MAX] {
            for field in [2, 4] {
                let mut input = [0x12, 0x34, 0xff, 0x52, 0, 4, 0x56, 0x78];
                for value in 0..=u16::MAX {
                    input[field..field + 2].copy_from_slice(&value.to_be_bytes());
                    let _ = assert_main_header_admission_case(
                        &input,
                        &limits,
                        PacketAdmissionState {
                            position: 2,
                            work: 0,
                            header_bytes: u64::MAX,
                            packet_count: 31,
                        },
                        count,
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 1_179_648);
}

#[test]
fn actual_main_header_admission_preserves_arbitrary_reader_states_and_partial_commits() {
    let base = ResourceLimits::HARDENED;
    let mut cases = 0;
    for limits in [
        base,
        base.with_maximum_work_units(0).unwrap(),
        base.with_maximum_work_units(1).unwrap(),
        base.with_maximum_input_bytes(0).unwrap(),
    ] {
        for marker in [
            SOC, SOT, SOD, EOC, SIZ, COD, 0xff58, 0xff61, 0xff00, 0xffff, 0xff70,
        ] {
            let mut input = vec![0x31, 0x41];
            input.extend(marker.to_be_bytes());
            input.extend([0, 5, 0x59, 0x26, 0x53]);
            for end in 0..=input.len() {
                for position in [0, 2, end, end + 1, usize::MAX - 1, usize::MAX] {
                    for work in [0, 1, base.maximum_work_units(), u64::MAX - 1, u64::MAX] {
                        for count in [0, u64::MAX - 1, u64::MAX] {
                            for (header_bytes, packet_count) in
                                [(0, 0), (17, u64::MAX), (u64::MAX, 19)]
                            {
                                let _ = assert_main_header_admission_case(
                                    &input[..end],
                                    &limits,
                                    PacketAdmissionState {
                                        position,
                                        work,
                                        header_bytes,
                                        packet_count,
                                    },
                                    count,
                                );
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 118_800);
}

#[test]
fn actual_main_header_admission_error_frontiers_are_not_normalized() {
    let limits = ResourceLimits::HARDENED;
    let input = [0x31, 0x41, 0xff, 0x70, 0, 5, 0x59, 0x26, 0x53];
    let mut siz_input = input;
    siz_input[2..4].copy_from_slice(&SIZ.to_be_bytes());
    let boundary_inputs = [SOC, SOT, SOD, EOC].map(|marker| {
        let mut bytes = input;
        bytes[2..4].copy_from_slice(&marker.to_be_bytes());
        (marker, bytes)
    });
    let mut parser = Parser {
        input: &input,
        limits: &limits,
        position: 2,
        work_units: 7,
        packet_length_bytes: 19,
        packet_lengths: u64::MAX,
    };
    let mut count = u64::MAX;
    assert_eq!(
        parser.read_main_header_segment(&mut count),
        Err(DecodeError::MalformedInput {
            offset: 9,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    assert_eq!(
        (parser.position, parser.work_units, count),
        (9, 8, u64::MAX)
    );
    count = 11;
    parser.position = 2;
    assert_eq!(
        parser.read_main_header_segment(&mut count),
        Err(DecodeError::MalformedInput {
            offset: 2,
            kind: MalformedKind::InvalidMarker
        })
    );
    assert_eq!((parser.position, parser.work_units, count), (9, 9, 12));
    parser.input = &siz_input;
    parser.position = 2;
    assert_eq!(
        parser.read_main_header_segment(&mut count),
        Err(DecodeError::MalformedInput {
            offset: 2,
            kind: MalformedKind::InvalidMarkerOrder
        })
    );
    assert_eq!((parser.position, parser.work_units, count), (9, 10, 13));
    for (marker, input) in &boundary_inputs {
        parser.input = input;
        parser.position = 2;
        let before = (parser.position, parser.work_units, count);
        let result = parser.read_main_header_segment(&mut count);
        if *marker == SOT {
            assert_eq!(result, Ok(None));
        } else {
            assert_eq!(
                result,
                Err(DecodeError::MalformedInput {
                    offset: 2,
                    kind: MalformedKind::InvalidMarkerOrder
                })
            );
        }
        assert_eq!((parser.position, parser.work_units, count), before);
    }
    assert_eq!(
        (parser.packet_length_bytes, parser.packet_lengths),
        (19, u64::MAX)
    );
}

#[test]
fn actual_main_header_admission_consumes_real_prologue_and_preserves_layout_dispatch() {
    let limits = ResourceLimits::HARDENED;
    let input = codestream_with_headers(1, &baseline_headers(), &[], &[]);
    let layout = parse_layout(&input, &limits).unwrap();
    let mut parser = new_parser(&input, &limits).unwrap();
    let (size, _, start) = parser.parse_layout_prologue().unwrap();
    assert_eq!(size, layout.info.image_size);
    assert_eq!(parser.position, start);
    let mut count = 1;
    let mut markers = Vec::new();
    while let Some(segment) = parser.read_main_header_segment(&mut count).unwrap() {
        markers.push(segment.marker);
    }
    assert_eq!(markers, [COD, QCD]);
    assert_eq!(count, layout.info.main_header_segments);
    assert_eq!(count, 3);
    let sot_position = parser.position;
    let work = parser.work_units;
    assert_eq!(parser.read_main_header_segment(&mut count), Ok(None));
    assert_eq!(
        (parser.position, parser.work_units, count),
        (sot_position, work, 3)
    );
    assert_eq!(parser.read_sot(1).unwrap().start, sot_position);
    assert_eq!(parser.position, sot_position + 12);
    assert_eq!(parser.work_units, work + 1);
}

fn assert_layout_prologue_case(
    input: &[u8],
    limits: &ResourceLimits,
    state: PacketAdmissionState,
) -> Result<(ImageSize, u16, usize), DecodeError> {
    let raw = || Parser {
        input,
        limits,
        position: state.position,
        work_units: state.work,
        packet_length_bytes: state.header_bytes,
        packet_lengths: state.packet_count,
    };
    let mut reference = raw();
    // Replay the pre-extraction prologue with the separately tested reader/SIZ leaves.
    let expected = (|| {
        reference.expect_standalone(SOC)?;
        let siz = reference.read_segment()?;
        if siz.marker != SIZ {
            return Err(DecodeError::MalformedInput {
                offset: siz.offset as u64,
                kind: MalformedKind::InvalidMarkerOrder,
            });
        }
        let (size, r_siz) = reference.parse_siz(siz)?;
        Ok((size, r_siz, reference.position))
    })();
    let mut actual = raw();
    assert_eq!(actual.parse_layout_prologue(), expected);
    assert_packet_admission_state(
        &actual,
        PacketAdmissionState {
            position: reference.position,
            work: reference.work_units,
            header_bytes: state.header_bytes,
            packet_count: state.packet_count,
        },
        input,
        limits,
    );
    expected
}

#[test]
fn actual_layout_prologue_preserves_all_marker_and_length_contexts() {
    let base = ResourceLimits::HARDENED;
    let limits = [
        base.with_maximum_work_units(0).unwrap(),
        base.with_maximum_work_units(1).unwrap(),
        base.with_maximum_work_units(2).unwrap(),
        base,
    ];
    let mut input = SOC.to_be_bytes().to_vec();
    input.extend(siz());
    input.extend([0xff, 0x52, 0, 2]);
    let mut cases = 0;
    for limits in &limits {
        for field in [0, 2, 4] {
            let original = [input[field], input[field + 1]];
            for value in 0..=u16::MAX {
                input[field..field + 2].copy_from_slice(&value.to_be_bytes());
                let _ = assert_layout_prologue_case(
                    &input,
                    limits,
                    PacketAdmissionState {
                        position: 0,
                        work: 0,
                        header_bytes: u64::MAX,
                        packet_count: 17,
                    },
                );
                cases += 1;
            }
            input[field..field + 2].copy_from_slice(&original);
        }
    }
    assert_eq!(cases, 786_432);
}

#[test]
fn actual_layout_prologue_preserves_arbitrary_states_prefixes_and_error_commits() {
    let base = ResourceLimits::HARDENED;
    let limits = [
        base,
        base.with_maximum_work_units(0).unwrap(),
        base.with_maximum_work_units(1).unwrap(),
        base.with_maximum_work_units(2).unwrap(),
        base.with_maximum_input_bytes(0).unwrap(),
    ];
    let mut input = vec![0x31, 0x41, 0x59];
    input.extend(SOC.to_be_bytes());
    input.extend(siz());
    input.extend([0xff, 0, 0xff]);
    let mut cases = 0;
    for limits in &limits {
        for end in 0..=input.len() {
            for position in [0, 1, 3, 5, end, end + 1, usize::MAX - 1, usize::MAX] {
                for work in [0, 1, 2, base.maximum_work_units(), u64::MAX - 1, u64::MAX] {
                    for (header_bytes, packet_count) in [(0, 0), (17, u64::MAX), (u64::MAX, 19)] {
                        let _ = assert_layout_prologue_case(
                            &input[..end],
                            limits,
                            PacketAdmissionState {
                                position,
                                work,
                                header_bytes,
                                packet_count,
                            },
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 37_440);

    let input = [0xff, 0x4f, 0xff, 0x52, 0, 2];
    let mut parser = Parser {
        input: &input,
        limits: &limits[1],
        position: 0,
        work_units: 0,
        packet_length_bytes: 19,
        packet_lengths: u64::MAX,
    };
    assert_eq!(
        parser.parse_layout_prologue(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 0,
            actual: 1,
        })
    );
    assert_eq!((parser.position, parser.work_units), (2, 1));
    parser.limits = &limits[2];
    parser.position = 0;
    parser.work_units = 0;
    assert_eq!(
        parser.parse_layout_prologue(),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2,
        })
    );
    assert_eq!((parser.position, parser.work_units), (2, 2));
    parser.limits = &base;
    parser.position = 0;
    parser.work_units = 0;
    assert_eq!(
        parser.parse_layout_prologue(),
        Err(DecodeError::MalformedInput {
            offset: 2,
            kind: MalformedKind::InvalidMarkerOrder,
        })
    );
    assert_eq!((parser.position, parser.work_units), (6, 2));
    assert_eq!(
        (parser.packet_length_bytes, parser.packet_lengths),
        (19, u64::MAX)
    );
}

#[test]
fn actual_layout_prologue_derives_complete_image_and_stops_before_main_header() {
    let limits = ResourceLimits::HARDENED;
    for components in [1_u16, 2, 64] {
        for r_siz in [0_u16, 1, 0x4000, u16::MAX] {
            let mut raw = siz_with_components(components);
            raw[4..6].copy_from_slice(&r_siz.to_be_bytes());
            for (index, word) in [97_u32, 83, 3, 5, 16, 24, 1, 2].into_iter().enumerate() {
                raw[6 + index * 4..10 + index * 4].copy_from_slice(&word.to_be_bytes());
            }
            let mut infos = [ComponentInfo::default(); MAX_COMPONENTS];
            for (index, info) in infos.iter_mut().take(usize::from(components)).enumerate() {
                let index = u8::try_from(index).unwrap();
                *info = ComponentInfo {
                    precision: 1 + index % 38,
                    signed: index % 2 == 1,
                    x_subsampling: 1 + index,
                    y_subsampling: u8::MAX - index,
                    x_registration: 0,
                    y_registration: 0,
                };
                raw[40 + usize::from(index) * 3..43 + usize::from(index) * 3].copy_from_slice(&[
                    info.precision - 1 + if info.signed { 128 } else { 0 },
                    info.x_subsampling,
                    info.y_subsampling,
                ]);
            }
            let mut input = vec![0x27, 0x18, 0xff, 0x4f];
            input.extend(&raw);
            let start = input.len();
            input.extend([0xff, 0, 0xff, 0xff, 0x90]);
            let expected = ImageSize {
                width: 94,
                height: 78,
                x_origin: 3,
                y_origin: 5,
                components,
                uniform_bit_depth: if components == 1 { Some(1) } else { None },
                uniform_signed: if components == 1 { Some(false) } else { None },
                tile_width: 16,
                tile_height: 24,
                tile_x_origin: 1,
                tile_y_origin: 2,
                tiles_across: 6,
                tiles_down: 4,
                component_info: infos,
            };
            assert_eq!(
                assert_layout_prologue_case(
                    &input,
                    &limits,
                    PacketAdmissionState {
                        position: 2,
                        work: 17,
                        header_bytes: 31,
                        packet_count: u64::MAX,
                    },
                ),
                Ok((expected, r_siz, start)),
            );
            for limit in [
                limits.with_geometry_limits_for_test(0, 0, 0, 0, 0),
                limits.with_geometry_limits_for_test(64, 93, 0, 0, 0),
                limits.with_geometry_limits_for_test(64, 94, 77, 0, 0),
                limits.with_geometry_limits_for_test(64, 94, 78, 7331, 0),
                limits.with_geometry_limits_for_test(64, 94, 78, 7332, 23),
            ] {
                assert!(
                    assert_layout_prologue_case(
                        &input,
                        &limit,
                        PacketAdmissionState {
                            position: 2,
                            work: 0,
                            header_bytes: 0,
                            packet_count: 0,
                        },
                    )
                    .is_err()
                );
            }
        }
    }
    let input = codestream_with_headers(1, &baseline_headers(), &[], &[]);
    let layout = parse_layout(&input, &limits).unwrap();
    let mut parser = new_parser(&input, &limits).unwrap();
    let (size, r_siz, start) = parser.parse_layout_prologue().unwrap();
    assert_eq!(layout.info.image_size, size);
    assert_eq!(r_siz, 0);
    assert_eq!(start, 2 + siz().len());
    assert_eq!(parser.peek_marker(), Ok(COD));
    assert_eq!((parser.position, parser.work_units), (start, 2));
}

fn reference_main_styles(
    parser: &Parser<'_>,
    components: u16,
    default: CodingStyle,
    segments: &[Option<Segment<'_>>],
    extensions: &Part2Extensions,
) -> Result<ComponentCodingStyles, DecodeError> {
    if components == 0 || usize::from(components) > MAX_COMPONENTS {
        return Err(input_error_literal(0, MalformedKind::InvalidImageGeometry));
    }
    let mut owner = ComponentCodingStyles {
        components,
        styles: [default; MAX_COMPONENTS],
    };
    for component in 0..components {
        if let Some(Some(segment)) = segments.get(usize::from(component)) {
            let (_, style) = parser.parse_coc(*segment, components, default)?;
            owner.styles[usize::from(component)] = style;
        }
    }
    reference_decomposition_owner(&mut owner, extensions)?;
    Ok(owner)
}

fn reference_style_overrides(
    parser: &Parser<'_>,
    components: u16,
    default: CodingStyle,
    segments: &[Option<Segment<'_>>],
    owner: &mut ComponentCodingStyles,
) -> Result<(), DecodeError> {
    for component in 0..components {
        if let Some(Some(segment)) = segments.get(usize::from(component)) {
            let (_, style) = parser.parse_coc(*segment, components, default)?;
            if component >= owner.components || usize::from(component) >= owner.styles.len() {
                return Err(input_error_literal(0, MalformedKind::InvalidCodingStyle));
            }
            owner.styles[usize::from(component)] = style;
        }
    }
    Ok(())
}

#[test]
fn actual_raw_component_style_overrides_keep_partial_owners_and_every_frame() {
    let input = [0xa5, 0x5a];
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let default = parser
        .parse_cod(Segment {
            marker: COD,
            offset: 19,
            payload: &[6, 4, 0, 3, 0, 2, 2, 2, 0, 1],
        })
        .unwrap();
    let defaults = [default, raw_resolution_style(2, 4)];
    let payloads: &[&[u8]] = &[&[], &[0], &[0, 0, 1, 2, 2, 0, 1], &[1, 0, 1, 3, 2, 0, 1]];
    let mut cases = 0;
    for components in [0, 1, 2, 63, 64, 65] {
        for count in [0, 1, 2, 64, 65, u16::MAX] {
            for default in defaults {
                let styles = core::array::from_fn(|index| {
                    raw_resolution_style((index % 4) as u8, index % 8)
                });
                for length in [0, 1, 2, 64, 66] {
                    for pattern in 0..3 {
                        for payload in payloads {
                            let segments: Vec<_> = (0..length)
                                .map(|index| {
                                    if pattern == 0
                                        || (pattern == 1 && index != 0)
                                        || (pattern == 2 && index % 3 == 2)
                                    {
                                        None
                                    } else {
                                        Some(Segment {
                                            marker: QCD,
                                            offset: 100 + index * 17,
                                            payload,
                                        })
                                    }
                                })
                                .collect();
                            let before = segments.clone();
                            for position in [0, usize::MAX] {
                                let state = PacketAdmissionState {
                                    position,
                                    work: u64::MAX,
                                    header_bytes: 97,
                                    packet_count: u64::MAX,
                                };
                                set_packet_admission_state(&mut parser, state);
                                let mut actual = ComponentCodingStyles {
                                    components: count,
                                    styles,
                                };
                                let mut expected = actual;
                                let result = reference_style_overrides(
                                    &parser,
                                    components,
                                    default,
                                    &segments,
                                    &mut expected,
                                );
                                assert_eq!(
                                    parser.apply_component_style_overrides(
                                        components,
                                        default,
                                        &segments,
                                        &mut actual
                                    ),
                                    result,
                                    "count={components}, inherited={count}, length={length}, pattern={pattern}"
                                );
                                assert_eq!(
                                    (actual.components, actual.styles),
                                    (expected.components, expected.styles)
                                );
                                assert_main_component_frames(
                                    &parser, state, &input, &limits, &segments, &before,
                                );
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    for count in [0, 64, u16::MAX] {
        let mut actual = ComponentCodingStyles {
            components: count,
            styles: [default; MAX_COMPONENTS],
        };
        let before = actual;
        assert_eq!(
            parser.apply_component_style_overrides(u16::MAX, default, &[None], &mut actual),
            Ok(())
        );
        assert_eq!(actual, before);
        cases += 1;
    }
    assert_eq!(cases, 8_643);
}

#[test]
fn actual_component_style_overrides_preserve_parse_before_slot_errors() {
    let input = [];
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&input, &limits).unwrap();
    let default = parser
        .parse_cod(Segment {
            marker: COD,
            offset: 0,
            payload: &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1],
        })
        .unwrap();
    let valid = Segment {
        marker: COC,
        offset: 101,
        payload: &[1, 0, 0, 3, 2, 0, 1],
    };
    let malformed = Segment {
        marker: COC,
        offset: 203,
        payload: &[1],
    };
    let parsed = parser.parse_coc(valid, 2, default).unwrap().1;
    for count in [0, 1, 2] {
        let mut actual = ComponentCodingStyles {
            components: count,
            styles: [default; MAX_COMPONENTS],
        };
        let mut expected = actual;
        let result = reference_style_overrides(
            &parser,
            2,
            default,
            &[Some(valid), Some(malformed)],
            &mut expected,
        );
        assert_eq!(
            parser.apply_component_style_overrides(
                2,
                default,
                &[Some(valid), Some(malformed)],
                &mut actual
            ),
            result
        );
        assert_eq!(actual, expected);
        assert_eq!(actual.styles[0], if count == 0 { default } else { parsed });
        assert_eq!(actual.styles[1..], [default; MAX_COMPONENTS][1..]);
    }
    let mut actual = ComponentCodingStyles {
        components: 2,
        styles: [default; MAX_COMPONENTS],
    };
    assert_eq!(
        parser.apply_component_style_overrides(2, default, &[Some(valid)], &mut actual),
        Ok(())
    );
    assert_eq!(actual.styles[0], parsed);
    assert_eq!(actual.styles[1], default);
}

#[test]
fn actual_tile_styles_inherit_or_reset_and_use_real_override_producer() {
    let limits = ResourceLimits::HARDENED;
    let reference = new_parser(&[], &limits).unwrap();
    let headers = baseline_headers();
    let main_default = reference
        .parse_cod(Segment {
            marker: COD,
            offset: 0,
            payload: &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1],
        })
        .unwrap();
    let main_coc = [0, 0, 0, 4, 2, 0, 1];
    let tile_coc = [1, 0, 0, 3, 2, 0, 1];
    let tile_cod = [0, 0, 0, 1, 0, 0, 1, 2, 0, 1];
    for reset in [false, true] {
        let mut main_headers = headers.to_vec();
        main_headers.push(segment(COC, &main_coc));
        let mut tile_headers = Vec::new();
        if reset {
            tile_headers.push(segment(COD, &tile_cod));
        }
        tile_headers.push(segment(COC, &tile_coc));
        let input = codestream_with_headers(2, &main_headers, &tile_headers, &[]);
        let layout = parse_layout(&input, &limits).unwrap();
        let tile_default = if reset {
            reference
                .parse_cod(Segment {
                    marker: COD,
                    offset: 0,
                    payload: &tile_cod,
                })
                .unwrap()
        } else {
            main_default
        };
        let mut expected = ComponentCodingStyles {
            components: 2,
            styles: [tile_default; MAX_COMPONENTS],
        };
        if !reset {
            expected.styles[0] = reference
                .parse_coc(
                    Segment {
                        marker: COC,
                        offset: 0,
                        payload: &main_coc,
                    },
                    2,
                    main_default,
                )
                .unwrap()
                .1;
        }
        expected.styles[1] = reference
            .parse_coc(
                Segment {
                    marker: COC,
                    offset: 0,
                    payload: &tile_coc,
                },
                2,
                tile_default,
            )
            .unwrap()
            .1;
        assert_eq!(layout.tile_parts[0].component_coding_styles, expected);
    }
}

fn reference_quantization_overrides(
    parser: &Parser<'_>,
    components: u16,
    styles: &ComponentCodingStyles,
    segments: &[Option<Segment<'_>>],
    owner: &mut ComponentQuantizations,
) -> Result<(), DecodeError> {
    for component in 0..components {
        let index = usize::from(component);
        let style = || {
            if component >= styles.components || index >= styles.styles.len() {
                Err(input_error_literal(0, MalformedKind::InvalidCodingStyle))
            } else {
                Ok(styles.styles[index])
            }
        };
        if let Some(Some(segment)) = segments.get(index) {
            let (_, value) = parser.parse_qcc(*segment, components, style()?)?;
            if component >= owner.components || index >= owner.quantizations.len() {
                return Err(input_error_literal(0, MalformedKind::InvalidQuantization));
            }
            owner.quantizations[index] = value;
        }
        if component >= owner.components || index >= owner.quantizations.len() {
            return Err(input_error_literal(0, MalformedKind::InvalidQuantization));
        }
        let quantization = owner.quantizations[index];
        let coding = style()?;
        let compatible = match quantization.style {
            QuantizationStyle::ScalarDerived => quantization.step_count == 1,
            _ => quantization.step_count == reference_truncated_subband_count(coding),
        };
        if !compatible {
            return Err(input_error_literal(0, MalformedKind::InvalidQuantization));
        }
    }
    Ok(())
}

#[test]
fn actual_raw_component_quantization_overrides_keep_partial_owners_and_every_frame() {
    let input = [0x5a, 0xa5];
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let valid = [1, 1, 0x40, 0x19];
    let mut cases = 0;
    for components in [0, 1, 2, 64, 65] {
        for count in [0, 1, 2, 65] {
            for length in [0, 1, 2, 64, 66] {
                for style_count in [0, 1, 2, 65] {
                    for pattern in [0, 3, 7] {
                        let styles = ComponentCodingStyles {
                            components: style_count,
                            styles: core::array::from_fn(|i| {
                                raw_resolution_style((i % 3) as u8, pattern)
                            }),
                        };
                        let styles_before = styles;
                        for slot_count in [0, 1, 2, 64, 66] {
                            for mode in 0..4 {
                                let slots: Vec<_> = (0..slot_count)
                                    .map(|index| {
                                        let payload: &[u8] = match mode {
                                            0 => return None,
                                            1 => &valid,
                                            2 if index == 0 => &valid,
                                            2 if index > 1 => return None,
                                            _ => &[],
                                        };
                                        Some(Segment {
                                            marker: COD,
                                            offset: 101 + index * 102,
                                            payload,
                                        })
                                    })
                                    .collect();
                                for position in [0, usize::MAX] {
                                    let state = PacketAdmissionState {
                                        position,
                                        work: u64::MAX,
                                        header_bytes: 73,
                                        packet_count: u64::MAX,
                                    };
                                    set_packet_admission_state(&mut parser, state);
                                    let mut values: Vec<_> = (0..length)
                                        .map(|i| {
                                            raw_subband_quantization(
                                                QuantizationStyle::ScalarDerived,
                                                1,
                                                i % 8,
                                            )
                                        })
                                        .collect();
                                    values.reserve(3);
                                    let mut actual = ComponentQuantizations {
                                        components: count,
                                        quantizations: values,
                                    };
                                    let mut expected = actual.clone();
                                    let pointer = actual.quantizations.as_ptr();
                                    let capacity = actual.quantizations.capacity();
                                    let result = reference_quantization_overrides(
                                        &parser,
                                        components,
                                        &styles,
                                        &slots,
                                        &mut expected,
                                    );
                                    assert_eq!(
                                        parser.apply_component_quantization_overrides(
                                            components,
                                            &styles,
                                            &slots,
                                            &mut actual
                                        ),
                                        result,
                                        "components={components}, count={count}, length={length}, styles={style_count}, pattern={pattern}, slots={slot_count}, mode={mode}"
                                    );
                                    assert_eq!(actual, expected);
                                    assert_eq!(actual.quantizations.as_ptr(), pointer);
                                    assert_eq!(actual.quantizations.capacity(), capacity);
                                    assert_eq!(styles, styles_before);
                                    assert_main_component_frames(
                                        &parser, state, &input, &limits, &slots, &slots,
                                    );
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 48_000);
    for length in [0, 64, 66] {
        let styles = ComponentCodingStyles {
            components: u16::MAX,
            styles: [raw_resolution_style(0, 0); MAX_COMPONENTS],
        };
        let mut actual = ComponentQuantizations {
            components: u16::MAX,
            quantizations: vec![
                raw_subband_quantization(QuantizationStyle::ScalarDerived, 1, 0);
                length
            ],
        };
        let mut expected = actual.clone();
        let result =
            reference_quantization_overrides(&parser, u16::MAX, &styles, &[], &mut expected);
        assert_eq!(
            parser.apply_component_quantization_overrides(u16::MAX, &styles, &[], &mut actual),
            result,
        );
        assert_eq!(actual, expected);
    }
}

#[test]
fn actual_component_quantization_overrides_preserve_lookup_parse_set_and_error_prefix_order() {
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let coding = raw_resolution_style(0, 0);
    let styles = ComponentCodingStyles {
        components: 2,
        styles: [coding; MAX_COMPONENTS],
    };
    let raw = raw_subband_quantization(QuantizationStyle::ScalarDerived, 1, 7);
    let valid = Segment {
        marker: QCC,
        offset: 101,
        payload: &[1, 1, 0x40, 0x19],
    };
    let empty = Segment {
        marker: QCC,
        offset: 203,
        payload: &[],
    };
    let parsed = parser.parse_qcc(valid, 2, coding).unwrap().1;
    let mut owner = ComponentQuantizations {
        components: 2,
        quantizations: vec![raw; 3],
    };
    assert_eq!(
        parser.apply_component_quantization_overrides(
            2,
            &styles,
            &[Some(valid), Some(empty)],
            &mut owner
        ),
        Err(input_error_literal(203, MalformedKind::InvalidMarkerLength)),
    );
    assert_eq!(owner.quantizations, vec![parsed, raw, raw]);
    let mut missing_quantization = ComponentQuantizations {
        components: 2,
        quantizations: vec![raw],
    };
    assert_eq!(
        parser.apply_component_quantization_overrides(
            2,
            &styles,
            &[Some(valid)],
            &mut missing_quantization
        ),
        Err(input_error_literal(0, MalformedKind::InvalidQuantization)),
    );
    assert_eq!(missing_quantization.quantizations, vec![parsed]);
    let mut incompatible = ComponentQuantizations {
        components: 2,
        quantizations: vec![
            raw,
            raw_subband_quantization(QuantizationStyle::None, 0, 3),
            raw,
        ],
    };
    let tail = incompatible.quantizations[1..].to_vec();
    assert_eq!(
        parser.apply_component_quantization_overrides(
            2,
            &styles,
            &[Some(valid)],
            &mut incompatible
        ),
        Err(input_error_literal(0, MalformedKind::InvalidQuantization)),
    );
    assert_eq!(incompatible.quantizations[0], parsed);
    assert_eq!(incompatible.quantizations[1..], tail);
    let absent_styles = ComponentCodingStyles {
        components: 0,
        ..styles
    };
    for (slots, coding_styles, expected) in [
        (
            &[Some(empty)][..],
            &absent_styles,
            MalformedKind::InvalidCodingStyle,
        ),
        (&[][..], &absent_styles, MalformedKind::InvalidQuantization),
    ] {
        let mut absent = ComponentQuantizations {
            components: 0,
            quantizations: vec![raw; 3],
        };
        assert_eq!(
            parser.apply_component_quantization_overrides(2, coding_styles, slots, &mut absent),
            Err(input_error_literal(0, expected)),
        );
        assert_eq!(absent.quantizations, vec![raw; 3]);
    }
    let mut absent = ComponentQuantizations {
        components: 0,
        quantizations: vec![raw; 3],
    };
    assert_eq!(
        parser.apply_component_quantization_overrides(2, &styles, &[Some(empty)], &mut absent),
        Err(input_error_literal(203, MalformedKind::InvalidMarkerLength)),
    );
    assert_eq!(absent.quantizations, vec![raw; 3]);
    let mut present = ComponentQuantizations {
        components: 1,
        quantizations: vec![raw; 3],
    };
    assert_eq!(
        parser.apply_component_quantization_overrides(1, &absent_styles, &[], &mut present),
        Err(input_error_literal(0, MalformedKind::InvalidCodingStyle)),
    );
    assert_eq!(present.quantizations, vec![raw; 3]);
}

#[test]
fn actual_tile_quantizations_inherit_or_reset_and_use_real_override_producer() {
    let limits = ResourceLimits::HARDENED;
    let reference = new_parser(&[], &limits).unwrap();
    let main_qcc = [0, 1, 0x40, 0x19];
    let tile_qcd = [1, 0x50, 0x11];
    let tile_qcc = [1, 1, 0x48, 0x08];
    for reset in [false, true] {
        let mut main_headers = baseline_headers().to_vec();
        main_headers.push(segment(QCC, &main_qcc));
        let mut tile_headers = Vec::new();
        if reset {
            tile_headers.push(segment(QCD, &tile_qcd));
        }
        tile_headers.push(segment(QCC, &tile_qcc));
        let input = codestream_with_headers(2, &main_headers, &tile_headers, &[]);
        let layout = parse_layout(&input, &limits).unwrap();
        let tile = &layout.tile_parts[0];
        let mut expected = if reset {
            let default = reference
                .parse_qcd(
                    Segment {
                        marker: QCD,
                        offset: 0,
                        payload: &tile_qcd,
                    },
                    tile.coding_style,
                )
                .unwrap();
            ComponentQuantizations {
                components: 2,
                quantizations: vec![default; 2],
            }
        } else {
            layout.info.component_quantizations.clone()
        };
        expected.quantizations[1] = reference
            .parse_qcc(
                Segment {
                    marker: QCC,
                    offset: 0,
                    payload: &tile_qcc,
                },
                2,
                tile.component_coding_styles.style(1).unwrap(),
            )
            .unwrap()
            .1;
        assert_eq!(tile.component_quantizations, expected);
        if !reset {
            assert_eq!(
                expected.quantizations[0],
                layout.info.component_quantizations.quantizations[0]
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn reference_tile_component_configuration(
    parser: &Parser<'_>,
    components: u16,
    coding: CodingStyle,
    reset_styles: bool,
    coc: &[Option<Segment<'_>>],
    qcd: Option<Segment<'_>>,
    default_quantization: Quantization,
    qcc: &[Option<Segment<'_>>],
    inherited_styles: ComponentCodingStyles,
    inherited_quantizations: ComponentQuantizations,
    extensions: &Part2Extensions,
) -> Result<(ComponentCodingStyles, Quantization, ComponentQuantizations), DecodeError> {
    let mut styles = if reset_styles {
        if components == 0 || usize::from(components) > MAX_COMPONENTS {
            return Err(input_error_literal(0, MalformedKind::InvalidImageGeometry));
        }
        ComponentCodingStyles {
            components,
            styles: [coding; MAX_COMPONENTS],
        }
    } else {
        inherited_styles
    };
    reference_style_overrides(parser, components, coding, coc, &mut styles)?;
    parser.resolve_decomposition_structures(&mut styles, extensions)?;
    let default = match qcd {
        None => default_quantization,
        Some(segment) => parser.parse_qcd(segment, coding)?,
    };
    let mut quantizations = if qcd.is_some() {
        if components == 0 || usize::from(components) > MAX_COMPONENTS {
            return Err(input_error_literal(0, MalformedKind::InvalidImageGeometry));
        }
        ComponentQuantizations {
            components,
            quantizations: vec![default; usize::from(components)],
        }
    } else {
        inherited_quantizations
    };
    reference_quantization_overrides(parser, components, &styles, qcc, &mut quantizations)?;
    Ok((styles, default, quantizations))
}

#[test]
fn actual_owned_tile_components_preserve_raw_resets_inheritance_holes_and_frames() {
    let input = [0x5a, 0xa5];
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let coding = raw_resolution_style(0, 0);
    let default = raw_subband_quantization(QuantizationStyle::ScalarDerived, 1, 0);
    let extensions = Part2Extensions::default();
    let extension_before = extensions.clone();
    let coc_value = Segment {
        marker: COC,
        offset: 101,
        payload: &[1, 0, 0, 3, 2, 0, 1],
    };
    let qcc_value = Segment {
        marker: QCC,
        offset: 203,
        payload: &[1, 1, 0x40, 0x19],
    };
    let qcd_value = Segment {
        marker: QCD,
        offset: 303,
        payload: &[1, 0x48, 0x08],
    };
    let mut cases = 0;
    for components in [0, 1, 2, 64, 65] {
        for style_count in [0, 1, 2, 65] {
            for quantization_count in [0, 1, 2, 65] {
                for length in [0, 1, 2, 64] {
                    for reset in [false, true] {
                        for qcd in [
                            None,
                            Some(qcd_value),
                            Some(Segment {
                                marker: QCD,
                                offset: 303,
                                payload: &[],
                            }),
                        ] {
                            for mode in 0..3 {
                                let coc = match mode {
                                    0 => [None, None],
                                    1 => [Some(coc_value), None],
                                    _ => [
                                        Some(Segment {
                                            marker: COC,
                                            offset: 101,
                                            payload: &[],
                                        }),
                                        None,
                                    ],
                                };
                                let qcc = match mode {
                                    0 => [None, None],
                                    1 => [None, Some(qcc_value)],
                                    _ => [
                                        Some(Segment {
                                            marker: QCC,
                                            offset: 203,
                                            payload: &[],
                                        }),
                                        None,
                                    ],
                                };
                                for position in [0, usize::MAX] {
                                    let state = PacketAdmissionState {
                                        position,
                                        work: u64::MAX,
                                        header_bytes: 73,
                                        packet_count: u64::MAX,
                                    };
                                    set_packet_admission_state(&mut parser, state);
                                    let inherited_styles = ComponentCodingStyles {
                                        components: style_count,
                                        styles: core::array::from_fn(|i| {
                                            raw_resolution_style((i % 3) as u8, i % 8)
                                        }),
                                    };
                                    let mut values: Vec<_> = (0..length)
                                        .map(|i| {
                                            raw_subband_quantization(
                                                QuantizationStyle::ScalarDerived,
                                                1,
                                                i % 8,
                                            )
                                        })
                                        .collect();
                                    values.reserve(3);
                                    let pointer = values.as_ptr();
                                    let capacity = values.capacity();
                                    let inherited_quantizations = ComponentQuantizations {
                                        components: quantization_count,
                                        quantizations: values,
                                    };
                                    let expected = reference_tile_component_configuration(
                                        &parser,
                                        components,
                                        coding,
                                        reset,
                                        &coc,
                                        qcd,
                                        default,
                                        &qcc,
                                        inherited_styles,
                                        inherited_quantizations.clone(),
                                        &extensions,
                                    );
                                    let actual = parser.finish_tile_component_configuration(
                                        components,
                                        coding,
                                        reset,
                                        &coc,
                                        qcd,
                                        default,
                                        &qcc,
                                        inherited_styles,
                                        inherited_quantizations,
                                        &extensions,
                                    );
                                    assert_eq!(
                                        actual, expected,
                                        "components={components}, styles={style_count}, quantizations={quantization_count}, length={length}, reset={reset}, qcd={qcd:?}, mode={mode}"
                                    );
                                    if let Ok((_, _, owner)) = &actual
                                        && qcd.is_none()
                                    {
                                        assert_eq!(owner.quantizations.as_ptr(), pointer);
                                        assert_eq!(owner.quantizations.capacity(), capacity);
                                    }
                                    assert_eq!(extensions, extension_before);
                                    assert_main_component_frames(
                                        &parser, state, &input, &limits, &coc, &coc,
                                    );
                                    assert_main_component_frames(
                                        &parser, state, &input, &limits, &qcc, &qcc,
                                    );
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 11_520);
}

#[test]
fn actual_owned_tile_components_preserve_factory_override_resolution_qcd_error_order() {
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let coding = parser
        .parse_cod(Segment {
            marker: COD,
            offset: 0,
            payload: &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1],
        })
        .unwrap();
    let styles = ComponentCodingStyles {
        components: 2,
        styles: [coding; MAX_COMPONENTS],
    };
    let quantization = raw_subband_quantization(QuantizationStyle::ScalarDerived, 1, 0);
    let quants = ComponentQuantizations {
        components: 2,
        quantizations: vec![quantization; 3],
    };
    let extensions = Part2Extensions::default();
    let bad_coc = Segment {
        marker: COC,
        offset: 101,
        payload: &[],
    };
    let bad_qcd = Segment {
        marker: QCD,
        offset: 303,
        payload: &[],
    };
    let bad_qcc = Segment {
        marker: QCC,
        offset: 203,
        payload: &[],
    };
    assert_eq!(
        parser.finish_tile_component_configuration(
            0,
            coding,
            true,
            &[Some(bad_coc)],
            Some(bad_qcd),
            quantization,
            &[Some(bad_qcc)],
            styles,
            quants.clone(),
            &extensions
        ),
        Err(input_error_literal(0, MalformedKind::InvalidImageGeometry)),
    );
    assert_eq!(
        parser.finish_tile_component_configuration(
            2,
            coding,
            false,
            &[Some(bad_coc)],
            Some(bad_qcd),
            quantization,
            &[Some(bad_qcc)],
            styles,
            quants.clone(),
            &extensions
        ),
        Err(input_error_literal(101, MalformedKind::InvalidMarkerLength)),
    );
    let mut missing_dfs = styles;
    missing_dfs.styles[0].decomposition_structure = Some(1);
    let result = parser.finish_tile_component_configuration(
        2,
        coding,
        false,
        &[],
        Some(bad_qcd),
        quantization,
        &[Some(bad_qcc)],
        missing_dfs,
        quants.clone(),
        &extensions,
    );
    let mut expected = missing_dfs;
    assert_eq!(
        result,
        parser
            .resolve_decomposition_structures(&mut expected, &extensions)
            .map(|()| (expected, quantization, quants.clone()))
    );
    assert!(result.is_err());
    let empty_styles = ComponentCodingStyles {
        components: 0,
        ..styles
    };
    assert_eq!(
        parser.finish_tile_component_configuration(
            0,
            coding,
            false,
            &[],
            Some(bad_qcd),
            quantization,
            &[],
            empty_styles,
            quants.clone(),
            &extensions
        ),
        Err(input_error_literal(303, MalformedKind::InvalidMarkerLength)),
    );
    assert_eq!(
        parser.finish_tile_component_configuration(
            2,
            coding,
            false,
            &[],
            Some(bad_qcd),
            quantization,
            &[Some(bad_qcc)],
            styles,
            quants,
            &extensions
        ),
        Err(input_error_literal(303, MalformedKind::InvalidMarkerLength)),
    );
}

#[test]
fn actual_tile_component_join_uses_real_dispatch_and_all_cod_qcd_reset_combinations() {
    let limits = ResourceLimits::HARDENED;
    let reference = new_parser(&[], &limits).unwrap();
    let tile_cod = [0, 0, 0, 1, 0, 0, 1, 2, 0, 1];
    let tile_coc = [1, 0, 0, 3, 2, 0, 1];
    let tile_qcd = [1, 0x48, 0x08];
    let tile_qcc = [1, 1, 0x40, 0x19];
    for reset_styles in [false, true] {
        for reset_quantizations in [false, true] {
            let mut main_headers = baseline_headers().to_vec();
            main_headers.push(segment(COC, &[0, 0, 0, 4, 2, 0, 1]));
            main_headers.push(segment(QCC, &[0, 1, 0x38, 0x73]));
            let mut tile_headers = Vec::new();
            if reset_styles {
                tile_headers.push(segment(COD, &tile_cod));
            }
            tile_headers.push(segment(COC, &tile_coc));
            if reset_quantizations {
                tile_headers.push(segment(QCD, &tile_qcd));
            }
            tile_headers.push(segment(QCC, &tile_qcc));
            let input = codestream_with_headers(2, &main_headers, &tile_headers, &[]);
            let layout = parse_layout(&input, &limits).unwrap();
            let tile = &layout.tile_parts[0];
            let coc = [
                None,
                Some(Segment {
                    marker: COC,
                    offset: 0,
                    payload: &tile_coc,
                }),
            ];
            let qcc = [
                None,
                Some(Segment {
                    marker: QCC,
                    offset: 0,
                    payload: &tile_qcc,
                }),
            ];
            let qcd = if reset_quantizations {
                Some(Segment {
                    marker: QCD,
                    offset: 0,
                    payload: &tile_qcd,
                })
            } else {
                None
            };
            let expected = reference_tile_component_configuration(
                &reference,
                2,
                tile.coding_style,
                reset_styles,
                &coc,
                qcd,
                layout.info.quantization,
                &qcc,
                layout.info.component_coding_styles,
                layout.info.component_quantizations.clone(),
                &tile.part2_extensions,
            )
            .unwrap();
            assert_eq!(tile.component_coding_styles, expected.0);
            assert_eq!(tile.quantization, expected.1);
            assert_eq!(tile.component_quantizations, expected.2);
        }
    }
}

fn reference_main_quantizations(
    parser: &Parser<'_>,
    components: u16,
    default: Quantization,
    styles: &ComponentCodingStyles,
    segments: &[Option<Segment<'_>>],
) -> Result<ComponentQuantizations, DecodeError> {
    if components == 0 || usize::from(components) > MAX_COMPONENTS {
        return Err(input_error_literal(0, MalformedKind::InvalidImageGeometry));
    }
    let mut owner = ComponentQuantizations {
        components,
        quantizations: vec![default; usize::from(components)],
    };
    for component in 0..components {
        let style = || {
            if component >= styles.components || usize::from(component) >= styles.styles.len() {
                Err(input_error_literal(0, MalformedKind::InvalidCodingStyle))
            } else {
                Ok(styles.styles[usize::from(component)])
            }
        };
        if let Some(Some(segment)) = segments.get(usize::from(component)) {
            let (_, value) = parser.parse_qcc(*segment, components, style()?)?;
            owner.quantizations[usize::from(component)] = value;
        }
        let quantization = owner.quantizations[usize::from(component)];
        let compatible = match quantization.style {
            QuantizationStyle::ScalarDerived => {
                style()?;
                quantization.step_count == 1
            }
            _ => quantization.step_count == reference_truncated_subband_count(style()?),
        };
        if !compatible {
            return Err(input_error_literal(0, MalformedKind::InvalidQuantization));
        }
    }
    Ok(owner)
}

#[test]
fn actual_main_component_factories_preserve_all_counts_defaults_and_storage() {
    let mut cases = 0;
    for components in 0..=u16::MAX {
        let pattern = usize::from(components % 8);
        let style = raw_resolution_style(components as u8, pattern);
        let quantization = raw_subband_quantization(
            [
                QuantizationStyle::None,
                QuantizationStyle::ScalarDerived,
                QuantizationStyle::ScalarExpounded,
            ][pattern % 3],
            components,
            pattern,
        );
        let styles = ComponentCodingStyles::new(components, style);
        let quantizations = ComponentQuantizations::new(components, quantization);
        if components == 0 || components > 64 {
            let error = input_error_literal(0, MalformedKind::InvalidImageGeometry);
            assert_eq!(styles, Err(error));
            assert_eq!(quantizations, Err(error));
        } else {
            let styles = styles.unwrap();
            let quantizations = quantizations.unwrap();
            assert_eq!(styles.components, components);
            assert_eq!(styles.styles, [style; MAX_COMPONENTS]);
            assert_eq!(quantizations.components, components);
            assert_eq!(
                quantizations.quantizations,
                vec![quantization; usize::from(components)]
            );
            assert_eq!(
                ComponentCodingStyles::uniform(components, style).unwrap(),
                styles
            );
            assert_eq!(
                ComponentQuantizations::uniform(components, quantization).unwrap(),
                quantizations
            );
        }
        cases += 1;
    }
    assert_eq!(cases, 65_536);
}

#[test]
fn actual_main_component_quantization_access_preserves_raw_owner_and_error_tails() {
    let mut cases = 0;
    for count in [0, 1, 2, 63, 64, 65, 257, u16::MAX] {
        for length in [0, 1, 2, 63, 64, 65, 257] {
            for component in [0, 1, 2, 63, 64, 256, u16::MAX] {
                let mut values: Vec<_> = (0..length)
                    .map(|i| {
                        raw_subband_quantization(
                            QuantizationStyle::ScalarExpounded,
                            i as u16,
                            i % 8,
                        )
                    })
                    .collect();
                values.reserve(3);
                let mut owner = ComponentQuantizations {
                    components: count,
                    quantizations: values,
                };
                let before = owner.clone();
                let capacity = owner.quantizations.capacity();
                let pointer = owner.quantizations.as_ptr();
                let invalid = component >= count || usize::from(component) >= length;
                let error = input_error_literal(0, MalformedKind::InvalidQuantization);
                let expected = if invalid {
                    Err(error)
                } else {
                    Ok(before.quantizations[usize::from(component)])
                };
                assert_eq!(owner.quantization(component), expected);
                assert_eq!(owner, before);
                let value = raw_subband_quantization(QuantizationStyle::ScalarDerived, u16::MAX, 7);
                let mut expected = before;
                if !invalid {
                    expected.quantizations[usize::from(component)] = value;
                }
                assert_eq!(
                    owner.set(component, value),
                    if invalid { Err(error) } else { Ok(()) }
                );
                assert_eq!(owner, expected);
                assert_eq!(owner.quantizations.capacity(), capacity);
                assert_eq!(owner.quantizations.as_ptr(), pointer);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 392);
}

#[test]
fn actual_main_component_compatibility_preserves_raw_fields_and_truncated_directions() {
    let mut cases = 0;
    for levels in 0..=u8::MAX {
        for pattern in 0..8 {
            let style = raw_resolution_style(levels, pattern);
            for count in [
                0,
                1,
                2,
                32,
                64,
                97,
                98,
                u16::MAX,
                reference_truncated_subband_count(style),
            ] {
                for kind in [
                    QuantizationStyle::None,
                    QuantizationStyle::ScalarDerived,
                    QuantizationStyle::ScalarExpounded,
                ] {
                    let value = raw_subband_quantization(kind, count, pattern);
                    let expected = if kind == QuantizationStyle::ScalarDerived {
                        count == 1
                    } else {
                        count == reference_truncated_subband_count(style)
                    };
                    assert_eq!(value.is_compatible_with(style), expected);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 55_296);
}

fn assert_main_component_frames(
    parser: &Parser<'_>,
    state: PacketAdmissionState,
    input: &[u8],
    limits: &ResourceLimits,
    segments: &[Option<Segment<'_>>],
    before: &[Option<Segment<'_>>],
) {
    assert_packet_admission_state(parser, state, input, limits);
    assert_eq!(segments.len(), before.len());
    for (after, before) in segments.iter().zip(before) {
        match (after, before) {
            (Some(after), Some(before)) => {
                assert_eq!(
                    (after.marker, after.offset, after.payload),
                    (before.marker, before.offset, before.payload)
                );
                assert!(core::ptr::eq(
                    after.payload.as_ptr(),
                    before.payload.as_ptr()
                ));
            }
            (None, None) => {}
            _ => panic!("segment presence changed"),
        }
    }
}

#[test]
fn actual_main_component_styles_preserve_lazy_slots_defaults_resolution_and_first_errors() {
    let input = [0xa5, 0x5a];
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let defaults = [
        parser
            .parse_cod(Segment {
                marker: COD,
                offset: 19,
                payload: &[6, 4, 0, 3, 0, 2, 2, 2, 0, 1],
            })
            .unwrap(),
        raw_resolution_style(2, 4),
        raw_resolution_style(33, 7),
        raw_resolution_style(u8::MAX, 2),
    ];
    let payloads: &[&[u8]] = &[
        &[],
        &[0],
        &[0, 0, 1, 2, 2, 0, 1],
        &[0, 0, 129, 2, 2, 0, 1],
        &[255, 255],
    ];
    let mut cases = 0;
    for components in [0, 1, 2, 63, 64, 65, u16::MAX] {
        for default in defaults {
            for variant in 0..8 {
                let extensions = raw_decomposition_extensions(variant, 3);
                let extension_before = extensions.clone();
                for length in [0, 1, 2, 64, 66] {
                    for payload in payloads {
                        let segments: Vec<_> = (0..length)
                            .map(|index| {
                                if index % 3 == 2 {
                                    None
                                } else {
                                    Some(Segment {
                                        marker: QCD,
                                        offset: 100 + index * 17,
                                        payload,
                                    })
                                }
                            })
                            .collect();
                        let before = segments.clone();
                        for position in [0, usize::MAX] {
                            let state = PacketAdmissionState {
                                position,
                                work: u64::MAX,
                                header_bytes: 97,
                                packet_count: u64::MAX,
                            };
                            set_packet_admission_state(&mut parser, state);
                            assert_eq!(
                                parser.finish_main_component_styles(
                                    components,
                                    default,
                                    &segments,
                                    &extensions
                                ),
                                reference_main_styles(
                                    &parser,
                                    components,
                                    default,
                                    &segments,
                                    &extensions
                                ),
                                "count={components}, length={length}, variant={variant}, payload={payload:?}"
                            );
                            assert_main_component_frames(
                                &parser, state, &input, &limits, &segments, &before,
                            );
                            assert_eq!(extensions, extension_before);
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 11_200);
}

#[test]
fn actual_main_component_quantizations_preserve_resolved_styles_slots_compatibility_and_first_errors()
 {
    let input = [0x5a, 0xa5];
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let payloads: &[&[u8]] = &[&[], &[0], &[0, 0, 0], &[0, 1, 0, 0], &[255, 255]];
    let mut cases = 0;
    for components in [0, 1, 2, 63, 64, 65, u16::MAX] {
        for style_count in [0, 1, 2, 64, 65, u16::MAX] {
            for pattern in 0..8 {
                let styles = ComponentCodingStyles {
                    components: style_count,
                    styles: core::array::from_fn(|i| raw_resolution_style((i % 3) as u8, pattern)),
                };
                let styles_before = styles;
                for kind in [
                    QuantizationStyle::None,
                    QuantizationStyle::ScalarDerived,
                    QuantizationStyle::ScalarExpounded,
                ] {
                    let default = raw_subband_quantization(
                        kind,
                        if pattern % 2 == 0 { 1 } else { u16::MAX },
                        pattern,
                    );
                    for length in [0, 1, 2, 64, 66] {
                        for payload in payloads {
                            let segments: Vec<_> = (0..length)
                                .map(|index| {
                                    if index % 3 == 2 {
                                        None
                                    } else {
                                        Some(Segment {
                                            marker: COD,
                                            offset: 200 + index * 19,
                                            payload,
                                        })
                                    }
                                })
                                .collect();
                            let before = segments.clone();
                            let state = PacketAdmissionState {
                                position: usize::MAX,
                                work: u64::MAX,
                                header_bytes: 73,
                                packet_count: u64::MAX,
                            };
                            set_packet_admission_state(&mut parser, state);
                            assert_eq!(
                                parser.finish_main_component_quantizations(
                                    components, default, &styles, &segments
                                ),
                                reference_main_quantizations(
                                    &parser, components, default, &styles, &segments
                                ),
                                "count={components}, style_count={style_count}, pattern={pattern}, length={length}, kind={kind:?}, payload={payload:?}"
                            );
                            assert_eq!(styles, styles_before);
                            assert_main_component_frames(
                                &parser, state, &input, &limits, &segments, &before,
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 25_200);
}

#[test]
fn actual_main_component_finalizers_consume_real_header_reader_and_decomposition_producers() {
    let mut input = siz_with_components(2);
    input.extend(segment(COD, &[6, 4, 0, 3, 0, 2, 2, 2, 0, 1]));
    input.extend(segment(COC, &[0, 0, 129, 2, 2, 0, 1]));
    input.extend(segment(QCD, &[1, 0x38, 0x73]));
    input.extend(segment(QCC, &[1, 1, 0x40, 0x19]));
    input.extend(segment(DFS, &raw_dfs_payload(1, 2)));
    input.extend(segment(ADS, &raw_ads_payload(1, 3, 4, 1)));
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let segment = parser.read_segment().unwrap();
    let (size, _) = parser.parse_siz(segment).unwrap();
    let segment = parser.read_segment().unwrap();
    let default = parser.parse_cod(segment).unwrap();
    let coc = parser.read_segment().unwrap();
    let segment = parser.read_segment().unwrap();
    let quantization = parser.parse_qcd(segment, default).unwrap();
    let qcc = parser.read_segment().unwrap();
    let mut extensions = raw_decomposition_extensions(0, 0);
    extensions.metadata_bytes = 0;
    let segment = parser.read_segment().unwrap();
    parser.parse_dfs(segment, &mut extensions).unwrap();
    let segment = parser.read_segment().unwrap();
    parser.parse_ads(segment, &mut extensions).unwrap();
    // Slot ownership, not the repeated encoded component index, selects the override.
    let coc_slots = [None, Some(coc)];
    let qcc_slots = [Some(qcc), None];
    let state = PacketAdmissionState {
        position: parser.position,
        work: parser.work_units,
        header_bytes: parser.packet_length_bytes,
        packet_count: parser.packet_lengths,
    };
    let extension_before = extensions.clone();
    let expected_styles =
        reference_main_styles(&parser, size.components, default, &coc_slots, &extensions).unwrap();
    let styles = parser
        .finish_main_component_styles(size.components, default, &coc_slots, &extensions)
        .unwrap();
    assert_eq!(styles, expected_styles);
    assert_ne!(
        styles.styles[1].decomposition_directions,
        default.decomposition_directions
    );
    let quantizations = parser
        .finish_main_component_quantizations(size.components, quantization, &styles, &qcc_slots)
        .unwrap();
    assert_eq!(
        quantizations,
        reference_main_quantizations(&parser, size.components, quantization, &styles, &qcc_slots)
            .unwrap()
    );
    assert_ne!(quantizations.quantizations[0], quantization);
    assert_eq!(quantizations.quantizations[1], quantization);
    assert_eq!(extensions, extension_before);
    assert_main_component_frames(&parser, state, &input, &limits, &coc_slots, &coc_slots);
    assert_main_component_frames(&parser, state, &input, &limits, &qcc_slots, &qcc_slots);
    assert_eq!(parser.position, input.len());

    let headers = [
        self::segment(COD, &[6, 4, 0, 3, 0, 2, 2, 2, 0, 1]),
        self::segment(COC, &[1, 0, 129, 2, 2, 0, 1]),
        self::segment(QCD, &[1, 0x38, 0x73]),
        self::segment(QCC, &[0, 1, 0x40, 0x19]),
        self::segment(DFS, &raw_dfs_payload(1, 2)),
    ];
    let bytes = codestream_with_headers(2, &headers, &[], &[]);
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(layout.info.component_coding_styles, styles);
    assert_eq!(layout.info.component_quantizations, quantizations);
}

#[test]
fn actual_main_component_finalizers_preserve_specific_raw_order_and_unused_payloads() {
    let input = [0x73, 0x19];
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&input, &limits).unwrap();
    let default = parser
        .parse_cod(Segment {
            marker: COD,
            offset: 13,
            payload: &[0, 0, 0, 1, 0, 2, 2, 2, 0, 1],
        })
        .unwrap();
    let mut extensions = raw_decomposition_extensions(0, 0);
    extensions
        .decomposition_structures
        .push(DecompositionStructure {
            index: 1,
            directions: vec![DecompositionDirection::Horizontal],
        });
    let explicit = Segment {
        marker: COC,
        offset: 101,
        payload: &[0, 0, 1, 2, 2, 0, 1],
    };
    let dfs = Segment {
        marker: COC,
        offset: 203,
        payload: &[0, 0, 129, 2, 2, 0, 1],
    };
    let malformed = Segment {
        marker: COC,
        offset: 777,
        payload: &[],
    };
    let slots = [Some(explicit), Some(dfs), Some(malformed)];
    let styles = parser
        .finish_main_component_styles(2, default, &slots, &extensions)
        .unwrap();
    assert_eq!(styles.styles[0].decomposition_levels, 1);
    assert_eq!(
        styles.styles[1].decomposition_levels,
        default.decomposition_levels
    );
    assert_eq!(styles.styles[2..], [default; MAX_COMPONENTS][2..]);
    assert_eq!(
        styles.styles[1].decomposition_directions[..2],
        [DecompositionDirection::Horizontal; 2]
    );
    assert_eq!(
        parser.finish_main_component_styles(
            2,
            default,
            &[Some(explicit), Some(malformed), Some(dfs)],
            &extensions
        ),
        Err(input_error_literal(777, MalformedKind::InvalidMarkerLength))
    );
    let mut missing = default;
    missing.decomposition_structure = Some(127);
    // All COC payloads are parsed before any decomposition lookup.
    assert_eq!(
        parser.finish_main_component_styles(2, missing, &[None, Some(malformed)], &extensions),
        Err(input_error_literal(777, MalformedKind::InvalidMarkerLength))
    );
    let empty = ComponentCodingStyles {
        components: 0,
        styles: styles.styles,
    };
    let value = raw_subband_quantization(QuantizationStyle::ScalarDerived, 1, 7);
    // The style lookup precedes a present QCC parse, but not factory geometry.
    assert_eq!(
        parser.finish_main_component_quantizations(1, value, &empty, &[Some(malformed)]),
        Err(input_error_literal(0, MalformedKind::InvalidCodingStyle))
    );
    assert_eq!(
        parser.finish_main_component_quantizations(0, value, &empty, &[Some(malformed)]),
        Err(input_error_literal(0, MalformedKind::InvalidImageGeometry))
    );
    let incompatible = Quantization {
        step_count: 0,
        ..value
    };
    assert_eq!(
        parser.finish_main_component_quantizations(
            2,
            incompatible,
            &styles,
            &[None, Some(malformed)]
        ),
        Err(input_error_literal(0, MalformedKind::InvalidQuantization))
    );
    let valid_qcc = Segment {
        marker: QCC,
        offset: 509,
        payload: &[0, 1, 0, 0],
    };
    let values = parser
        .finish_main_component_quantizations(
            1,
            incompatible,
            &styles,
            &[Some(valid_qcc), Some(malformed)],
        )
        .unwrap();
    assert_eq!(values.quantizations.len(), 1);
    assert_eq!(values.quantizations[0].step_count, 1);
    assert_eq!(parser.position, 0);
    assert_eq!(parser.work_units, 0);
    assert_eq!(parser.packet_length_bytes, 0);
    assert_eq!(parser.packet_lengths, 0);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));
}

fn raw_decomposition_extensions(variant: usize, length: usize) -> Part2Extensions {
    use DecompositionDirection::{Horizontal, None, TwoDimensional, Vertical};
    let directions = (0..length)
        .map(|index| [None, Horizontal, Vertical, TwoDimensional][index % 4])
        .collect();
    let dfs = |index, directions| DecompositionStructure { index, directions };
    let ads = |depths| ArbitraryDecomposition {
        index: 0,
        sublevel_depths: depths,
        subband_splits: vec![Vertical, None, Horizontal],
    };
    let mut extensions = raw_owned_tile_part_fixture(0).part2_extensions;
    extensions.decomposition_structures.clear();
    extensions.arbitrary_decompositions.clear();
    extensions.metadata_bytes = u64::MAX;
    match variant {
        0 => {}
        1 => extensions.decomposition_structures.push(dfs(0, directions)),
        2 => extensions
            .decomposition_structures
            .push(dfs(u8::MAX, directions)),
        3 => {
            extensions.decomposition_structures.push(dfs(0, directions));
            extensions
                .decomposition_structures
                .push(dfs(0, vec![TwoDimensional]));
        }
        4 => {
            extensions.arbitrary_decompositions.push(ads(vec![0]));
            extensions.arbitrary_decompositions.push(ads(vec![1, 2, 3]));
        }
        5 => {
            extensions.arbitrary_decompositions.push(ads(vec![1, 2, 3]));
            extensions.arbitrary_decompositions.push(ads(vec![0]));
        }
        6 => {
            extensions.arbitrary_decompositions.push(ads(Vec::new()));
            extensions.arbitrary_decompositions.push(ads(vec![0]));
        }
        _ => {
            extensions.decomposition_structures.push(dfs(0, directions));
            extensions.arbitrary_decompositions.push(ads(vec![0]));
        }
    }
    extensions
}

fn reference_decomposition_style(
    mut style: CodingStyle,
    extensions: &Part2Extensions,
) -> Result<CodingStyle, DecodeError> {
    let Some(index) = style.decomposition_structure else {
        return Ok(style);
    };
    if let Some(position) = extensions
        .decomposition_structures
        .iter()
        .position(|entry| entry.index == index)
    {
        let directions = &extensions.decomposition_structures[position].directions;
        let Some(last) = directions.last() else {
            return Err(input_error_literal(0, MalformedKind::InvalidCodingStyle));
        };
        let count = usize::from(style.decomposition_levels);
        if count > style.decomposition_directions.len() {
            return Err(input_error_literal(0, MalformedKind::InvalidCodingStyle));
        }
        let selected: Vec<_> = directions
            .iter()
            .copied()
            .chain(core::iter::repeat(*last))
            .take(count)
            .collect();
        style.decomposition_directions[..count].copy_from_slice(&selected);
        return Ok(style);
    }
    let Some(position) = extensions
        .arbitrary_decompositions
        .iter()
        .position(|entry| entry.index == index)
    else {
        return Err(input_error_literal(
            0,
            MalformedKind::MissingRequiredStructure,
        ));
    };
    if extensions.arbitrary_decompositions[position]
        .sublevel_depths
        .iter()
        .all(|depth| (1..=3).contains(depth))
    {
        Ok(style)
    } else {
        Err(input_error_literal(0, MalformedKind::InvalidCodingStyle))
    }
}

fn reference_decomposition_owner(
    owner: &mut ComponentCodingStyles,
    extensions: &Part2Extensions,
) -> Result<(), DecodeError> {
    for index in 0..usize::from(owner.components) {
        let style = *owner
            .styles
            .get(index)
            .ok_or_else(|| input_error_literal(0, MalformedKind::InvalidCodingStyle))?;
        if style.decomposition_structure.is_some() {
            let resolved = reference_decomposition_style(style, extensions)?;
            owner.styles[index] = resolved;
        }
    }
    Ok(())
}

fn raw_component_application_size(components: u16, variant: u8) -> ImageSize {
    let mut size = raw_resolution_size(
        if variant == 0 { 0 } else { u32::MAX },
        17,
        (0, u8::MAX),
        0x1234,
        components,
    );
    for (index, info) in size.component_info.iter_mut().enumerate() {
        info.precision = if variant == 1 {
            (index as u8).wrapping_mul(17)
        } else {
            7
        };
        info.signed = variant == 2 && index % 2 != 0;
        info.x_subsampling = (index as u8).wrapping_mul(3);
        info.y_subsampling = u8::MAX - index as u8;
        info.x_registration = (index as u16).wrapping_mul(257);
        info.y_registration = u16::MAX - info.x_registration;
    }
    size
}

fn reference_uniform_component_depths(size: &ImageSize, first: ComponentInfo) -> bool {
    (1..usize::from(size.components)).all(|index| {
        size.component_info
            .get(index)
            .is_some_and(|info| (info.precision, info.signed) == (first.precision, first.signed))
    })
}

fn reference_component_depth_application(
    size: &mut ImageSize,
    depths: &[ComponentBitDepth],
    offset: usize,
) -> Result<(), DecodeError> {
    if depths.is_empty() {
        return Ok(());
    }
    for index in 0..usize::from(size.components) {
        let depth = depths
            .get(index)
            .ok_or_else(|| input_error_literal(offset, MalformedKind::MissingRequiredStructure))?;
        let info = size
            .component_info
            .get_mut(index)
            .ok_or_else(|| input_error_literal(offset, MalformedKind::InvalidImageGeometry))?;
        *info = ComponentInfo {
            precision: depth.precision,
            signed: depth.signed,
            ..*info
        };
    }
    if size.components == 0 {
        return Err(input_error_literal(0, MalformedKind::InvalidImageGeometry));
    }
    let first = size.component_info[0];
    let uniform = reference_uniform_component_depths(size, first);
    size.uniform_bit_depth = uniform.then_some(first.precision);
    size.uniform_signed = uniform.then_some(first.signed);
    Ok(())
}

fn reference_component_registration_application(
    size: &mut ImageSize,
    registrations: &[ComponentRegistration],
    offset: usize,
) -> Result<(), DecodeError> {
    if registrations.is_empty() {
        return Ok(());
    }
    for index in 0..usize::from(size.components) {
        let registration = registrations
            .get(index)
            .ok_or_else(|| input_error_literal(offset, MalformedKind::MissingRequiredStructure))?;
        let info = size
            .component_info
            .get_mut(index)
            .ok_or_else(|| input_error_literal(offset, MalformedKind::InvalidImageGeometry))?;
        *info = ComponentInfo {
            x_registration: registration.horizontal,
            y_registration: registration.vertical,
            ..*info
        };
    }
    Ok(())
}

#[test]
fn actual_decomposition_lookups_preserve_first_payload_and_borrow_for_all_ids() {
    use DecompositionDirection::{Horizontal, None, Vertical};
    let mut cases = 0;
    for stored in 0..=u8::MAX {
        let mut extensions = raw_decomposition_extensions(0, 0);
        extensions.decomposition_structures = vec![
            DecompositionStructure {
                index: stored.wrapping_add(1),
                directions: Vec::new(),
            },
            DecompositionStructure {
                index: stored,
                directions: vec![Horizontal, None],
            },
            DecompositionStructure {
                index: stored,
                directions: vec![Vertical],
            },
        ];
        extensions.arbitrary_decompositions = vec![
            ArbitraryDecomposition {
                index: stored.wrapping_add(1),
                sublevel_depths: Vec::new(),
                subband_splits: Vec::new(),
            },
            ArbitraryDecomposition {
                index: stored,
                sublevel_depths: vec![0, u8::MAX],
                subband_splits: vec![Vertical, None],
            },
            ArbitraryDecomposition {
                index: stored,
                sublevel_depths: vec![1],
                subband_splits: vec![Horizontal],
            },
        ];
        let before = extensions.clone();
        for index in 0..=u8::MAX {
            let expected = extensions
                .decomposition_structures
                .iter()
                .find(|entry| entry.index == index);
            let actual = extensions.decomposition_structure(index);
            assert_eq!(actual, expected);
            if let (Some(actual), Some(expected)) = (actual, expected) {
                assert!(core::ptr::eq(actual, expected));
            }
            let expected = extensions
                .arbitrary_decompositions
                .iter()
                .find(|entry| entry.index == index);
            let actual = extensions.arbitrary_decomposition(index);
            assert_eq!(actual, expected);
            if let (Some(actual), Some(expected)) = (actual, expected) {
                assert!(core::ptr::eq(actual, expected));
            }
            cases += 1;
        }
        assert_eq!(extensions, before);
    }
    assert_eq!(cases, 65_536);
}

#[test]
fn actual_decomposition_setter_preserves_raw_count_every_slot_and_unused_tail() {
    let mut cases = 0;
    for components in [0, 1, 63, 64, 65, u16::MAX] {
        for component in [0, 1, 63, 64, 65, u16::MAX] {
            for pattern in 0..4 {
                for levels in [0, 1, 31, 32, 33, u8::MAX] {
                    let before =
                        core::array::from_fn(|index| raw_resolution_style(index as u8, index % 8));
                    let mut owner = ComponentCodingStyles {
                        components,
                        styles: before,
                    };
                    let style = raw_resolution_style(levels, pattern);
                    let mut expected = before;
                    let result = if component < components && usize::from(component) < before.len()
                    {
                        expected[usize::from(component)] = style;
                        Ok(())
                    } else {
                        Err(input_error_literal(0, MalformedKind::InvalidCodingStyle))
                    };
                    assert_eq!(owner.set(component, style), result);
                    assert_eq!((owner.components, owner.styles), (components, expected));
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 864);
}

#[test]
fn actual_decomposition_style_preserves_all_levels_duplicates_priority_and_full_result() {
    use super::decomposition::resolve_decomposition_style;
    let mut cases = 0;
    for levels in 0..=u8::MAX {
        for pattern in 0..4 {
            for length in [0, 1, 2, 31, 32, 33, 255] {
                for variant in 0..8 {
                    let extensions = raw_decomposition_extensions(variant, length);
                    let before = extensions.clone();
                    for selector in [None, Some(0), Some(1), Some(u8::MAX)] {
                        let mut style = raw_resolution_style(levels, pattern);
                        style.decomposition_structure = selector;
                        assert_eq!(
                            resolve_decomposition_style(style, &extensions),
                            reference_decomposition_style(style, &extensions),
                            "levels={levels}, pattern={pattern}, length={length}, variant={variant}, selector={selector:?}"
                        );
                        cases += 1;
                    }
                    assert_eq!(extensions, before);
                }
            }
        }
    }
    assert_eq!(cases, 229_376);
}

#[test]
fn actual_decomposition_ads_validates_only_raw_depths_not_levels_or_splits() {
    use super::decomposition::resolve_decomposition_style;
    let mut cases = 0;
    for depth in 0..=u8::MAX {
        for position in [0, 1, 3] {
            let mut extensions = raw_decomposition_extensions(5, 0);
            extensions.arbitrary_decompositions[0].sublevel_depths = vec![1, 2, 3, 1];
            extensions.arbitrary_decompositions[0].sublevel_depths[position] = depth;
            for levels in [0, 1, 32, 33, u8::MAX] {
                for selector in [None, Some(0)] {
                    let mut style = raw_resolution_style(levels, 6);
                    style.decomposition_structure = selector;
                    assert_eq!(
                        resolve_decomposition_style(style, &extensions),
                        reference_decomposition_style(style, &extensions)
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 7_680);
    for count in 0..=u8::MAX {
        for levels in 0..=u8::MAX {
            let mut extensions = raw_decomposition_extensions(5, 0);
            let ads = &mut extensions.arbitrary_decompositions[0];
            ads.sublevel_depths = vec![3; usize::from(count)];
            ads.subband_splits = vec![DecompositionDirection::None; usize::from(count)];
            let mut style = raw_resolution_style(levels, 7);
            style.decomposition_structure = Some(0);
            assert_eq!(resolve_decomposition_style(style, &extensions), Ok(style));
        }
    }
}

fn component_application_reader_state(parser: &Parser<'_>) -> PacketAdmissionState {
    PacketAdmissionState {
        position: parser.position,
        work: parser.work_units,
        header_bytes: parser.packet_length_bytes,
        packet_count: parser.packet_lengths,
    }
}

fn assert_component_depth_application(
    parser: &Parser<'_>,
    size: ImageSize,
    depths: &[ComponentBitDepth],
) {
    let before = component_application_reader_state(parser);
    let mut expected = size;
    let expected_result =
        reference_component_depth_application(&mut expected, depths, parser.position);
    let mut actual = size;
    assert_eq!(
        parser.apply_component_bit_depths(&mut actual, depths),
        expected_result
    );
    assert_eq!(actual, expected);
    assert_packet_admission_state(parser, before, parser.input, parser.limits);
}

fn assert_component_registration_application(
    parser: &Parser<'_>,
    size: ImageSize,
    registrations: &[ComponentRegistration],
) {
    let before = component_application_reader_state(parser);
    let mut expected = size;
    let expected_result =
        reference_component_registration_application(&mut expected, registrations, parser.position);
    let mut actual = size;
    assert_eq!(
        parser.apply_component_registrations(&mut actual, registrations),
        expected_result
    );
    assert_eq!(actual, expected);
    assert_packet_admission_state(parser, before, parser.input, parser.limits);
}

#[test]
fn actual_component_uniformity_uses_physical_infos_and_every_raw_first_depth() {
    let mut contexts = 0;
    for components in [
        0,
        1,
        2,
        MAX_COMPONENTS as u16 - 1,
        MAX_COMPONENTS as u16,
        MAX_COMPONENTS as u16 + 1,
        u16::MAX,
    ] {
        for variant in 0..3 {
            let size = raw_component_application_size(components, variant);
            for precision in 0..=u8::MAX {
                for signed in [false, true] {
                    let first = ComponentInfo {
                        precision,
                        signed,
                        x_subsampling: 0,
                        y_subsampling: u8::MAX,
                        x_registration: u16::MAX,
                        y_registration: 0,
                    };
                    assert_eq!(
                        component_depths_uniform(&size, first),
                        reference_uniform_component_depths(&size, first)
                    );
                    contexts += 1;
                }
            }
        }
    }
    assert_eq!(contexts, 10_752);
}

#[test]
fn actual_decomposition_owner_preserves_error_prefixes_all_slots_and_immutable_reader() {
    let input = [0xa5, 0x5a];
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX;
    parser.packet_lengths = u64::MAX;
    let mut cases = 0;
    for components in [0, 1, 2, 63, 64, 65, u16::MAX] {
        for pattern in 0..4 {
            for variant in 0..8 {
                for length in [0, 1, 2, 31, 32, 33] {
                    let extensions = raw_decomposition_extensions(variant, length);
                    let extension_before = extensions.clone();
                    for bad in [None, Some(0), Some(1), Some(MAX_COMPONENTS - 1)] {
                        let styles = core::array::from_fn(|index| {
                            let mut style = raw_resolution_style(
                                if pattern < 2 {
                                    2
                                } else {
                                    [0, 1, 32, 33, u8::MAX][index % 5]
                                },
                                index % 8,
                            );
                            style.decomposition_structure = if bad == Some(index) {
                                Some(253)
                            } else if pattern == 1 || index % 3 == 1 {
                                None
                            } else if pattern == 3 {
                                Some(u8::MAX)
                            } else {
                                Some(0)
                            };
                            style
                        });
                        for position in [0, usize::MAX] {
                            parser.position = position;
                            let before = PacketAdmissionState {
                                position,
                                work: parser.work_units,
                                header_bytes: parser.packet_length_bytes,
                                packet_count: parser.packet_lengths,
                            };
                            let mut actual = ComponentCodingStyles { components, styles };
                            let mut expected = actual;
                            let result = reference_decomposition_owner(&mut expected, &extensions);
                            assert_eq!(
                                parser.resolve_decomposition_structures(&mut actual, &extensions),
                                result
                            );
                            assert_eq!(
                                (actual.components, actual.styles),
                                (expected.components, expected.styles)
                            );
                            assert_packet_admission_state(&parser, before, &input, &limits);
                            assert_eq!(extensions, extension_before);
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 10_752);
}

#[test]
fn actual_component_depth_application_preserves_prefix_errors_flags_tails_and_reader() {
    let input = [0xa5, 0x5a];
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX;
    parser.packet_lengths = u64::MAX;
    let mut contexts = 0;
    for components in [
        0,
        1,
        2,
        MAX_COMPONENTS as u16 - 1,
        MAX_COMPONENTS as u16,
        MAX_COMPONENTS as u16 + 1,
        u16::MAX,
    ] {
        for variant in 0..3 {
            for uniform_bit_depth in [None, Some(0), Some(u8::MAX)] {
                for uniform_signed in [None, Some(false), Some(true)] {
                    let mut size = raw_component_application_size(components, variant);
                    size.uniform_bit_depth = uniform_bit_depth;
                    size.uniform_signed = uniform_signed;
                    for length in [
                        0,
                        1,
                        2,
                        MAX_COMPONENTS - 1,
                        MAX_COMPONENTS,
                        MAX_COMPONENTS + 1,
                    ] {
                        for pattern in 0..5 {
                            let depths: Vec<_> = (0..length)
                                .map(|index| ComponentBitDepth {
                                    precision: match pattern {
                                        0 => 0,
                                        1 => 7,
                                        2 => u8::MAX,
                                        _ => (index as u8).wrapping_mul(17),
                                    },
                                    signed: pattern == 2 || (pattern == 4 && index % 2 != 0),
                                })
                                .collect();
                            for position in [0, 17, usize::MAX] {
                                parser.position = position;
                                assert_component_depth_application(&parser, size, &depths);
                                contexts += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 17_010);
    let mut words = 0;
    parser.position = usize::MAX;
    for precision in 0..=u8::MAX {
        for signed in [false, true] {
            for components in [0, 1, 2, MAX_COMPONENTS as u16, MAX_COMPONENTS as u16 + 1] {
                let size = raw_component_application_size(components, 2);
                for length in [1, 2, MAX_COMPONENTS] {
                    let depths = vec![ComponentBitDepth { precision, signed }; length];
                    assert_component_depth_application(&parser, size, &depths);
                    words += 1;
                }
            }
        }
    }
    assert_eq!(words, 7_680);
}

#[test]
fn actual_decomposition_resolution_consumes_real_dfs_ads_reader_producers() {
    let mut input = segment(DFS, &raw_dfs_payload(5, 2));
    input.extend(segment(ADS, &raw_ads_payload(7, 3, 4, 1)));
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let mut extensions = raw_decomposition_extensions(0, 0);
    extensions.metadata_bytes = 0;
    extensions
        .decomposition_structures
        .push(DecompositionStructure {
            index: 5,
            directions: vec![],
        });
    extensions
        .decomposition_structures
        .push(DecompositionStructure {
            index: 5,
            directions: vec![DecompositionDirection::Horizontal],
        });
    extensions
        .arbitrary_decompositions
        .push(ArbitraryDecomposition {
            index: 7,
            sublevel_depths: vec![0],
            subband_splits: vec![],
        });
    extensions
        .arbitrary_decompositions
        .push(ArbitraryDecomposition {
            index: 7,
            sublevel_depths: vec![255],
            subband_splits: vec![],
        });
    let raw = parser.read_segment().unwrap();
    parser.parse_dfs(raw, &mut extensions).unwrap();
    let raw = parser.read_segment().unwrap();
    parser.parse_ads(raw, &mut extensions).unwrap();
    assert!(core::ptr::eq(
        extensions.decomposition_structure(5).unwrap(),
        &extensions.decomposition_structures[0]
    ));
    assert!(core::ptr::eq(
        extensions.arbitrary_decomposition(7).unwrap(),
        &extensions.arbitrary_decompositions[0]
    ));
    let mut dfs_style = raw_resolution_style(7, 6);
    dfs_style.decomposition_structure = Some(5);
    let mut ads_style = raw_resolution_style(u8::MAX, 4);
    ads_style.decomposition_structure = Some(7);
    let mut owner = ComponentCodingStyles::new(2, dfs_style).unwrap();
    owner.set(1, ads_style).unwrap();
    let mut expected = owner;
    reference_decomposition_owner(&mut expected, &extensions).unwrap();
    let before = PacketAdmissionState {
        position: parser.position,
        work: parser.work_units,
        header_bytes: parser.packet_length_bytes,
        packet_count: parser.packet_lengths,
    };
    let extension_before = extensions.clone();
    parser
        .resolve_decomposition_structures(&mut owner, &extensions)
        .unwrap();
    assert_eq!(
        (owner.components, owner.styles),
        (expected.components, expected.styles)
    );
    assert_eq!(owner.styles[1], ads_style);
    let directions = &extensions.decomposition_structures[0].directions;
    assert_eq!(&owner.styles[0].decomposition_directions[..2], directions);
    assert!(
        owner.styles[0].decomposition_directions[2..7]
            .iter()
            .all(|direction| direction == directions.last().unwrap())
    );
    assert_eq!(parser.position, input.len());
    assert_packet_admission_state(&parser, before, &input, &limits);
    assert_eq!(extensions, extension_before);
}

#[test]
fn actual_component_registration_preserves_native_bounds_order_and_every_raw_fraction() {
    let input = [0xa5, 0x5a];
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX;
    parser.packet_lengths = u64::MAX;
    let mut contexts = 0;
    for components in [
        0,
        1,
        2,
        MAX_COMPONENTS as u16 - 1,
        MAX_COMPONENTS as u16,
        MAX_COMPONENTS as u16 + 1,
        u16::MAX,
    ] {
        for variant in 0..3 {
            for uniform_bit_depth in [None, Some(0), Some(u8::MAX)] {
                for uniform_signed in [None, Some(false), Some(true)] {
                    let mut size = raw_component_application_size(components, variant);
                    size.uniform_bit_depth = uniform_bit_depth;
                    size.uniform_signed = uniform_signed;
                    for length in [
                        0,
                        1,
                        2,
                        MAX_COMPONENTS - 1,
                        MAX_COMPONENTS,
                        MAX_COMPONENTS + 1,
                    ] {
                        for pattern in 0..3 {
                            let registrations: Vec<_> = (0..length)
                                .map(|index| ComponentRegistration {
                                    horizontal: if pattern == 0 {
                                        0
                                    } else {
                                        (index as u16).wrapping_mul(257)
                                    },
                                    vertical: if pattern == 2 { u16::MAX } else { index as u16 },
                                })
                                .collect();
                            for position in [0, 17, usize::MAX] {
                                parser.position = position;
                                assert_component_registration_application(
                                    &parser,
                                    size,
                                    &registrations,
                                );
                                contexts += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 10_206);
    parser.position = usize::MAX;
    let size = raw_component_application_size(1, 1);
    for horizontal in 0..=u16::MAX {
        assert_component_registration_application(
            &parser,
            size,
            &[ComponentRegistration {
                horizontal,
                vertical: u16::MAX - horizontal,
            }],
        );
    }
}

#[test]
fn actual_component_application_consumes_real_siz_cbd_crg_reader_producers() {
    let mut siz = vec![0, 0];
    for word in [32_u32, 32, 0, 0, 32, 32, 0, 0] {
        siz.extend(word.to_be_bytes());
    }
    siz.extend(2_u16.to_be_bytes());
    siz.extend([7, 1, 1, 7, 1, 1]);
    let mut input = segment(SIZ, &siz);
    input.extend(segment(CBD, &[0, 2, 7, 0x87]));
    input.extend(segment(CRG, &[0x12, 0x34, 0xab, 0xcd, 0xff, 0xff, 0, 1]));
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let raw = parser.read_segment().unwrap();
    let (mut size, _) = parser.parse_siz(raw).unwrap();
    let mut extensions = Part2Extensions::default();
    let raw = parser.read_segment().unwrap();
    parser
        .parse_cbd(raw, size.components, &mut extensions)
        .unwrap();
    let raw = parser.read_segment().unwrap();
    parser
        .parse_crg(raw, size.components, &mut extensions)
        .unwrap();
    let before = component_application_reader_state(&parser);
    let original = size;
    parser
        .apply_component_bit_depths(&mut size, &extensions.component_bit_depths)
        .unwrap();
    parser
        .apply_component_registrations(&mut size, &extensions.component_registrations)
        .unwrap();
    assert_eq!(
        (size.components, size.uniform_bit_depth, size.uniform_signed),
        (2, None, None)
    );
    assert_eq!(
        (
            size.component_info[0].precision,
            size.component_info[0].signed
        ),
        (8, false)
    );
    assert_eq!(
        (
            size.component_info[1].precision,
            size.component_info[1].signed
        ),
        (8, true)
    );
    assert_eq!(
        (
            size.component_info[0].x_registration,
            size.component_info[0].y_registration
        ),
        (0x1234, 0xabcd)
    );
    assert_eq!(
        (
            size.component_info[1].x_registration,
            size.component_info[1].y_registration
        ),
        (u16::MAX, 1)
    );
    assert_eq!(size.component_info[2..], original.component_info[2..]);
    assert_eq!(
        (size.width, size.height, size.tiles_across, size.tiles_down),
        (32, 32, 1, 1)
    );
    assert_eq!(parser.position, input.len());
    assert_packet_admission_state(&parser, before, &input, &limits);
}

#[test]
fn raw_component_quantization_and_roi_getters_preserve_logical_physical_policy() {
    let quantization = raw_subband_quantization(QuantizationStyle::ScalarDerived, u16::MAX, 7);
    let roi = RoiShifts {
        shifts: core::array::from_fn(|index| u8::try_from(index).unwrap().wrapping_mul(17)),
    };
    for components in [0, 1, 2, 63, 64, 65, u16::MAX] {
        for physical in [0, 1, 2, 64, 65] {
            let values = ComponentQuantizations {
                components,
                quantizations: vec![quantization; physical],
            };
            for component in 0..=u16::MAX {
                let expected = if component < components && usize::from(component) < physical {
                    Ok(quantization)
                } else {
                    Err(DecodeError::MalformedInput {
                        offset: 0,
                        kind: MalformedKind::InvalidQuantization,
                    })
                };
                assert_eq!(values.quantization(component), expected);
            }
        }
    }
    for component in 0..=u16::MAX {
        let expected =
            roi.shifts
                .get(usize::from(component))
                .copied()
                .ok_or(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::InvalidRegionOfInterest,
                });
        assert_eq!(roi.shift(component), expected);
    }
}

fn reference_component_plan_metadata(
    size: &ImageSize,
    styles: &ComponentCodingStyles,
    quantizations: &ComponentQuantizations,
    roi: &RoiShifts,
    component: u16,
    selection: (u16, u8),
    force: bool,
) -> Result<crate::decode::PlannedComponentMetadata, DecodeError> {
    let invalid_style = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodingStyle,
    };
    if component >= styles.components {
        return Err(invalid_style);
    }
    let style = *styles
        .styles
        .get(usize::from(component))
        .ok_or(invalid_style)?;
    if selection.1 > style.decomposition_levels {
        return Err(DecodeError::InvalidSelection {
            reason: crate::SelectionError::ReductionTooLarge,
        });
    }
    let output = style.decomposition_levels - selection.1;
    let invalid_quant = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidQuantization,
    };
    if component >= quantizations.components {
        return Err(invalid_quant);
    }
    let quantization = quantizations
        .quantizations
        .get(usize::from(component))
        .ok_or(invalid_quant)?;
    let mut tier1_style =
        crate::tier1::tier1_coding_style_from_code_block_style(style.code_block_style)?;
    if force
        && matches!(
            tier1_style.block_coding,
            crate::tier1::Tier1BlockCoding::HighThroughput | crate::tier1::Tier1BlockCoding::Mixed
        )
    {
        tier1_style.force_high_throughput = true;
    }
    let bounds = reference_tile_component_bounds(size, selection.0, component)?;
    let geometry =
        reference_resolution_geometry(size, style, component, output, Some(selection.0))?;
    let scale = (0..selection.1).try_fold((1, 1), |previous, stage| {
        reference_resolution_scale_step(style, stage, previous)
    })?;
    let invalid_geometry = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidImageGeometry,
    };
    if component >= size.components {
        return Err(invalid_geometry);
    }
    let info = size
        .component_info
        .get(usize::from(component))
        .ok_or(invalid_geometry)?;
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    };
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let ceil = |value: u32, divisor: u32| {
        if divisor == 0 {
            return Err(invalid);
        }
        Ok(u32::try_from(u64::from(value).div_ceil(u64::from(divisor))).unwrap())
    };
    let origin_x = ceil(size.x_origin, u32::from(info.x_subsampling))?;
    let origin_y = ceil(size.y_origin, u32::from(info.y_subsampling))?;
    let x =
        u32::try_from(i64::from(ceil(bounds.x0, scale.0)?) - i64::from(ceil(origin_x, scale.0)?))
            .map_err(|_| arithmetic)?;
    let y =
        u32::try_from(i64::from(ceil(bounds.y0, scale.1)?) - i64::from(ceil(origin_y, scale.1)?))
            .map_err(|_| arithmetic)?;
    let shift = *roi
        .shifts
        .get(usize::from(component))
        .ok_or(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidRegionOfInterest,
        })?;
    let subbands = reference_component_subbands(
        size,
        style,
        quantization,
        component,
        Some(selection.0),
        shift,
    )?;
    Ok(crate::decode::PlannedComponentMetadata {
        component_coding_style: style,
        output_resolution: output,
        tier1_style,
        bounds,
        component_width: geometry.width,
        component_height: geometry.height,
        component_x: x,
        component_y: y,
        subbands,
    })
}

#[test]
fn actual_component_plan_metadata_preserves_all_ordered_raw_admission_and_output_fields() {
    let mut cases = 0;
    let mut successes = 0;
    for components in [0, 1, 2, 64, 65, u16::MAX] {
        let mut size = raw_resolution_size(33, 1, (1, 1), 0, components);
        for info in &mut size.component_info {
            info.precision = 8;
        }
        for style_owner in [0, 1, 2, 64, u16::MAX] {
            for quant_owner in [0, 1, 2, u16::MAX] {
                for physical in [0, 1, 2] {
                    let quantizations = ComponentQuantizations {
                        components: quant_owner,
                        quantizations: vec![
                            raw_subband_quantization(
                                QuantizationStyle::ScalarDerived,
                                1,
                                4
                            );
                            physical
                        ],
                    };
                    for component in [0, 1, 63, 64, u16::MAX] {
                        for tile in [0, u16::MAX] {
                            for discard in [0, 1, 2, u8::MAX] {
                                let roi = RoiShifts {
                                    shifts: [if discard == 1 { u8::MAX } else { 0 };
                                        MAX_COMPONENTS],
                                };
                                for code_style in [0, 0x40, 0xc0, 0xff] {
                                    let mut style = raw_resolution_style(1, 3);
                                    style.code_block_style = code_style;
                                    style.code_block_width = 4;
                                    style.code_block_height = 4;
                                    style.precinct_exponents = [(0, 0); 33];
                                    let styles = ComponentCodingStyles {
                                        components: style_owner,
                                        styles: [style; MAX_COMPONENTS],
                                    };
                                    for force in [false, true] {
                                        let expected = reference_component_plan_metadata(
                                            &size,
                                            &styles,
                                            &quantizations,
                                            &roi,
                                            component,
                                            (tile, discard),
                                            force,
                                        );
                                        assert_eq!(
                                            crate::decode::prepare_component_plan_metadata(
                                                &size,
                                                &styles,
                                                &quantizations,
                                                &roi,
                                                component,
                                                (tile, discard),
                                                force
                                            ),
                                            expected,
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
    }
    assert_eq!(cases, 115_200);
    assert!(
        successes > 100,
        "{successes} full component metadata owners checked"
    );
}

fn reference_resolution_count(style: CodingStyle, resolution: u8) -> Result<usize, DecodeError> {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodingStyle,
    };
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    if resolution > style.decomposition_levels {
        return Err(invalid);
    }
    let mut count = 1_u128;
    for current in 1..=u16::from(resolution) {
        let stage = u16::from(style.decomposition_levels) - current;
        count += match style
            .decomposition_directions
            .get(usize::from(stage))
            .ok_or(invalid)?
        {
            DecompositionDirection::None => 0,
            DecompositionDirection::Horizontal | DecompositionDirection::Vertical => 1,
            DecompositionDirection::TwoDimensional => 3,
        };
        if count > usize::MAX as u128 {
            return Err(arithmetic);
        }
    }
    Ok(usize::try_from(count).unwrap())
}

fn reference_resolution_plan_metadata(
    size: &ImageSize,
    style: CodingStyle,
    component: u16,
    selection: (u16, u8),
    origin: [u32; 2],
) -> Result<crate::decode::ResolutionPlanMetadata, DecodeError> {
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    };
    let invalid_style = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodingStyle,
    };
    let resolution = selection.1;
    let geometry =
        reference_resolution_geometry(size, style, component, resolution, Some(selection.0))?;
    let first = if resolution == 0 {
        0
    } else {
        reference_resolution_count(style, resolution - 1)?
    };
    let last = reference_resolution_count(style, resolution)?;
    let count = usize::try_from(last as i128 - first as i128).map_err(|_| arithmetic)?;
    let precincts = if count == 0 {
        0
    } else {
        u32::try_from(geometry.precincts).map_err(|_| arithmetic)?
    };
    let p = *style
        .precinct_exponents
        .get(usize::from(resolution))
        .ok_or(invalid_style)?;
    if p.0 > 31 || p.1 > 31 {
        return Err(invalid);
    }
    let scale = (0..style.decomposition_levels - resolution)
        .try_fold((1, 1), |before, stage| {
            reference_resolution_scale_step(style, stage, before)
        })?;
    let x0 = u32::try_from(u64::from(origin[0]).div_ceil(u64::from(scale.0))).unwrap();
    let y0 = u32::try_from(u64::from(origin[1]).div_ceil(u64::from(scale.1))).unwrap();
    let pw = 1_u32 << p.0;
    let ph = 1_u32 << p.1;
    let first_precinct = [x0 / pw, y0 / ph];
    let direction = if resolution == 0 {
        DecompositionDirection::None
    } else {
        *style
            .decomposition_directions
            .get(usize::from(style.decomposition_levels - resolution))
            .ok_or(invalid_style)?
    };
    let split_x = matches!(
        direction,
        DecompositionDirection::Horizontal | DecompositionDirection::TwoDimensional
    );
    let split_y = matches!(
        direction,
        DecompositionDirection::Vertical | DecompositionDirection::TwoDimensional
    );
    let bx = if split_x {
        p.0.checked_sub(1).ok_or(invalid)?
    } else {
        p.0
    };
    let by = if split_y {
        p.1.checked_sub(1).ok_or(invalid)?
    } else {
        p.1
    };
    if bx > 31 || by > 31 {
        return Err(invalid);
    }
    let bw = 1_u32 << bx;
    let bh = 1_u32 << by;
    let cw = bw.min(u32::from(style.code_block_width));
    let ch = bh.min(u32::from(style.code_block_height));
    if pw == 0 || ph == 0 || cw == 0 || ch == 0 {
        return Err(invalid);
    }
    Ok(crate::decode::ResolutionPlanMetadata {
        geometry,
        first_subband: first,
        subband_count: count,
        precincts_in_resolution: precincts,
        first_precinct,
        band_size: [bw, bh],
        block_size: [cw, ch],
    })
}

#[test]
fn actual_resolution_plan_metadata_preserves_complete_raw_geometry_counts_split_and_origin_fields()
{
    let mut cases = 0;
    let mut successes = 0;
    let mut lazy_narrowing = 0;
    for large in [false, true] {
        let mut size = raw_resolution_size(if large { 65_536 } else { 33 }, 0, (1, 1), 0, 2);
        for info in &mut size.component_info {
            info.x_registration = 0;
            info.y_registration = 0;
        }
        if large {
            size.tile_width = 65_536;
            size.tile_height = 65_536;
            size.tiles_across = 1;
            size.tiles_down = 1;
        }
        for levels in [0, 1, 2, 31, 32, u8::MAX] {
            for resolution in [0, 1, 2, 31, u8::MAX] {
                for pattern in 0..8 {
                    for p in [
                        (0, 0),
                        (1, 1),
                        (2, 3),
                        (31, 31),
                        (32, 0),
                        (u8::MAX, u8::MAX),
                    ] {
                        for (cw, ch) in [(1, 1), (0, 1), (4, 8), (u16::MAX, u16::MAX)] {
                            let mut style = raw_resolution_style(levels, pattern);
                            style.code_block_width = cw;
                            style.code_block_height = ch;
                            style.precinct_exponents = [p; 33];
                            for component in [0, 1, 64] {
                                for tile in [0, u16::MAX] {
                                    for origin in [[0, 0], [1, 3], [u32::MAX, u32::MAX]] {
                                        let expected = reference_resolution_plan_metadata(
                                            &size,
                                            style,
                                            component,
                                            (tile, resolution),
                                            origin,
                                        );
                                        assert_eq!(
                                            crate::decode::prepare_resolution_plan_metadata(
                                                &size,
                                                style,
                                                component,
                                                (tile, resolution),
                                                origin
                                            ),
                                            expected
                                        );
                                        if let Ok(value) = expected {
                                            successes += 1;
                                            lazy_narrowing += usize::from(
                                                value.subband_count == 0
                                                    && value.geometry.precincts
                                                        > u64::from(u32::MAX),
                                            );
                                        }
                                        cases += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 207_360);
    assert!(successes > 100 && lazy_narrowing > 0);
}

fn raw_mct_identity_fixture(variant: usize) -> MultipleComponentTransform {
    let matrix = MctArray {
        index: 1,
        kind: MctArrayKind::Decorrelation,
        numeric_format: MctNumericFormat::Int16,
        fraction_bits: 0,
        values: vec![1, 0, 0, 1],
    };
    let offsets = MctArray {
        index: 2,
        kind: MctArrayKind::Offset,
        numeric_format: MctNumericFormat::Int32,
        fraction_bits: 0,
        values: vec![0, 0],
    };
    let collection = MctCollection {
        reversible: true,
        input_components: vec![0, 1],
        output_components: vec![0, 1],
        kind: MctCollectionKind::Decorrelation,
        matrix: Some(matrix),
        offsets: Some(offsets),
        wavelet: None,
    };
    let mut value = MultipleComponentTransform {
        stages: vec![MctStage {
            index: 1,
            collections: vec![collection],
        }],
    };
    match variant {
        0 => {}
        1 => value.stages.clear(),
        2 => value.stages.push(value.stages[0].clone()),
        3 => value.stages[0].index = u8::MAX,
        4 => value.stages[0].collections.clear(),
        5 => {
            let collection = value.stages[0].collections[0].clone();
            value.stages[0].collections.push(collection);
        }
        6 => value.stages[0].collections[0].reversible = false,
        7 => value.stages[0].collections[0].input_components.reverse(),
        8 => value.stages[0].collections[0]
            .output_components
            .push(u16::MAX),
        9 => value.stages[0].collections[0].kind = MctCollectionKind::Dependency,
        10 => value.stages[0].collections[0].matrix = None,
        11 => {
            value.stages[0].collections[0]
                .matrix
                .as_mut()
                .unwrap()
                .index = 2
        }
        12 => {
            value.stages[0].collections[0].matrix.as_mut().unwrap().kind = MctArrayKind::Dependency
        }
        13 => {
            value.stages[0].collections[0]
                .matrix
                .as_mut()
                .unwrap()
                .numeric_format = MctNumericFormat::Float32
        }
        14 => {
            value.stages[0].collections[0]
                .matrix
                .as_mut()
                .unwrap()
                .fraction_bits = u8::MAX
        }
        15 => {
            value.stages[0].collections[0]
                .matrix
                .as_mut()
                .unwrap()
                .values[0] = i64::MIN
        }
        16 => {
            value.stages[0].collections[0]
                .matrix
                .as_mut()
                .unwrap()
                .values
                .pop();
        }
        17 => value.stages[0].collections[0].offsets = None,
        18 => {
            value.stages[0].collections[0]
                .offsets
                .as_mut()
                .unwrap()
                .values[0] = i64::MAX
        }
        19 => {
            value.stages[0].collections[0].wavelet = Some(MctWavelet {
                transform: MctWaveletType::Reversible5x3,
                levels: 0,
                component_offset: 0,
            })
        }
        20 => {
            value.stages[0].collections[0].wavelet = Some(MctWavelet {
                transform: MctWaveletType::Irreversible9x7,
                levels: 0,
                component_offset: 0,
            })
        }
        21 => {
            value.stages[0].collections[0].wavelet = Some(MctWavelet {
                transform: MctWaveletType::Reversible5x3,
                levels: u8::MAX,
                component_offset: i32::MIN,
            })
        }
        22 => {
            value.stages[0].collections[0]
                .offsets
                .as_mut()
                .unwrap()
                .numeric_format = MctNumericFormat::Float64
        }
        _ => value.stages[0].collections[0].kind = MctCollectionKind::Wavelet,
    }
    value
}

#[test]
fn actual_mct_identity_compares_every_raw_graph_array_stage_and_collection_field() {
    let mut cases = 0;
    for left in 0..24 {
        for right in 0..24 {
            let left = raw_mct_identity_fixture(left);
            let right = raw_mct_identity_fixture(right);
            assert_eq!(left.equals(&right), left == right);
            assert_eq!(
                crate::decode::optional_multiple_component_transforms_equal(
                    Some(&left),
                    Some(&right)
                ),
                left == right
            );
            for (a, b) in left.stages.iter().zip(&right.stages) {
                assert_eq!(a.equals(b), a == b);
                for (a, b) in a.collections.iter().zip(&b.collections) {
                    assert_eq!(a.equals(b), a == b);
                    for (a, b) in [
                        a.matrix.as_ref().zip(b.matrix.as_ref()),
                        a.offsets.as_ref().zip(b.offsets.as_ref()),
                    ]
                    .into_iter()
                    .flatten()
                    {
                        assert_eq!(a.equals(b), a == b);
                    }
                }
            }
            cases += 1;
        }
    }
    assert_eq!(cases, 576);
    let empty = MultipleComponentTransform { stages: Vec::new() };
    assert!(!crate::decode::optional_multiple_component_transforms_equal(Some(&empty), None));
    assert!(crate::decode::optional_multiple_component_transforms_equal(
        None, None
    ));
}

#[test]
fn actual_maximum_isotropic_reduction_preserves_full_u8_levels_and_physical_prefix_laziness() {
    let mut cases = 0;
    for levels in 0..=u8::MAX {
        for pattern in 0..8 {
            for stop in 0..=32 {
                let mut style = raw_resolution_style(levels, pattern);
                for direction in style.decomposition_directions.iter_mut().take(stop) {
                    *direction = DecompositionDirection::TwoDimensional;
                }
                if stop < 32 {
                    style.decomposition_directions[stop] = DecompositionDirection::None;
                }
                let expected = style
                    .decomposition_directions
                    .iter()
                    .take(usize::from(levels).min(32))
                    .take_while(|direction| {
                        matches!(direction, DecompositionDirection::TwoDimensional)
                    })
                    .count();
                assert_eq!(usize::from(style.maximum_isotropic_reduction()), expected);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 67_584);
}

fn reference_tile_component_resolutions(
    styles: &ComponentCodingStyles,
    main: CodingStyle,
    components: u16,
    discard: Option<u8>,
) -> Result<Vec<u8>, DecodeError> {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodingStyle,
    };
    let reduction = DecodeError::InvalidSelection {
        reason: crate::SelectionError::ReductionTooLarge,
    };
    let count = if discard.is_some() {
        components
    } else if main.multiple_component_transform {
        components.min(3)
    } else {
        0
    };
    let mut output = Vec::new();
    for component in 0..count {
        if component >= styles.components {
            return Err(invalid);
        }
        let style = styles.styles.get(usize::from(component)).ok_or(invalid)?;
        if let Some(discard) = discard {
            let maximum = style
                .decomposition_directions
                .iter()
                .take(usize::from(style.decomposition_levels).min(32))
                .take_while(|direction| matches!(direction, DecompositionDirection::TwoDimensional))
                .count();
            if usize::from(discard) > maximum {
                return Err(reduction);
            }
        }
        let agreement = matches!(
            (style.transform, main.transform),
            (
                WaveletTransform::Reversible5x3,
                WaveletTransform::Reversible5x3
            ) | (
                WaveletTransform::Irreversible9x7,
                WaveletTransform::Irreversible9x7
            )
        );
        if main.multiple_component_transform && component < 3 && !agreement {
            return Err(invalid);
        }
        if let Some(discard) = discard {
            if style.decomposition_levels == u8::MAX {
                return Err(reduction);
            }
            output.push(
                u8::try_from(i16::from(style.decomposition_levels) + 1 - i16::from(discard))
                    .map_err(|_| reduction)?,
            );
        }
    }
    Ok(output)
}

#[test]
fn actual_tile_style_resolution_preparation_preserves_raw_modes_owners_and_arbitrary_agreement_policy()
 {
    let mut cases = 0;
    let modes = [
        None,
        Some(0),
        Some(1),
        Some(2),
        Some(31),
        Some(32),
        Some(u8::MAX),
    ];
    for levels in [0, 1, 2, 31, 32, u8::MAX] {
        for pattern in 0..8 {
            for logical in [0, 1, 2, 3, 64, 65, u16::MAX] {
                for components in [0, 1, 2, 3, 64, u16::MAX] {
                    for flag in [false, true] {
                        for main_transform in [
                            WaveletTransform::Reversible5x3,
                            WaveletTransform::Irreversible9x7,
                            WaveletTransform::Arbitrary(3),
                        ] {
                            let mut main = raw_resolution_style(levels, pattern);
                            main.multiple_component_transform = flag;
                            main.transform = main_transform;
                            for transform in [
                                main_transform,
                                WaveletTransform::Reversible5x3,
                                WaveletTransform::Arbitrary(3),
                            ] {
                                let mut style = raw_resolution_style(levels, pattern);
                                style.transform = transform;
                                let styles = ComponentCodingStyles {
                                    components: logical,
                                    styles: [style; MAX_COMPONENTS],
                                };
                                for mode in modes {
                                    assert_eq!(
                                        crate::decode::prepare_tile_component_resolutions(
                                            &styles, main, components, mode
                                        ),
                                        reference_tile_component_resolutions(
                                            &styles, main, components, mode
                                        )
                                    );
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 254_016);
}

fn reference_tile_decode_metadata(
    parts: &[TilePartPayload<'_>],
    components: u16,
    discard: Option<u8>,
) -> Result<((bool, bool), Vec<u8>), DecodeError> {
    let first = parts.first().ok_or(DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTilePart,
    })?;
    if parts
        .iter()
        .any(|part| part.multiple_component_transform != first.multiple_component_transform)
    {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidTransform,
        });
    }
    let irreversible = match first.coding_style.transform {
        WaveletTransform::Irreversible9x7 => true,
        WaveletTransform::Reversible5x3 => false,
        WaveletTransform::Arbitrary(index) => {
            !first
                .part2_extensions
                .arbitrary_kernels
                .iter()
                .find(|kernel| kernel.index == index)
                .ok_or(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::MissingRequiredStructure,
                })?
                .reversible
        }
    };
    Ok((
        (
            first.coding_style.multiple_component_transform,
            irreversible,
        ),
        reference_tile_component_resolutions(
            &first.component_coding_styles,
            first.coding_style,
            components,
            discard,
        )?,
    ))
}

#[test]
fn actual_tile_metadata_derives_first_payload_mct_kernel_and_ordered_style_results() {
    let bytes = codestream(&[0], false);
    let layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
    let template = &layout.tile_parts[0];
    let modes = [
        None,
        Some(0),
        Some(1),
        Some(2),
        Some(31),
        Some(32),
        Some(u8::MAX),
    ];
    let mut cases = 0;
    let mut successes = 0;
    for shape in 0..6 {
        for components in [0, 1, 3, u16::MAX] {
            for mode in modes {
                for transform in [
                    WaveletTransform::Reversible5x3,
                    WaveletTransform::Irreversible9x7,
                    WaveletTransform::Arbitrary(3),
                    WaveletTransform::Arbitrary(4),
                ] {
                    for flag in [false, true] {
                        for logical in [0, 1, 64, u16::MAX] {
                            for pattern in [0, 3, 7] {
                                for registry in 0..3 {
                                    let mut first = template.clone();
                                    first.coding_style.transform = transform;
                                    first.coding_style.multiple_component_transform = flag;
                                    let mut style = raw_resolution_style(
                                        if pattern == 7 { u8::MAX } else { 2 },
                                        pattern,
                                    );
                                    style.transform = transform;
                                    first.component_coding_styles = ComponentCodingStyles {
                                        components: logical,
                                        styles: [style; MAX_COMPONENTS],
                                    };
                                    let kernel = |reversible| ArbitraryKernel {
                                        index: 3,
                                        reversible,
                                        descriptor: u16::MAX,
                                        coefficient_type: u8::MAX,
                                        whole_sample_filter: false,
                                        initial_odd: true,
                                        whole_sample_extension: false,
                                        scaling: None,
                                        steps: Vec::new(),
                                    };
                                    first.part2_extensions.arbitrary_kernels = match registry {
                                        0 => Vec::new(),
                                        1 => vec![kernel(true)],
                                        _ => vec![kernel(false), kernel(true)],
                                    };
                                    let mut second = first.clone();
                                    match shape {
                                        3 => {
                                            first.multiple_component_transform =
                                                Some(MultipleComponentTransform {
                                                    stages: Vec::new(),
                                                })
                                        }
                                        4 => {
                                            first.multiple_component_transform =
                                                Some(raw_mct_identity_fixture(0));
                                            second.multiple_component_transform =
                                                Some(raw_mct_identity_fixture(3));
                                        }
                                        5 => {
                                            first.multiple_component_transform =
                                                Some(raw_mct_identity_fixture(0));
                                            second.multiple_component_transform =
                                                Some(raw_mct_identity_fixture(0));
                                        }
                                        _ => {}
                                    }
                                    let parts = match shape {
                                        0 => Vec::new(),
                                        1 => vec![first],
                                        _ => vec![first, second],
                                    };
                                    let expected =
                                        reference_tile_decode_metadata(&parts, components, mode);
                                    let actual = crate::decode::prepare_tile_decode_metadata(
                                        &parts, components, mode,
                                    )
                                    .map(|value| {
                                        assert!(core::ptr::eq(value.first, &parts[0]));
                                        (value.standard, value.resolution_counts)
                                    });
                                    successes += usize::from(expected.is_ok());
                                    assert_eq!(actual, expected);
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 48_384);
    assert!(successes > 100);
}

fn reference_capability_word(caps: &ExtendedCapabilities, part: u8) -> Option<u16> {
    if part == 0 || part > 32 {
        return None;
    }
    if caps.p_cap & (1_u32 << (32 - u32::from(part))) == 0 {
        return None;
    }
    let index = (1..part)
        .filter(|prior| caps.p_cap & (1_u32 << (32 - u32::from(*prior))) != 0)
        .count();
    caps.c_capabilities.get(index).copied()
}

#[test]
fn actual_capability_lookup_preserves_all_u8_parts_raw_masks_and_ragged_physical_words() {
    let masks = [
        0,
        1,
        0x8000_0000,
        PART_15_CAPABILITY_FLAG,
        PART_15_CAPABILITY_FLAG | 0x8000_0000,
        u32::MAX,
        0xaaaa_5555,
        0x5555_aaaa,
        u32::MAX ^ PART_15_CAPABILITY_FLAG,
    ];
    let mut cases = 0;
    for mask in masks {
        for physical in [0, 1, 2, 14, 15, 31, 32, 33] {
            let caps = ExtendedCapabilities {
                p_cap: mask,
                c_capabilities: (0..physical)
                    .map(|index| u16::try_from(index).unwrap().wrapping_mul(2_177))
                    .collect(),
            };
            for part in 0..=u8::MAX {
                assert_eq!(
                    caps.capability_for_part(part),
                    reference_capability_word(&caps, part)
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 18_432);
}

#[test]
fn actual_ht_profile_policy_preserves_every_raw_ccap_word_physical_lookup_and_unused_owner_field() {
    let mut cases = 0;
    for word in 0..=u16::MAX {
        for mask in [
            PART_15_CAPABILITY_FLAG,
            PART_15_CAPABILITY_FLAG | 0x8000_0000,
            u32::MAX,
            0,
        ] {
            let target = (1..15_u8)
                .filter(|part| mask & (1_u32 << (32 - u32::from(*part))) != 0)
                .count();
            for physical in [target, target + 1, 34] {
                let mut values = vec![u16::MAX; physical];
                if let Some(value) = values.get_mut(target) {
                    *value = word;
                }
                let caps = ExtendedCapabilities {
                    p_cap: mask,
                    c_capabilities: values,
                };
                let expected_word = reference_capability_word(&caps, 15);
                let expected_mode = expected_word.and_then(|word| match word >> 14 {
                    0 => Some(Part15BlockMode::HtOnly),
                    2 => Some(Part15BlockMode::HtDeclared),
                    3 => Some(Part15BlockMode::Mixed),
                    _ => None,
                });
                let expected_multiple = expected_word.is_some_and(|word| word & 0x2000 != 0);
                let expected_bound = expected_word.map(|word| {
                    let value = u8::try_from(word & 31).unwrap();
                    match value {
                        0 => 8,
                        1..=19 => value + 8,
                        20..=30 => (value - 19) * 4 + 27,
                        _ => 74,
                    }
                });
                assert_eq!(caps.part15_value(), expected_word);
                assert_eq!(caps.part15_block_mode(), expected_mode);
                assert_eq!(caps.part15_allows_multiple_ht_sets(), expected_multiple);
                assert_eq!(caps.part15_magnitude_bound(), expected_bound);
                for unrelated in [false, true] {
                    let profile = CodestreamProfile {
                        r_siz: if unrelated { u16::MAX } else { 0 },
                        block_coding: if unrelated {
                            CodestreamBlockCoding::Mixed
                        } else {
                            CodestreamBlockCoding::Legacy
                        },
                        extended_capabilities: Some(caps.clone()),
                        profile: unrelated.then(|| ProfileNumber {
                            words: vec![u16::MAX, 0, 17],
                        }),
                        corresponding_profile: unrelated.then(|| ProfileNumber {
                            words: vec![31, u16::MAX],
                        }),
                    };
                    assert_eq!(profile.part15_allows_multiple_ht_sets(), expected_multiple);
                    assert_eq!(
                        profile.part15_magnitude_bound(),
                        expected_bound.unwrap_or(74)
                    );
                    assert_eq!(
                        profile.part15_requires_all_ht_blocks(),
                        matches!(expected_mode, Some(Part15BlockMode::HtOnly))
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 1_572_864);
    let absent = CodestreamProfile {
        r_siz: u16::MAX,
        block_coding: CodestreamBlockCoding::HighThroughput,
        extended_capabilities: None,
        profile: Some(ProfileNumber {
            words: vec![u16::MAX],
        }),
        corresponding_profile: None,
    };
    assert!(!absent.part15_allows_multiple_ht_sets());
    assert_eq!(absent.part15_magnitude_bound(), 74);
    assert!(!absent.part15_requires_all_ht_blocks());
}

fn raw_owned_tile_part_fixture(variant: usize) -> TilePartPayload<'static> {
    let coefficient = KernelCoefficient {
        bytes: [u8::MAX; 16],
        width: u8::MAX,
    };
    let kernel = ArbitraryKernel {
        index: u8::MAX,
        reversible: variant.is_multiple_of(2),
        descriptor: u16::MAX,
        coefficient_type: u8::MAX,
        whole_sample_filter: true,
        initial_odd: false,
        whole_sample_extension: true,
        scaling: Some(coefficient),
        steps: vec![KernelLiftingStep {
            offset: i8::MIN,
            exponent: u8::MAX,
            residue: Some(coefficient),
            coefficients: vec![coefficient; variant % 4],
        }],
    };
    let nonlinear = NonlinearPointTransform {
        component: Some(u16::MAX),
        precision: 0,
        signed: true,
        transform_type: u8::MAX,
        parameters: vec![0, u8::MAX, 17],
        d_min: Some(u32::MAX),
        d_max: Some(0),
        point_bits: Some(u8::MAX),
        points: vec![0, u32::MAX, 31],
        gamma_parameters: Some([u32::MAX, 0, 1, 2, 3]),
    };
    let style = raw_resolution_style(u8::MAX, variant % 8);
    let quantization = raw_subband_quantization(QuantizationStyle::ScalarDerived, u16::MAX, 3);
    TilePartPayload {
        tile_index: u16::try_from(variant).unwrap(),
        tile_part_index: u8::try_from(variant).unwrap(),
        tile_part_count: 0,
        coding_style: style,
        quantization,
        component_coding_styles: ComponentCodingStyles {
            components: u16::MAX,
            styles: [style; MAX_COMPONENTS],
        },
        component_quantizations: ComponentQuantizations {
            components: u16::MAX,
            quantizations: vec![quantization; variant % 4],
        },
        roi_shifts: RoiShifts {
            shifts: [u8::MAX; MAX_COMPONENTS],
        },
        progression_changes: ProgressionChanges {
            records: vec![ProgressionChange {
                resolution_start: u8::MAX,
                component_start: u16::MAX,
                layer_end: 0,
                resolution_end: 0,
                component_end: 0,
                progression_order: ProgressionOrder::Cprl,
            }],
        },
        multiple_component_transform: Some(raw_mct_identity_fixture(variant % 24)),
        part2_extensions: Part2Extensions {
            decomposition_structures: vec![DecompositionStructure {
                index: u8::MAX,
                directions: vec![
                    DecompositionDirection::None,
                    DecompositionDirection::Horizontal,
                    DecompositionDirection::TwoDimensional,
                ],
            }],
            arbitrary_decompositions: vec![ArbitraryDecomposition {
                index: 0,
                sublevel_depths: vec![0, u8::MAX],
                subband_splits: vec![
                    DecompositionDirection::Vertical,
                    DecompositionDirection::None,
                ],
            }],
            nonlinear_transforms: vec![nonlinear],
            component_bit_depths: vec![
                ComponentBitDepth {
                    precision: 0,
                    signed: true,
                },
                ComponentBitDepth {
                    precision: u8::MAX,
                    signed: false,
                },
            ],
            arbitrary_kernels: vec![kernel],
            component_registrations: vec![ComponentRegistration {
                horizontal: u16::MAX,
                vertical: 0,
            }],
            tile_part_lengths: vec![
                TilePartLength {
                    tile_index: None,
                    length: u32::MAX,
                },
                TilePartLength {
                    tile_index: Some(u16::MAX),
                    length: 0,
                },
            ],
            metadata_bytes: u64::MAX,
        },
        packet_lengths: PacketLengths {
            source: PacketLengthSource::Plm(&[0, u8::MAX, 0x81]),
            packet_count: u64::MAX,
            encoded_bytes: 0,
        },
        packed_packet_headers: PackedPacketHeaders {
            source: PackedPacketHeaderSource::MarkerSegments {
                header: &[0xff, 0x61, 0, 3, 0],
                marker: 0xff61,
                logical_start: usize::MAX,
            },
            length: usize::MAX,
            fragments: u16::MAX,
        },
        has_functional_header_marker: true,
        has_roi_marker: false,
        data: &[0, 0xff, 0x81, 0x7f],
    }
}

#[test]
fn actual_owned_tile_part_clone_preserves_every_raw_field_and_independent_nested_buffers() {
    for variant in 0..24 {
        let source = raw_owned_tile_part_fixture(variant);
        let before = format!("{source:?}");
        let mut copied = source.clone();
        assert_eq!(copied, source);
        assert!(core::ptr::eq(copied.data, source.data));
        copied.component_quantizations.quantizations.clear();
        copied.progression_changes.records.clear();
        copied.part2_extensions.decomposition_structures[0]
            .directions
            .clear();
        copied.part2_extensions.arbitrary_decompositions[0]
            .sublevel_depths
            .clear();
        copied.part2_extensions.arbitrary_decompositions[0]
            .subband_splits
            .clear();
        copied.part2_extensions.nonlinear_transforms[0]
            .parameters
            .clear();
        copied.part2_extensions.nonlinear_transforms[0]
            .points
            .clear();
        copied.part2_extensions.arbitrary_kernels[0].steps[0]
            .coefficients
            .clear();
        copied.part2_extensions.arbitrary_kernels[0].steps.clear();
        copied.part2_extensions.component_bit_depths.clear();
        copied.part2_extensions.component_registrations.clear();
        copied.part2_extensions.tile_part_lengths.clear();
        if let Some(transform) = &mut copied.multiple_component_transform {
            for stage in &mut transform.stages {
                for collection in &mut stage.collections {
                    collection.input_components.clear();
                    collection.output_components.clear();
                    if let Some(array) = &mut collection.matrix {
                        array.values.clear();
                    }
                    if let Some(array) = &mut collection.offsets {
                        array.values.clear();
                    }
                }
                stage.collections.clear();
            }
            transform.stages.clear();
        }
        assert_eq!(format!("{source:?}"), before);
        assert_ne!(copied, source);
    }
}

#[test]
fn actual_ordered_tile_collection_copies_raw_non_normalized_fields_and_retains_duplicate_order() {
    let mut cases = 0;
    for length in 0..=64 {
        for pattern in 0..4 {
            let source = (0..length)
                .map(|index| {
                    let mut value = raw_owned_tile_part_fixture(index % 24);
                    value.tile_index = match pattern {
                        0 => 0,
                        1 => u16::try_from(index % 2).unwrap(),
                        2 => u16::MAX,
                        _ => u16::try_from(index % 3).unwrap(),
                    };
                    value.tile_part_index = u8::try_from(index).unwrap();
                    value
                })
                .collect::<Vec<_>>();
            for tile in [0, 1, 2, u16::MAX] {
                let actual = crate::decode::collect_tile_parts(&source, tile).unwrap();
                let expected = source
                    .iter()
                    .filter(|part| part.tile_index == tile)
                    .collect::<Vec<_>>();
                assert_eq!(actual.len(), expected.len());
                for (copied, original) in actual.iter().zip(expected) {
                    assert_eq!(copied, original);
                    assert!(core::ptr::eq(copied.data, original.data));
                }
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 1_040);
}

fn reference_truncated_subband_count(style: CodingStyle) -> u16 {
    let total = style
        .decomposition_directions
        .iter()
        .take(usize::from(style.decomposition_levels.min(32)))
        .fold(1_u32, |count, direction| {
            count
                + match direction {
                    DecompositionDirection::None => 0,
                    DecompositionDirection::Horizontal | DecompositionDirection::Vertical => 1,
                    DecompositionDirection::TwoDimensional => 3,
                }
        });
    u16::try_from(total).unwrap()
}

fn reference_subband_resolution(
    style: CodingStyle,
    bounds: [u32; 4],
    depth: [u8; 2],
    quantization: &Quantization,
    resolution: u8,
    mut before: Vec<crate::decode::SubbandGeometry>,
) -> Result<Vec<crate::decode::SubbandGeometry>, DecodeError> {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodingStyle,
    };
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    if resolution > style.decomposition_levels {
        return Err(invalid);
    }
    let scale = (0..style.decomposition_levels - resolution)
        .try_fold((1, 1), |previous, stage| {
            reference_resolution_scale_step(style, stage, previous)
        })?;
    let ceil = |value: u32, divisor: u32| {
        u32::try_from(u64::from(value).div_ceil(u64::from(divisor))).unwrap()
    };
    let [x0, y0, x1, y1] = [
        ceil(bounds[0], scale.0),
        ceil(bounds[1], scale.1),
        ceil(bounds[2], scale.0),
        ceil(bounds[3], scale.1),
    ];
    let dimensions = [
        u32::try_from(i64::from(x1) - i64::from(x0)).map_err(|_| arithmetic)?,
        u32::try_from(i64::from(y1) - i64::from(y0)).map_err(|_| arithmetic)?,
    ];
    if resolution == 0 {
        before.push(reference_subband_admission(
            0,
            SubbandOrientation::Ll,
            [x0, y0, x1, y1],
            dimensions,
            [true, true],
            depth,
            quantization,
            0,
        )?);
        return Ok(before);
    }
    let low = [ceil(x0, 2), ceil(y0, 2), ceil(x1, 2), ceil(y1, 2)];
    let direction = style
        .decomposition_directions
        .get(usize::from(style.decomposition_levels - resolution))
        .ok_or(invalid)?;
    let orientations: &[SubbandOrientation] = match direction {
        DecompositionDirection::None => &[],
        DecompositionDirection::Horizontal => &[SubbandOrientation::Hl],
        DecompositionDirection::Vertical => &[SubbandOrientation::Lh],
        DecompositionDirection::TwoDimensional => &[
            SubbandOrientation::Hl,
            SubbandOrientation::Lh,
            SubbandOrientation::Hh,
        ],
    };
    let both = *direction == DecompositionDirection::TwoDimensional;
    let phase = [x0 & 1 == 0, y0 & 1 == 0];
    for orientation in orientations {
        let index = u16::try_from(before.len()).map_err(|_| arithmetic)?;
        let band = match orientation {
            SubbandOrientation::Hl => [
                x0 / 2,
                if both { low[1] } else { y0 },
                x1 / 2,
                if both { low[3] } else { y1 },
            ],
            SubbandOrientation::Lh => [
                if both { low[0] } else { x0 },
                y0 / 2,
                if both { low[2] } else { x1 },
                y1 / 2,
            ],
            SubbandOrientation::Hh => [x0 / 2, y0 / 2, x1 / 2, y1 / 2],
            SubbandOrientation::Ll => unreachable!(),
        };
        before.push(reference_subband_admission(
            resolution,
            *orientation,
            band,
            dimensions,
            phase,
            depth,
            quantization,
            index,
        )?);
    }
    Ok(before)
}

fn reference_component_subbands(
    size: &ImageSize,
    style: CodingStyle,
    quantization: &Quantization,
    component: u16,
    tile: Option<u16>,
    roi: u8,
) -> Result<Vec<crate::decode::SubbandGeometry>, DecodeError> {
    let invalid_geometry = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidImageGeometry,
    };
    if component >= size.components {
        return Err(invalid_geometry);
    }
    let info = size
        .component_info
        .get(usize::from(component))
        .ok_or(invalid_geometry)?;
    let bounds = reference_component_coordinate_bounds(size, component, tile)?;
    let expected = reference_truncated_subband_count(style);
    let mut bands = Vec::new();
    for resolution in 0_u16..=u16::from(style.decomposition_levels) {
        bands = reference_subband_resolution(
            style,
            bounds,
            [info.precision, roi],
            quantization,
            u8::try_from(resolution).unwrap(),
            bands,
        )?;
        if resolution == u16::from(u8::MAX) {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::ArithmeticOverflow,
            });
        }
    }
    if bands.len() != usize::from(expected) {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock,
        });
    }
    Ok(bands)
}

#[test]
fn complete_subband_vectors_match_raw_coordinates_direction_order_and_every_field() {
    let mut cases = 0;
    let mut successes = 0;
    for levels in 0..=u8::MAX {
        for pattern in 0..8 {
            let style = raw_resolution_style(levels, pattern);
            assert_eq!(
                style.subband_count(),
                reference_truncated_subband_count(style)
            );
        }
    }
    for extent in [0, 1, 5, 33] {
        for origin in [0, 1, u32::MAX] {
            for sampling in [(0, 1), (1, 0), (1, 1), (2, 3)] {
                for precision in [0, 1, 8, 38, u8::MAX] {
                    let mut size = raw_resolution_size(extent, origin, sampling, u16::MAX, 1);
                    for info in &mut size.component_info {
                        info.precision = precision;
                    }
                    for quantization_style in [
                        QuantizationStyle::None,
                        QuantizationStyle::ScalarDerived,
                        QuantizationStyle::ScalarExpounded,
                    ] {
                        for count in [0, 1, 97, u16::MAX] {
                            let quantization =
                                raw_subband_quantization(quantization_style, count, 4);
                            for (levels, pattern) in
                                [(0, 0), (1, 1), (2, 2), (2, 3), (32, 0), (u8::MAX, 0)]
                            {
                                let style = raw_resolution_style(levels, pattern);
                                for tile in [None, Some(0), Some(u16::MAX)] {
                                    for roi in [0, 1, 73, u8::MAX] {
                                        let expected = reference_component_subbands(
                                            &size,
                                            style,
                                            &quantization,
                                            0,
                                            tile,
                                            roi,
                                        );
                                        assert_eq!(
                                            crate::decode::derive_component_subbands_for(
                                                &size,
                                                style,
                                                &quantization,
                                                0,
                                                tile,
                                                roi
                                            ),
                                            expected,
                                        );
                                        if tile.is_none() && roi == 0 {
                                            assert_eq!(
                                                crate::decode::derive_component_subbands(
                                                    &size,
                                                    style,
                                                    &quantization,
                                                    0
                                                ),
                                                expected,
                                            );
                                        }
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
    }
    assert_eq!(cases, 207_360);
    assert!(
        successes > 1000,
        "{successes} complete subband vectors checked"
    );
}

#[test]
fn subband_vectors_preserve_component_admission_and_raw_prefix_index_boundaries() {
    let quantization = raw_subband_quantization(QuantizationStyle::ScalarDerived, 1, 4);
    let mut cases = 0;
    for components in [0, 1, 64, 65, u16::MAX] {
        for component in [0, 1, 63, 64, u16::MAX] {
            for tile in [None, Some(0), Some(u16::MAX)] {
                for extent in [1, u32::MAX] {
                    for (levels, pattern) in [(0, 0), (u8::MAX, 0)] {
                        for sampling in [(0, 1), (1, 0), (1, 1)] {
                            let size =
                                raw_resolution_size(extent, 1, sampling, u16::MAX, components);
                            let style = raw_resolution_style(levels, pattern);
                            assert_eq!(
                                crate::decode::derive_component_subbands_for(
                                    &size,
                                    style,
                                    &quantization,
                                    component,
                                    tile,
                                    0
                                ),
                                reference_component_subbands(
                                    &size,
                                    style,
                                    &quantization,
                                    component,
                                    tile,
                                    0
                                ),
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 900);
    let dummy = reference_subband_admission(
        0,
        SubbandOrientation::Ll,
        [0, 0, 1, 1],
        [1, 1],
        [true, false],
        [8, 0],
        &quantization,
        u16::MAX,
    )
    .unwrap();
    for length in [0, 1, usize::from(u16::MAX), usize::from(u16::MAX) + 1] {
        let before = vec![dummy; length];
        for pattern in 0..4 {
            let style = raw_resolution_style(1, pattern);
            for resolution in [0, 1] {
                assert_eq!(
                    crate::decode::derive_subband_resolution(
                        style,
                        [1, 3, 5, 9],
                        [8, 0],
                        &quantization,
                        resolution,
                        before.clone()
                    ),
                    reference_subband_resolution(
                        style,
                        [1, 3, 5, 9],
                        [8, 0],
                        &quantization,
                        resolution,
                        before.clone()
                    ),
                );
            }
        }
    }
}

fn raw_subband_quantization(style: QuantizationStyle, count: u16, pattern: usize) -> Quantization {
    Quantization {
        style,
        guard_bits: [0, 1, 7, u8::MAX, 2, 0, 73, 74][pattern],
        step_count: count,
        steps: core::array::from_fn(|index| QuantizationStep {
            exponent: match pattern {
                0 => 0,
                1 => u8::try_from(index % 74).unwrap(),
                2 => u8::MAX,
                3 => 31,
                4 => 7,
                5 => 1,
                6 => 73,
                _ => 74,
            },
            mantissa: u16::try_from(index)
                .unwrap()
                .wrapping_mul(997)
                .wrapping_add(u16::MAX),
        }),
    }
}

fn reference_quantization_lookup(
    value: &Quantization,
    index: u16,
) -> Result<QuantizationStep, DecodeError> {
    if index >= value.step_count || usize::from(index) >= value.steps.len() {
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidQuantization,
        })
    } else {
        Ok(value.steps[usize::from(index)])
    }
}

fn reference_quantization_at_index(
    value: &Quantization,
    resolution: u8,
    index: u16,
) -> Result<QuantizationStep, DecodeError> {
    if value.style != QuantizationStyle::ScalarDerived {
        return reference_quantization_lookup(value, index);
    }
    let base = reference_quantization_lookup(value, 0)?;
    let reduction = if resolution == 0 {
        0
    } else {
        u16::from(resolution) - 1
    };
    let exponent = (i32::from(base.exponent) - i32::from(reduction)).max(0);
    Ok(QuantizationStep {
        exponent: u8::try_from(exponent).unwrap(),
        mantissa: base.mantissa,
    })
}

#[test]
fn quantization_lookup_and_public_subband_index_preserve_raw_words_and_lazy_policy() {
    use SubbandOrientation::{Hh, Hl, Lh, Ll};
    for count in [0, 1, 2, 97, 98, u16::MAX] {
        let value = raw_subband_quantization(QuantizationStyle::ScalarDerived, count, 7);
        for index in 0..=u16::MAX {
            assert_eq!(
                value.step(index),
                reference_quantization_lookup(&value, index)
            );
        }
    }
    let mut cases = 0;
    for style in [
        QuantizationStyle::None,
        QuantizationStyle::ScalarDerived,
        QuantizationStyle::ScalarExpounded,
    ] {
        for count in [0, 1, 2, 97, 98, u16::MAX] {
            for pattern in 0..8 {
                let value = raw_subband_quantization(style, count, pattern);
                assert_eq!(value.style(), style);
                assert_eq!(value.guard_bits(), value.guard_bits);
                for resolution in 0..=u8::MAX {
                    for orientation in [Ll, Hl, Lh, Hh] {
                        let offset = match orientation {
                            Ll | Hl => 0,
                            Lh => 1,
                            Hh => 2,
                        };
                        let index = if resolution == 0 && orientation == Ll {
                            Some(0)
                        } else if resolution != 0 && orientation != Ll {
                            Some(u16::from(resolution) * 3 - 2 + offset)
                        } else {
                            None
                        };
                        let expected = if let Some(index) = index {
                            reference_quantization_at_index(&value, resolution, index)
                                .map(|step| (index, step))
                        } else {
                            Err(DecodeError::MalformedInput {
                                offset: 0,
                                kind: MalformedKind::InvalidCodeBlock,
                            })
                        };
                        assert_eq!(
                            crate::decode::quantization_step_for_subband(
                                &value,
                                resolution,
                                orientation
                            ),
                            expected,
                        );
                        let raw_index = u16::from(resolution).wrapping_mul(997);
                        assert_eq!(
                            crate::decode::quantization_step_at_index(
                                &value, resolution, raw_index
                            ),
                            reference_quantization_at_index(&value, resolution, raw_index),
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 147_456);
}

#[allow(clippy::too_many_arguments)]
fn reference_subband_admission(
    resolution: u8,
    orientation: SubbandOrientation,
    bounds: [u32; 4],
    dimensions: [u32; 2],
    phase: [bool; 2],
    depth: [u8; 2],
    quantization: &Quantization,
    index: u16,
) -> Result<crate::decode::SubbandGeometry, DecodeError> {
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    };
    let gain = match orientation {
        SubbandOrientation::Ll => 0,
        SubbandOrientation::Hl | SubbandOrientation::Lh => 1,
        SubbandOrientation::Hh => 2,
    };
    let dynamic_range = u8::try_from(u16::from(depth[0]) + gain).map_err(|_| arithmetic)?;
    if dynamic_range == 0 {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidQuantization,
        });
    }
    let step = reference_quantization_at_index(quantization, resolution, index)?;
    let raw = u32::from(quantization.guard_bits) + u32::from(step.exponent);
    if raw == 0 {
        return Err(invalid);
    }
    let bitplanes = raw - 1 + u32::from(depth[1]);
    if bitplanes == 0 || bitplanes > u32::from(crate::tier1::MAX_TIER1_BITPLANES) {
        return Err(invalid);
    }
    let width =
        u32::try_from(i64::from(bounds[2]) - i64::from(bounds[0])).map_err(|_| arithmetic)?;
    let height =
        u32::try_from(i64::from(bounds[3]) - i64::from(bounds[1])).map_err(|_| arithmetic)?;
    Ok(crate::decode::SubbandGeometry {
        resolution,
        orientation,
        x0: bounds[0],
        y0: bounds[1],
        width,
        height,
        resolution_width: dimensions[0],
        resolution_height: dimensions[1],
        quantization_index: index,
        quantization_step: step,
        dynamic_range,
        significant_bitplanes: u16::try_from(bitplanes).unwrap(),
        roi_shift: depth[1],
        low_pass_first_x: phase[0],
        low_pass_first_y: phase[1],
    })
}

#[test]
fn subband_admission_matches_every_field_and_raw_error_priority() {
    use SubbandOrientation::{Hh, Hl, Lh, Ll};
    let mut cases = 0;
    let mut successes = 0;
    for style in [
        QuantizationStyle::None,
        QuantizationStyle::ScalarDerived,
        QuantizationStyle::ScalarExpounded,
    ] {
        for count in [0, 1, 2, 97, 98, u16::MAX] {
            for pattern in 0..8 {
                let value = raw_subband_quantization(style, count, pattern);
                for precision in 0..=u8::MAX {
                    for seed in 0_u8..16 {
                        let orientation =
                            [Ll, Hl, Lh, Hh][usize::from(seed.wrapping_add(precision) % 4)];
                        let resolution = [0, 1, 2, 31, 32, u8::MAX][usize::from(seed % 6)];
                        let index = [0, 1, 2, 96, 97, 98, u16::MAX][usize::from(seed % 7)];
                        let bounds = [
                            [0, 0, 3, 5],
                            [1, 1, 1, 1],
                            [u32::MAX, 0, 0, u32::MAX],
                            [0, u32::MAX, u32::MAX, 0],
                        ][usize::from(seed % 4)];
                        let dimensions = [u32::from(seed), u32::MAX];
                        let phase = [seed & 1 != 0, seed & 2 != 0];
                        let depth = [precision, seed * 17];
                        let expected = reference_subband_admission(
                            resolution,
                            orientation,
                            bounds,
                            dimensions,
                            phase,
                            depth,
                            &value,
                            index,
                        );
                        assert_eq!(
                            crate::decode::make_subband_geometry(
                                resolution,
                                orientation,
                                bounds,
                                dimensions,
                                phase,
                                depth,
                                &value,
                                index,
                            ),
                            expected,
                        );
                        successes += usize::from(expected.is_ok());
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 589_824);
    assert!(
        successes > 1000,
        "{successes} complete subband outputs checked"
    );
}

fn raw_resolution_style(levels: u8, pattern: usize) -> CodingStyle {
    use DecompositionDirection::{Horizontal, None, TwoDimensional, Vertical};
    let directions = core::array::from_fn(|index| match pattern {
        0 => None,
        1 => Horizontal,
        2 => Vertical,
        3 => TwoDimensional,
        4 => [Horizontal, Vertical][index % 2],
        5 => [None, TwoDimensional][index % 2],
        6 => [Horizontal, None, Vertical][index % 3],
        _ => {
            if index == 31 {
                TwoDimensional
            } else {
                None
            }
        }
    });
    CodingStyle {
        progression_order: ProgressionOrder::Cprl,
        layers: 0,
        multiple_component_transform: true,
        decomposition_levels: levels,
        decomposition_structure: Some(u8::MAX),
        decomposition_directions: directions,
        code_block_width: 0,
        code_block_height: u16::MAX,
        code_block_style: u8::MAX,
        transform: WaveletTransform::Arbitrary(u8::MAX),
        precincts_defined: false,
        sop_markers: true,
        eph_markers: true,
        precinct_exponents: core::array::from_fn(|index| {
            let index = u8::try_from(index).unwrap();
            (index.wrapping_mul(17), u8::MAX - index.wrapping_mul(7))
        }),
    }
}

fn reference_resolution_scale_step(
    style: CodingStyle,
    stage: u8,
    scales: (u32, u32),
) -> Result<(u32, u32), DecodeError> {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodingStyle,
    };
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    if stage >= style.decomposition_levels {
        return Err(invalid);
    }
    let direction = style
        .decomposition_directions
        .get(usize::from(stage))
        .ok_or(invalid)?;
    let (horizontal, vertical) = match direction {
        DecompositionDirection::None => (u64::from(scales.0), u64::from(scales.1)),
        DecompositionDirection::Horizontal => (u64::from(scales.0) * 2, u64::from(scales.1)),
        DecompositionDirection::Vertical => (u64::from(scales.0), u64::from(scales.1) * 2),
        DecompositionDirection::TwoDimensional => {
            (u64::from(scales.0) * 2, u64::from(scales.1) * 2)
        }
    };
    Ok((
        u32::try_from(horizontal).map_err(|_| arithmetic)?,
        u32::try_from(vertical).map_err(|_| arithmetic)?,
    ))
}

fn reference_component_resolution_counts(
    components: u16,
    styles: &ComponentCodingStyles,
    discard: u8,
) -> Result<(u8, Vec<u8>, Vec<u8>), DecodeError> {
    let mut maximum = 0;
    let mut available = Vec::new();
    let mut selected = Vec::new();
    for component in 0..components {
        if component >= styles.components || usize::from(component) >= styles.styles.len() {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            });
        }
        let count =
            u8::try_from(u16::from(styles.styles[usize::from(component)].decomposition_levels) + 1)
                .map_err(|_| DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::ArithmeticOverflow,
                })?;
        maximum = maximum.max(count);
        available.push(count);
        if discard >= count {
            return Err(DecodeError::InvalidSelection {
                reason: crate::SelectionError::ReductionTooLarge,
            });
        }
        selected.push(count - discard);
    }
    Ok((maximum, available, selected))
}

fn raw_grid_styles(components: u16, pattern: usize) -> ComponentCodingStyles {
    ComponentCodingStyles {
        components,
        styles: core::array::from_fn(|index| {
            let levels = match pattern {
                0 => 0,
                1 => u8::try_from(index % 3).unwrap(),
                2 => u8::try_from(index % 4).unwrap(),
                3 => {
                    if index == 2 {
                        u8::MAX
                    } else {
                        1
                    }
                }
                4 => u8::MAX,
                5 => {
                    if index == 63 {
                        u8::MAX
                    } else {
                        1
                    }
                }
                6 => [0, 2, 31, 254][index % 4],
                _ => 32,
            };
            let mut style = raw_resolution_style(levels, if pattern == 2 { 0 } else { 3 });
            style.code_block_width = 4;
            style.code_block_height = 4;
            style.precinct_exponents = [(0, 0); 33];
            style
        }),
    }
}

#[test]
fn component_resolution_preparation_retains_raw_owners_discard_and_first_errors() {
    let mut cases = 0;
    for count in [0, 1, 2, 63, 64, 65, u16::MAX] {
        for owner in [0, 1, 2, 63, 64, 65, u16::MAX] {
            for discard in [0, 1, 2, 31, 32, 254, u8::MAX] {
                for pattern in 0..8 {
                    let styles = raw_grid_styles(owner, pattern);
                    assert_eq!(
                        crate::decode::prepare_component_resolution_counts(count, &styles, discard),
                        reference_component_resolution_counts(count, &styles, discard),
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 2744);
}

fn reference_subband_count(style: CodingStyle, resolution: u8) -> Result<usize, DecodeError> {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodingStyle,
    };
    if resolution > style.decomposition_levels {
        return Err(invalid);
    }
    let mut count = 1;
    for current in 1..=resolution {
        let stage = style.decomposition_levels - current;
        let direction = style
            .decomposition_directions
            .get(usize::from(stage))
            .ok_or(invalid)?;
        count += match direction {
            DecompositionDirection::None => 0,
            DecompositionDirection::Horizontal | DecompositionDirection::Vertical => 1,
            DecompositionDirection::TwoDimensional => 3,
        };
    }
    Ok(count)
}

fn reference_component_packet_grid(
    size: &ImageSize,
    styles: &ComponentCodingStyles,
    layers: u16,
    limits: &ResourceLimits,
    tile: Option<u16>,
    discard: u8,
) -> Result<crate::packet::PacketGrid, DecodeError> {
    let (maximum, resolutions, selected) =
        reference_component_resolution_counts(size.components, styles, discard)?;
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    usize::try_from(u128::from(size.components) * u128::from(maximum)).map_err(|_| arithmetic)?;
    let mut counts = Vec::new();
    let mut blocks = 0_u64;
    for component in 0..size.components {
        let style = styles.styles[usize::from(component)];
        let available = resolutions[usize::from(component)];
        for resolution in 0..maximum {
            if resolution >= available {
                counts.push(0);
                continue;
            }
            let geometry = reference_resolution_geometry(size, style, component, resolution, tile)?;
            let current = reference_subband_count(style, resolution)?;
            let previous = if resolution == 0 {
                0
            } else {
                reference_subband_count(style, resolution - 1)?
            };
            let subbands = current.checked_sub(previous).ok_or(arithmetic)?;
            if resolution < selected[usize::from(component)] {
                blocks = u64::try_from(u128::from(blocks) + u128::from(geometry.code_blocks))
                    .map_err(|_| arithmetic)?;
                if blocks > limits.maximum_code_blocks() {
                    return Err(DecodeError::LimitExceeded {
                        resource: crate::Resource::CodeBlocks,
                        limit: limits.maximum_code_blocks(),
                        actual: blocks,
                    });
                }
            }
            counts.push(if subbands == 0 {
                0
            } else {
                u32::try_from(geometry.precincts).map_err(|_| arithmetic)?
            });
        }
    }
    crate::packet::packet_grid_new_with_selected_resolutions(
        layers,
        size.components,
        resolutions,
        counts,
        if discard == 0 { None } else { Some(&selected) },
        limits,
    )
}

#[test]
fn component_packet_grid_matches_real_geometry_padding_selection_and_limit_order() {
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(1)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(1).unwrap(),
        ResourceLimits::HARDENED.with_maximum_packets(1).unwrap(),
    ];
    let mut cases = 0;
    let mut successes = 0;
    for extent in [0, 1, 17, 33] {
        for sampling in [(1, 1), (1, 3), (2, 2)] {
            for components in [0, 1, 2, 3, 4] {
                let size = raw_resolution_size(extent, 1, sampling, u16::MAX, components);
                for owner in [0, 1, 2, 4, u16::MAX] {
                    for pattern in 0..4 {
                        let styles = raw_grid_styles(owner, pattern);
                        for layers in [0, 1, 2] {
                            for discard in [0, 1, 2, 3] {
                                for tile in [None, Some(0), Some(1), Some(u16::MAX)] {
                                    for limit in &limits {
                                        let actual =
                                            crate::decode::derive_packet_grid_for_components(
                                                &size, &styles, layers, limit, tile, discard,
                                            );
                                        let expected = reference_component_packet_grid(
                                            &size, &styles, layers, limit, tile, discard,
                                        );
                                        successes += usize::from(expected.is_ok());
                                        assert_eq!(actual, expected);
                                        cases += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 230_400);
    assert!(successes > 100, "{successes} full grid states checked");
}

fn raw_resolution_size(
    extent: u32,
    origin: u32,
    sampling: (u8, u8),
    registration: u16,
    components: u16,
) -> ImageSize {
    ImageSize {
        width: extent,
        height: extent,
        x_origin: origin,
        y_origin: origin.min(1),
        components,
        uniform_bit_depth: None,
        uniform_signed: None,
        tile_width: 17,
        tile_height: 31,
        tile_x_origin: origin.saturating_sub(1),
        tile_y_origin: 0,
        tiles_across: 2,
        tiles_down: 2,
        component_info: [ComponentInfo {
            precision: registration as u8,
            signed: true,
            x_subsampling: sampling.0,
            y_subsampling: sampling.1,
            x_registration: registration,
            y_registration: u16::MAX - registration,
        }; MAX_COMPONENTS],
    }
}

fn reference_component_coordinate_bounds(
    size: &ImageSize,
    component: u16,
    tile_index: Option<u16>,
) -> Result<[u32; 4], DecodeError> {
    if let Some(tile) = tile_index {
        let bounds = reference_tile_component_bounds(size, tile, component)?;
        return Ok([bounds.x0, bounds.y0, bounds.x1, bounds.y1]);
    }
    let geometry = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidImageGeometry,
    };
    if component >= size.components {
        return Err(geometry);
    }
    let info = size
        .component_info
        .get(usize::from(component))
        .ok_or(geometry)?;
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let x1 = u32::try_from(u128::from(size.x_origin) + u128::from(size.width))
        .map_err(|_| arithmetic)?;
    let y1 = u32::try_from(u128::from(size.y_origin) + u128::from(size.height))
        .map_err(|_| arithmetic)?;
    let ceil = |value: u32, divisor: u8| {
        if divisor == 0 {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodeBlock,
            });
        }
        Ok(u32::try_from(u64::from(value).div_ceil(u64::from(divisor))).unwrap())
    };
    Ok([
        ceil(size.x_origin, info.x_subsampling)?,
        ceil(size.y_origin, info.y_subsampling)?,
        ceil(x1, info.x_subsampling)?,
        ceil(y1, info.y_subsampling)?,
    ])
}

fn reference_resolution_geometry(
    size: &ImageSize,
    style: CodingStyle,
    component: u16,
    resolution: u8,
    tile_index: Option<u16>,
) -> Result<crate::decode::ComponentResolutionGeometry, DecodeError> {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    };
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    if resolution > style.decomposition_levels {
        return Err(invalid);
    }
    let bounds = reference_component_coordinate_bounds(size, component, tile_index)?;
    let scale = (0..style.decomposition_levels - resolution)
        .try_fold((1, 1), |before, stage| {
            reference_resolution_scale_step(style, stage, before)
        })?;
    let ceil = |value: u32, divisor: u32| {
        u32::try_from(u128::from(value).div_ceil(u128::from(divisor))).unwrap()
    };
    let x0 = ceil(bounds[0], scale.0);
    let y0 = ceil(bounds[1], scale.1);
    let x1 = ceil(bounds[2], scale.0);
    let y1 = ceil(bounds[3], scale.1);
    let width = x1.checked_sub(x0).ok_or(arithmetic)?;
    let height = y1.checked_sub(y0).ok_or(arithmetic)?;
    if style.code_block_width == 0 || style.code_block_height == 0 {
        return Err(invalid);
    }
    let cells = |start: u32, end: u32, step: u32| {
        let right = u64::from(end).div_ceil(u64::from(step));
        let left = u64::from(start) / u64::from(step);
        u32::try_from(right.checked_sub(left).ok_or(arithmetic)?).map_err(|_| arithmetic)
    };
    let code_blocks_across = cells(x0, x1, u32::from(style.code_block_width))?;
    let code_blocks_down = cells(y0, y1, u32::from(style.code_block_height))?;
    let code_blocks = u64::try_from(u128::from(code_blocks_across) * u128::from(code_blocks_down))
        .map_err(|_| arithmetic)?;
    let precinct = style
        .precinct_exponents
        .get(usize::from(resolution))
        .ok_or(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodingStyle,
        })?;
    if precinct.0 > 31 || precinct.1 > 31 {
        return Err(invalid);
    }
    let precincts_across = cells(x0, x1, 1_u32 << precinct.0)?;
    let precincts_down = cells(y0, y1, 1_u32 << precinct.1)?;
    let precincts = u64::try_from(u128::from(precincts_across) * u128::from(precincts_down))
        .map_err(|_| arithmetic)?;
    Ok(crate::decode::ComponentResolutionGeometry {
        component,
        resolution,
        width,
        height,
        subbands: if resolution == 0 { 1 } else { 3 },
        code_blocks_across,
        code_blocks_down,
        code_blocks,
        precincts_across,
        precincts_down,
        precincts,
    })
}

#[test]
fn resolution_geometry_matches_complete_raw_whole_and_registered_tile_outputs() {
    let mut cases = 0;
    let mut successful = 0;
    for extent in [0, 1, 33, 1025, u32::MAX] {
        for origin in [0, 1, u32::MAX] {
            for sampling in [(1, 1), (1, 3), (2, 255), (255, 2)] {
                for registration in [0, 1, u16::MAX] {
                    let size = raw_resolution_size(extent, origin, sampling, registration, 1);
                    for tile in [None, Some(0), Some(1)] {
                        assert_eq!(
                            crate::decode::component_coordinate_bounds(&size, 0, tile),
                            reference_component_coordinate_bounds(&size, 0, tile),
                        );
                        for (levels, resolution, pattern) in [
                            (0, 0, 0),
                            (1, 0, 1),
                            (1, 1, 2),
                            (5, 2, 3),
                            (31, 0, 1),
                            (32, 0, 3),
                            (33, 0, 0),
                            (255, 255, 7),
                        ] {
                            for (block_x, block_y) in
                                [(0, 1), (1, 0), (1, 1), (3, 7), (u16::MAX, u16::MAX)]
                            {
                                for precinct in
                                    [(0, 0), (1, 31), (31, 1), (32, 0), (0, 32), (255, 255)]
                                {
                                    let mut style = raw_resolution_style(levels, pattern);
                                    style.code_block_width = block_x;
                                    style.code_block_height = block_y;
                                    if let Some(slot) =
                                        style.precinct_exponents.get_mut(usize::from(resolution))
                                    {
                                        *slot = precinct;
                                    }
                                    let expected = reference_resolution_geometry(
                                        &size, style, 0, resolution, tile,
                                    );
                                    assert_eq!(
                                        crate::decode::derive_component_resolution_geometry_for(
                                            &size, style, 0, resolution, tile,
                                        ),
                                        expected,
                                    );
                                    if tile.is_none() {
                                        assert_eq!(
                                            crate::decode::derive_component_resolution_geometry(
                                                &size, style, 0, resolution
                                            ),
                                            expected,
                                        );
                                    }
                                    successful += usize::from(expected.is_ok());
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 129_600);
    assert!(
        successful > 1000,
        "{successful} successful whole-owner outputs"
    );
}

#[test]
fn resolution_geometry_preserves_raw_admission_and_sampling_error_priority() {
    let mut cases = 0;
    for extent in [0, 1, 33, 1025, u32::MAX] {
        for origin in [0, 1, u32::MAX] {
            for sampling in [(0, 0), (0, 1), (1, 0), (1, 1), (2, 255), (255, 2)] {
                for count in [0, 1, 64, 65, u16::MAX] {
                    let size = raw_resolution_size(extent, origin, sampling, u16::MAX, count);
                    for component in [0, 1, 63, 64, u16::MAX] {
                        for tile in [None, Some(0), Some(1), Some(u16::MAX)] {
                            assert_eq!(
                                crate::decode::component_coordinate_bounds(&size, component, tile),
                                reference_component_coordinate_bounds(&size, component, tile),
                            );
                            for (levels, resolution, pattern) in
                                [(0, 255, 0), (255, 255, 7), (32, 0, 1)]
                            {
                                let mut style = raw_resolution_style(levels, pattern);
                                style.code_block_width = 3;
                                style.code_block_height = 7;
                                assert_eq!(
                                    crate::decode::derive_component_resolution_geometry_for(
                                        &size, style, component, resolution, tile,
                                    ),
                                    reference_resolution_geometry(
                                        &size, style, component, resolution, tile
                                    ),
                                );
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 27_000);
}

#[test]
fn resolution_styles_preserve_all_raw_level_resolution_and_lazy_precinct_cases() {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodingStyle,
    };
    let mut cases = 0;
    for pattern in 0..8 {
        for levels in 0..=u8::MAX {
            let style = raw_resolution_style(levels, pattern);
            for resolution in 0..=u8::MAX {
                let expected = if resolution > levels {
                    Err(invalid)
                } else {
                    (0..levels - resolution).try_fold((1, 1), |scales, stage| {
                        reference_resolution_scale_step(style, stage, scales)
                    })
                };
                assert_eq!(style.resolution_downsampling(resolution), expected);
                let expected_precinct = if resolution > levels {
                    Err(invalid)
                } else {
                    style
                        .precinct_exponents
                        .get(usize::from(resolution))
                        .copied()
                        .ok_or(invalid)
                };
                assert_eq!(style.precinct_exponents(resolution), expected_precinct);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 524_288);
    for horizontal in 0..=u8::MAX {
        for vertical in 0..=u8::MAX {
            let mut style = raw_resolution_style(0, 0);
            style.precinct_exponents[0] = (horizontal, vertical);
            assert_eq!(style.precinct_exponents(0), Ok((horizontal, vertical)));
        }
    }
}

#[test]
fn resolution_scale_step_preserves_raw_scales_selector_priority_and_overflow() {
    let scales = [0, 1, 2, (1_u32 << 31) - 1, 1_u32 << 31, u32::MAX];
    let mut cases = 0;
    for pattern in 0..8 {
        for levels in [0, 1, 31, 32, 33, u8::MAX] {
            let style = raw_resolution_style(levels, pattern);
            for stage in 0..=u8::MAX {
                for horizontal in scales {
                    for vertical in scales {
                        assert_eq!(
                            style.resolution_downsampling_step(stage, (horizontal, vertical)),
                            reference_resolution_scale_step(style, stage, (horizontal, vertical)),
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 442_368);
}

fn independent_execution_header(
    style: CodingStyle,
    extensions: &Part2Extensions,
) -> Result<(), DecodeError> {
    match style.decomposition_structure {
        Some(index)
            if !extensions
                .decomposition_structures
                .iter()
                .any(|value| value.index == index)
                && !extensions
                    .arbitrary_decompositions
                    .iter()
                    .any(|value| value.index == index) =>
        {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::MissingRequiredStructure,
            });
        }
        _ => {}
    }
    match style.transform {
        WaveletTransform::Arbitrary(index)
            if !extensions
                .arbitrary_kernels
                .iter()
                .any(|value| value.index == index) =>
        {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::MissingRequiredStructure,
            });
        }
        _ => {}
    }
    Ok(())
}

#[test]
fn actual_layout_execution_admission_preserves_raw_count_and_global_error_order() {
    let headers = baseline_headers();
    let bytes = codestream_with_headers(1, &headers, &[], &[]);
    let limits = ResourceLimits::default();
    let mut layout = parse_layout(&bytes, &limits).unwrap();
    let baseline = layout.info.coding_style;
    let template = layout.tile_parts[0].clone();
    layout.tile_parts = vec![template.clone(), template];
    let fixture = |mode| {
        let mut style = baseline;
        style.layers = 0;
        style.decomposition_levels = u8::MAX;
        style.decomposition_structure = None;
        style.transform = WaveletTransform::Reversible5x3;
        let mut extensions = Part2Extensions {
            metadata_bytes: u64::MAX,
            ..Part2Extensions::default()
        };
        match mode {
            1 => style.decomposition_structure = Some(7),
            2 => style.transform = WaveletTransform::Arbitrary(8),
            3 => {
                style.decomposition_structure = Some(7);
                extensions
                    .decomposition_structures
                    .push(DecompositionStructure {
                        index: 7,
                        directions: vec![],
                    });
            }
            4 => {
                style.decomposition_structure = Some(7);
                extensions
                    .arbitrary_decompositions
                    .push(ArbitraryDecomposition {
                        index: 7,
                        sublevel_depths: vec![u8::MAX],
                        subband_splits: vec![],
                    });
            }
            _ => {}
        }
        (style, extensions)
    };
    let main_depths = vec![
        ComponentBitDepth {
            precision: 0,
            signed: false,
        },
        ComponentBitDepth {
            precision: u8::MAX,
            signed: true,
        },
    ];
    let mut cases = 0;
    for count in [0, 1, 2, 64, 65, u16::MAX] {
        for main_count in [0, 1, 64, 65] {
            for tile_count in [0, 1, 64, 65] {
                for main_mode in [0, 1, 2] {
                    for first_mode in [0, 1, 3] {
                        for late_mode in [0, 2, 4] {
                            for depth_mode in 0..5 {
                                let (main_style, mut main) = fixture(main_mode);
                                main.component_bit_depths = main_depths.clone();
                                layout.info.image_size.components = count;
                                layout.info.component_coding_styles = ComponentCodingStyles {
                                    components: main_count,
                                    styles: [main_style; MAX_COMPONENTS],
                                };
                                layout.info.part2_extensions = main;
                                let (first_style, mut first) = fixture(first_mode);
                                first.component_bit_depths = match depth_mode {
                                    0 => vec![],
                                    1 => main_depths.clone(),
                                    2 => vec![
                                        ComponentBitDepth {
                                            precision: 1,
                                            signed: false,
                                        },
                                        main_depths[1],
                                    ],
                                    3 => vec![
                                        ComponentBitDepth {
                                            precision: 0,
                                            signed: true,
                                        },
                                        main_depths[1],
                                    ],
                                    _ => vec![main_depths[0]],
                                };
                                layout.tile_parts[0].component_coding_styles =
                                    ComponentCodingStyles {
                                        components: tile_count,
                                        styles: [first_style; MAX_COMPONENTS],
                                    };
                                layout.tile_parts[0].part2_extensions = first;
                                let (late_style, late) = fixture(late_mode);
                                layout.tile_parts[1].component_coding_styles =
                                    ComponentCodingStyles {
                                        components: tile_count,
                                        styles: [late_style; MAX_COMPONENTS],
                                    };
                                layout.tile_parts[1].part2_extensions = late;
                                let expected = (|| {
                                    for component in 0..count {
                                        independent_execution_header(
                                            layout.info.component_coding_styles.style(component)?,
                                            &layout.info.part2_extensions,
                                        )?;
                                    }
                                    for part in &layout.tile_parts {
                                        for component in 0..count {
                                            independent_execution_header(
                                                part.component_coding_styles.style(component)?,
                                                &part.part2_extensions,
                                            )?;
                                        }
                                        if !part.part2_extensions.component_bit_depths.is_empty()
                                            && part.part2_extensions.component_bit_depths
                                                != layout.info.part2_extensions.component_bit_depths
                                        {
                                            return Err(DecodeError::MalformedInput {
                                                offset: 0,
                                                kind: MalformedKind::InvalidMarkerOrder,
                                            });
                                        }
                                    }
                                    Ok(())
                                })();
                                assert_eq!(
                                    crate::decode::validate_part2_execution(&layout),
                                    expected
                                );
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 12960);
}

#[test]
fn actual_execution_style_admission_matches_raw_registry_membership_and_lazy_fields() {
    let headers = baseline_headers();
    let bytes = codestream_with_headers(1, &headers, &[], &[]);
    let limits = ResourceLimits::default();
    let baseline = parse_layout(&bytes, &limits).unwrap().info.coding_style;
    let mut cases = 0;
    for stored in 0..=u8::MAX {
        let ads_index = stored.wrapping_add(2);
        let atk_index = stored.wrapping_add(3);
        let extensions = Part2Extensions {
            decomposition_structures: vec![
                DecompositionStructure {
                    index: stored,
                    directions: vec![baseline.decomposition_directions[0]; 33],
                },
                DecompositionStructure {
                    index: stored.wrapping_add(1),
                    directions: vec![],
                },
                DecompositionStructure {
                    index: stored,
                    directions: vec![],
                },
            ],
            arbitrary_decompositions: vec![
                ArbitraryDecomposition {
                    index: ads_index,
                    sublevel_depths: vec![u8::MAX],
                    subband_splits: vec![],
                },
                ArbitraryDecomposition {
                    index: ads_index,
                    sublevel_depths: vec![],
                    subband_splits: vec![],
                },
            ],
            arbitrary_kernels: vec![ArbitraryKernel {
                index: atk_index,
                reversible: false,
                descriptor: u16::MAX,
                coefficient_type: u8::MAX,
                whole_sample_filter: false,
                initial_odd: true,
                whole_sample_extension: false,
                scaling: None,
                steps: vec![],
            }],
            metadata_bytes: u64::MAX,
            ..Part2Extensions::default()
        };
        extensions.validate_executable().unwrap();
        for index in 0..=u8::MAX {
            let dsc_position = if index == stored {
                Some(0)
            } else if index == stored.wrapping_add(1) {
                Some(1)
            } else {
                None
            };
            let dsc = extensions.decomposition_structure(index);
            assert_eq!(dsc.is_some(), dsc_position.is_some());
            if let Some(position) = dsc_position {
                assert!(std::ptr::eq(
                    dsc.unwrap(),
                    &extensions.decomposition_structures[position]
                ));
            }
            let ads = extensions.arbitrary_decomposition(index);
            assert_eq!(ads.is_some(), index == ads_index);
            if index == ads_index {
                assert!(std::ptr::eq(
                    ads.unwrap(),
                    &extensions.arbitrary_decompositions[0]
                ));
            }
            for transform in [
                WaveletTransform::Reversible5x3,
                WaveletTransform::Irreversible9x7,
                WaveletTransform::Arbitrary(atk_index),
                WaveletTransform::Arbitrary(atk_index.wrapping_add(1)),
            ] {
                let mut style = baseline;
                style.decomposition_structure = Some(index);
                style.transform = transform;
                style.layers = 0;
                style.decomposition_levels = u8::MAX;
                style.code_block_width = 0;
                style.code_block_height = u16::MAX;
                style.code_block_style = u8::MAX;
                let decomposition_exists = dsc_position.is_some() || index == ads_index;
                let kernel_exists = !matches!(transform, WaveletTransform::Arbitrary(requested) if requested != atk_index);
                let expected = if decomposition_exists && kernel_exists {
                    Ok(())
                } else {
                    Err(DecodeError::MalformedInput {
                        offset: 0,
                        kind: MalformedKind::MissingRequiredStructure,
                    })
                };
                assert_eq!(
                    crate::decode::validate_part2_coding_style(style, &extensions),
                    expected
                );
                cases += 1;
            }
        }
        let mut style = baseline;
        style.decomposition_structure = None;
        style.transform = WaveletTransform::Arbitrary(atk_index);
        crate::decode::validate_part2_coding_style(style, &extensions).unwrap();
    }
    assert_eq!(cases, 262144);
}

#[test]
fn actual_component_depth_comparison_preserves_raw_order_precision_and_sign() {
    let mut cases = 0;
    for precision in 0..=u8::MAX {
        for signed in [false, true] {
            let values = vec![
                ComponentBitDepth { precision, signed },
                ComponentBitDepth {
                    precision: 0,
                    signed: !signed,
                },
                ComponentBitDepth { precision, signed },
            ];
            let left = Part2Extensions {
                component_bit_depths: values.clone(),
                metadata_bytes: u64::MAX,
                ..Part2Extensions::default()
            };
            for variant in 0..5 {
                let mut other_values = values.clone();
                match variant {
                    1 => other_values[2].precision = precision.wrapping_add(1),
                    2 => other_values[2].signed = !signed,
                    3 => {
                        other_values.pop();
                    }
                    4 => other_values.push(ComponentBitDepth { precision, signed }),
                    _ => {}
                }
                let expected = values == other_values;
                let right = Part2Extensions {
                    component_bit_depths: other_values,
                    ..Part2Extensions::default()
                };
                assert_eq!(left.component_bit_depths_equal(&right), expected);
                assert_eq!(right.component_bit_depths_equal(&left), expected);
                assert_eq!(left.component_bit_depths(), &values);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 2560);
    let empty = Part2Extensions::default();
    assert!(empty.component_bit_depths_equal(&empty));
}

#[test]
fn registered_component_ceiling_matches_wide_arithmetic_and_all_registration_words() {
    let oracle = |value: u32, divisor: u32, registration: u16| {
        if divisor == 0 {
            return Err(selection_geometry_invalid());
        }
        let numerator = (u128::from(value) * 65_536).saturating_sub(u128::from(registration));
        let denominator = u128::from(divisor) * 65_536;
        Ok(u32::try_from(numerator.div_ceil(denominator)).unwrap())
    };
    for value in [0, 1, 2, 255, 65_535, 65_536, u32::MAX - 1, u32::MAX] {
        for divisor in [0, 1, 2, 3, 255, 65_536, u32::MAX - 1, u32::MAX] {
            for registration in [0, 1, 32_767, 32_768, 65_534, u16::MAX] {
                let expected = oracle(value, divisor, registration);
                assert_eq!(registered_ceil_div(value, divisor, registration), expected,);
                assert_eq!(
                    crate::decode::registered_ceil_div_u32(value, divisor, registration),
                    if divisor == 0 {
                        Err(DecodeError::MalformedInput {
                            offset: 0,
                            kind: MalformedKind::InvalidCodeBlock,
                        })
                    } else {
                        expected
                    },
                );
            }
        }
    }
    for registration in 0..=u16::MAX {
        for value in [0, 1, u32::MAX] {
            for divisor in [0, 1, 2, 255, u32::MAX] {
                let expected = oracle(value, divisor, registration);
                assert_eq!(registered_ceil_div(value, divisor, registration), expected,);
                assert_eq!(
                    crate::decode::registered_ceil_div_u32(value, divisor, registration),
                    if divisor == 0 {
                        Err(DecodeError::MalformedInput {
                            offset: 0,
                            kind: MalformedKind::InvalidCodeBlock,
                        })
                    } else {
                        expected
                    },
                );
            }
        }
    }
}

fn reference_tile_component_bounds(
    size: &ImageSize,
    tile_index: u16,
    component: u16,
) -> Result<TileComponentBounds, DecodeError> {
    let invalid = || DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidImageGeometry,
    };
    let checked = |value: u128| {
        u32::try_from(value).map_err(|_| DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        })
    };
    if u64::from(tile_index) >= u64::from(size.tiles_across) * u64::from(size.tiles_down)
        || size.tiles_across == 0
    {
        return Err(invalid());
    }
    let nx = checked(
        u128::from(size.tile_x_origin)
            + u128::from(u32::from(tile_index) % size.tiles_across) * u128::from(size.tile_width),
    )?;
    let ny = checked(
        u128::from(size.tile_y_origin)
            + u128::from(u32::from(tile_index) / size.tiles_across) * u128::from(size.tile_height),
    )?;
    let image_x1 = checked(u128::from(size.x_origin) + u128::from(size.width))?;
    let image_y1 = checked(u128::from(size.y_origin) + u128::from(size.height))?;
    let tx0 = nx.max(size.x_origin);
    let ty0 = ny.max(size.y_origin);
    let tx1 = checked(u128::from(nx) + u128::from(size.tile_width))?.min(image_x1);
    let ty1 = checked(u128::from(ny) + u128::from(size.tile_height))?.min(image_y1);
    if tx0 >= tx1 || ty0 >= ty1 {
        return Err(invalid());
    }
    if component >= size.components {
        return Err(invalid());
    }
    let info = size
        .component_info
        .get(usize::from(component))
        .ok_or_else(invalid)?;
    let ceil = |value: u32, divisor: u8, registration: u16| {
        if divisor == 0 {
            return Err(invalid());
        }
        let numerator = (u128::from(value) * 65_536).saturating_sub(u128::from(registration));
        Ok(u32::try_from(numerator.div_ceil(u128::from(divisor) * 65_536)).unwrap())
    };
    let image_x0 = ceil(size.x_origin, info.x_subsampling, info.x_registration)?;
    let image_y0 = ceil(size.y_origin, info.y_subsampling, info.y_registration)?;
    let x0 = ceil(tx0, info.x_subsampling, info.x_registration)?;
    let y0 = ceil(ty0, info.y_subsampling, info.y_registration)?;
    let x1 = ceil(tx1, info.x_subsampling, info.x_registration)?;
    let y1 = ceil(ty1, info.y_subsampling, info.y_registration)?;
    if x0 >= x1 || y0 >= y1 {
        return Err(invalid());
    }
    Ok(TileComponentBounds {
        tile_index,
        component,
        x0,
        y0,
        x1,
        y1,
        image_x: x0.checked_sub(image_x0).ok_or_else(invalid)?,
        image_y: y0.checked_sub(image_y0).ok_or_else(invalid)?,
    })
}

#[test]
fn tile_component_bounds_match_raw_geometry_and_ordered_descriptor_admission() {
    let mut cases = 0;
    for extent in [0, 1, 3, 31, u32::MAX] {
        for span in [0, 1, 2, 31, u32::MAX] {
            for origin in [0, 1, u32::MAX] {
                for tile_index in [0, 1, 5, 6, u16::MAX] {
                    for components in [0, 1, 64, 65, u16::MAX] {
                        for component in [0, 1, 63, 64, u16::MAX] {
                            for (x_subsampling, y_subsampling) in
                                [(0, 0), (0, 1), (1, 0), (1, 1), (2, 255), (255, 2)]
                            {
                                for registration in [0, 1, u16::MAX] {
                                    let size = ImageSize {
                                        width: extent,
                                        height: extent,
                                        x_origin: origin,
                                        y_origin: origin.min(1),
                                        components,
                                        uniform_bit_depth: None,
                                        uniform_signed: None,
                                        tile_width: span,
                                        tile_height: span.wrapping_add(1),
                                        tile_x_origin: origin.saturating_sub(1),
                                        tile_y_origin: 0,
                                        tiles_across: if span == u32::MAX { span } else { 3 },
                                        tiles_down: span,
                                        component_info: [ComponentInfo {
                                            precision: registration as u8,
                                            signed: true,
                                            x_subsampling,
                                            y_subsampling,
                                            x_registration: registration,
                                            y_registration: u16::MAX - registration,
                                        };
                                            MAX_COMPONENTS],
                                    };
                                    assert_eq!(
                                        size.tile_component_bounds(tile_index, component),
                                        reference_tile_component_bounds(
                                            &size, tile_index, component
                                        ),
                                        "extent={extent} span={span} origin={origin} tile={tile_index} count={components} component={component} sampling=({x_subsampling},{y_subsampling}) registration={registration}",
                                    );
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 168_750);
}

#[test]
fn actual_kernel_registry_retains_first_duplicates_and_every_raw_index() {
    let kernel = |index, reversible| ArbitraryKernel {
        index,
        reversible,
        descriptor: u16::MAX,
        coefficient_type: u8::MAX,
        whole_sample_filter: false,
        initial_odd: true,
        whole_sample_extension: false,
        scaling: None,
        steps: Vec::new(),
    };
    for first in 0..=u8::MAX {
        let extensions = Part2Extensions {
            arbitrary_kernels: vec![
                kernel(first, true),
                kernel(first.wrapping_add(1), false),
                kernel(first, false),
            ],
            ..Part2Extensions::default()
        };
        for index in 0..=u8::MAX {
            let expected = if index == first {
                Some(0)
            } else if index == first.wrapping_add(1) {
                Some(1)
            } else {
                None
            };
            let actual = extensions.arbitrary_kernel(index);
            assert_eq!(actual.is_some(), expected.is_some());
            if let Some(position) = expected {
                assert!(std::ptr::eq(
                    actual.unwrap(),
                    &extensions.arbitrary_kernels[position]
                ));
            }
        }
    }
}

fn input_error_literal(offset: usize, kind: MalformedKind) -> DecodeError {
    DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    }
}

fn packet_length_wide_window(
    encoded: &[u8],
    start: usize,
    end: usize,
) -> Result<(u32, usize), DecodeError> {
    let invalid = input_error_literal(start, MalformedKind::InvalidPacketLength);
    if start >= end || end > encoded.len() {
        return Err(invalid);
    }
    let window = &encoded[start..end];
    let Some(last) = window.iter().position(|byte| byte & 0x80 == 0) else {
        return Err(invalid);
    };
    if last >= 5 {
        return Err(invalid);
    }
    let wide: u128 = window[..=last]
        .iter()
        .enumerate()
        .map(|(index, byte)| u128::from(byte & 0x7f) << (7 * (last - index)))
        .sum();
    if wide == 0 || wide > u128::from(u32::MAX) {
        Err(invalid)
    } else {
        Ok((wide as u32, start + last + 1))
    }
}

#[test]
fn packet_lengths_exhaustive_two_byte_windows_and_every_raw_iterator_field() {
    for word in 0_u16..=u16::MAX {
        let bytes = word.to_be_bytes();
        for position in [0, 1, 2, 3, usize::MAX] {
            for segment_end in [0, 1, 2, 3, usize::MAX] {
                assert_eq!(
                    decode_packet_length(&bytes, position, segment_end),
                    packet_length_wide_window(&bytes, position, segment_end)
                );
                for source in [
                    PacketLengthSource::None,
                    PacketLengthSource::Plm(&bytes),
                    PacketLengthSource::Plt(&bytes),
                ] {
                    let lengths = PacketLengths {
                        source,
                        packet_count: u64::MAX,
                        encoded_bytes: u64::MAX,
                    };
                    assert_eq!(lengths.is_present(), source != PacketLengthSource::None);
                    assert_eq!(lengths.packet_count(), u64::MAX);
                    assert_eq!(lengths.encoded_bytes(), u64::MAX);
                    let fresh = lengths.iter();
                    assert_eq!(
                        (fresh.source, fresh.position, fresh.segment_end),
                        (source, 0, 0)
                    );
                    let mut actual = PacketLengthIter {
                        source,
                        position,
                        segment_end,
                    };
                    let expected = match source {
                        PacketLengthSource::None => Ok(None),
                        PacketLengthSource::Plm(_) if position == bytes.len() => Ok(None),
                        PacketLengthSource::Plm(_) => {
                            packet_length_wide_window(&bytes, position, bytes.len()).map(Some)
                        }
                        PacketLengthSource::Plt(_) if position < segment_end => {
                            packet_length_wide_window(&bytes, position, segment_end).map(Some)
                        }
                        PacketLengthSource::Plt(_) if position == bytes.len() => Ok(None),
                        PacketLengthSource::Plt(_) => Err(input_error_literal(
                            position,
                            MalformedKind::InvalidPacketLength,
                        )),
                    };
                    let (expected_result, expected_position) = match expected {
                        Ok(Some((value, next))) => (Ok(Some(value)), next),
                        Ok(None) => (Ok(None), position),
                        Err(error) => (Err(error), position),
                    };
                    assert_eq!(actual.next_length(), expected_result);
                    assert_eq!(
                        (actual.source, actual.position, actual.segment_end),
                        (source, expected_position, segment_end)
                    );
                }
            }
        }
    }
}

#[test]
fn packet_length_full_width_noncanonical_and_unterminated_groups_match_wide_words() {
    let inputs: &[&[u8]] = &[
        &[],
        &[0],
        &[0x80],
        &[0x81, 0],
        &[0x80, 0x80, 0x80, 0x80, 1],
        &[0x8f, 0xff, 0xff, 0xff, 0x7f],
        &[0x90, 0x80, 0x80, 0x80, 0],
        &[0xff, 0xff, 0xff, 0xff, 0xff],
        &[0x80, 0x80, 0x80, 0x80, 0x80, 1],
    ];
    for encoded in inputs {
        for start in (0..=encoded.len() + 1).chain([usize::MAX]) {
            for end in (0..=encoded.len() + 1).chain([usize::MAX]) {
                assert_eq!(
                    decode_packet_length(encoded, start, end),
                    packet_length_wide_window(encoded, start, end)
                );
            }
        }
    }
    assert_eq!(decode_packet_length(inputs[5], 0, 5), Ok((u32::MAX, 5)));
    assert_eq!(decode_packet_length(inputs[4], 0, 5), Ok((1, 5)));
}

#[test]
fn plt_real_marker_traversal_keeps_late_cursor_commits_and_repeated_error_states() {
    type Fixture<'a> = (&'a [u8], Result<Option<u32>, DecodeError>, usize, usize);
    let fixtures: &[Fixture<'_>] = &[
        (&[], Ok(None), 0, 0),
        (&[0xff, 0x55, 0, 2], Ok(None), 4, 0),
        (
            &[0xff, 0x58, 0, 2],
            Err(input_error_literal(4, MalformedKind::InvalidMarkerLength)),
            4,
            0,
        ),
        (&[0xff, 0x58, 0, 3, 9], Ok(None), 5, 5),
        (
            &[0xff, 0x58, 0, 4, 9, 0],
            Err(input_error_literal(5, MalformedKind::InvalidPacketLength)),
            5,
            6,
        ),
        (
            &[0xff, 0x55, 0, 2, 0xff, 0x58, 0, 2],
            Err(input_error_literal(8, MalformedKind::InvalidMarkerLength)),
            8,
            0,
        ),
        (
            &[0xff, 0x58, 0, 7],
            Err(input_error_literal(0, MalformedKind::InvalidMarkerLength)),
            0,
            0,
        ),
    ];
    for (header, expected, position, end) in fixtures {
        let source = PacketLengthSource::Plt(header);
        let mut actual = PacketLengthIter {
            source,
            position: 0,
            segment_end: 0,
        };
        assert_eq!(actual.next_length(), *expected);
        assert_eq!(
            (actual.source, actual.position, actual.segment_end),
            (source, *position, *end)
        );
    }
    let header = [
        0xff, 0x58, 0, 5, 0, 0x81, 0, 0xff, 0x55, 0, 2, 0xff, 0x58, 0, 4, 0, 5,
    ];
    let mut actual = PacketLengthIter {
        source: PacketLengthSource::Plt(&header),
        position: 0,
        segment_end: 0,
    };
    for (result, position, end) in [
        (Ok(Some(128)), 7, 7),
        (Ok(Some(5)), 17, 17),
        (Ok(None), 17, 17),
    ] {
        assert_eq!(actual.next_length(), result);
        assert_eq!((actual.position, actual.segment_end), (position, end));
    }
    let header = [0xff, 0x58, 0, 4, 0, 0];
    let mut actual = PacketLengthIter {
        source: PacketLengthSource::Plt(&header),
        position: 0,
        segment_end: 0,
    };
    for _ in 0..2 {
        assert_eq!(
            actual.next_length(),
            Err(input_error_literal(5, MalformedKind::InvalidPacketLength))
        );
        assert_eq!((actual.position, actual.segment_end), (5, 6));
    }
}

#[test]
fn packed_reassembly_literal_fragments_ranges_and_late_errors_have_exact_bytes() {
    type Fixture<'a> = (&'a [u8], &'a [u8], Option<(usize, MalformedKind)>);
    let fixtures: &[Fixture<'_>] = &[
        (&[], &[], None),
        (
            &[0xff],
            &[],
            Some((0, MalformedKind::InvalidPackedPacketHeader)),
        ),
        (
            &[0xff, 0x60, 0, 1],
            &[],
            Some((0, MalformedKind::InvalidMarkerLength)),
        ),
        (
            &[0xff, 0x60, 0, 2],
            &[],
            Some((0, MalformedKind::InvalidMarkerLength)),
        ),
        (&[0xff, 0x60, 0, 3, 0], &[], None),
        (
            &[
                0xff, 0x60, 0, 5, 0, 10, 11, 0xff, 0x55, 0, 2, 0xff, 0x60, 0, 4, 9, 12,
            ],
            &[10, 11, 12],
            None,
        ),
        (
            &[0xff, 0x60, 0, 4, 0, 10, 0xff],
            &[10],
            Some((6, MalformedKind::InvalidPackedPacketHeader)),
        ),
        (
            &[0xff, 0x60, 0, 4, 0],
            &[],
            Some((0, MalformedKind::InvalidMarkerLength)),
        ),
    ];
    for (header, flat, parse_error) in fixtures {
        for logical_start in [0, 1, 2, 3, 4, usize::MAX] {
            for length in 0..=5 {
                for fragments in [0, 1, u16::MAX] {
                    for cap in [
                        1,
                        2,
                        5,
                        ResourceLimits::default().maximum_packet_header_bytes(),
                    ] {
                        let limits = ResourceLimits::default()
                            .with_maximum_packet_header_bytes(cap)
                            .unwrap();
                        let packed = PackedPacketHeaders {
                            source: PackedPacketHeaderSource::MarkerSegments {
                                header,
                                marker: 0xff60,
                                logical_start,
                            },
                            length,
                            fragments,
                        };
                        let expected = if length as u64 > cap {
                            Err(DecodeError::LimitExceeded {
                                resource: Resource::PacketHeaderBytes,
                                limit: cap,
                                actual: length as u64,
                            })
                        } else if logical_start.checked_add(length).is_none() {
                            Err(input_error_literal(0, MalformedKind::ArithmeticOverflow))
                        } else if let Some((offset, kind)) = parse_error {
                            Err(input_error_literal(*offset, *kind))
                        } else if length == 0 {
                            Ok(Vec::new())
                        } else if let Some(bytes) = flat.get(logical_start..logical_start + length)
                        {
                            Ok(bytes.to_vec())
                        } else {
                            Err(input_error_literal(
                                flat.len(),
                                MalformedKind::InvalidPackedPacketHeader,
                            ))
                        };
                        assert!(packed.is_present());
                        assert_eq!(
                            (packed.len(), packed.is_empty(), packed.fragment_count()),
                            (length, length == 0, fragments)
                        );
                        assert_eq!(packed.reassemble(&limits), expected);
                    }
                }
            }
        }
    }
}

#[test]
fn packed_raw_source_marker_and_absent_metadata_do_not_invent_shape_invariants() {
    let header = [0xff, 0x60, 0, 2];
    let limits = ResourceLimits::default();
    for marker in 0..=u16::MAX {
        let packed = PackedPacketHeaders {
            source: PackedPacketHeaderSource::MarkerSegments {
                header: &header,
                marker,
                logical_start: usize::MAX,
            },
            length: 0,
            fragments: u16::MAX,
        };
        let expected = if marker == 0xff60 {
            Err(input_error_literal(0, MalformedKind::InvalidMarkerLength))
        } else {
            Ok(Vec::new())
        };
        assert_eq!(packed.reassemble(&limits), expected);
    }
    for cap in [1, ResourceLimits::default().maximum_packet_header_bytes()] {
        let limits = limits.with_maximum_packet_header_bytes(cap).unwrap();
        for length in [0, 1, usize::MAX] {
            let packed = PackedPacketHeaders {
                source: PackedPacketHeaderSource::None,
                length,
                fragments: u16::MAX,
            };
            assert!(!packed.is_present());
            assert_eq!(
                (packed.len(), packed.is_empty(), packed.fragment_count()),
                (length, length == 0, u16::MAX)
            );
            let expected = if length as u64 > cap {
                Err(DecodeError::LimitExceeded {
                    resource: Resource::PacketHeaderBytes,
                    limit: cap,
                    actual: length as u64,
                })
            } else {
                Ok(Vec::new())
            };
            assert_eq!(packed.reassemble(&limits), expected);
        }
    }
    let packed = PackedPacketHeaders {
        source: PackedPacketHeaderSource::MarkerSegments {
            header: &[],
            marker: 0,
            logical_start: usize::MAX,
        },
        length: 1,
        fragments: 0,
    };
    assert_eq!(
        packed.reassemble(&limits),
        Err(input_error_literal(0, MalformedKind::ArithmeticOverflow))
    );
    assert_eq!(packed_packet_headers_none(), PackedPacketHeaders::none());
    assert_eq!(packet_lengths_none(), PacketLengths::none());
}

#[test]
fn raw_progression_owner_records_preserve_inverted_windows_duplicates_and_boundaries() {
    let orders = [
        ProgressionOrder::Lrcp,
        ProgressionOrder::Rlcp,
        ProgressionOrder::Rpcl,
        ProgressionOrder::Pcrl,
        ProgressionOrder::Cprl,
    ];
    let mut records = Vec::new();
    for progression_order in orders {
        for resolution_start in [0, 1, u8::MAX] {
            for resolution_end in [0, 1, u8::MAX] {
                for component_start in [0, 1, u16::MAX] {
                    for component_end in [0, 1, u16::MAX] {
                        for layer_end in [0, 1, u16::MAX] {
                            let record = ProgressionChange {
                                resolution_start,
                                component_start,
                                layer_end,
                                resolution_end,
                                component_end,
                                progression_order,
                            };
                            for layer in [0, 1, u16::MAX] {
                                for resolution in [0, 1, u8::MAX] {
                                    for component in [0, 1, u16::MAX] {
                                        let expected = (0..layer_end).contains(&layer)
                                            && (resolution_start..resolution_end)
                                                .contains(&resolution)
                                            && (component_start..component_end)
                                                .contains(&component);
                                        assert_eq!(
                                            record.contains(layer, resolution, component),
                                            expected
                                        );
                                    }
                                }
                            }
                            records.extend_from_slice(&[record, record]);
                        }
                    }
                }
            }
        }
    }
    let changes = ProgressionChanges::from_records(records.clone());
    assert_eq!(changes.records(), records);
    assert_eq!(changes.len(), records.len());
    assert!(changes.is_present());
    assert!(!changes.is_empty());
    let empty = ProgressionChanges::from_records(Vec::new());
    assert!(empty.records().is_empty());
    assert_eq!(empty.len(), 0);
    assert!(!empty.is_present());
    assert!(empty.is_empty());
}

#[test]
fn complete_packet_style_owners_preserve_raw_counts_styles_and_header_presence() {
    let mut style = CodingStyle {
        progression_order: ProgressionOrder::Lrcp,
        layers: 0,
        multiple_component_transform: true,
        decomposition_levels: u8::MAX,
        decomposition_structure: Some(u8::MAX),
        decomposition_directions: [DecompositionDirection::None; 32],
        code_block_width: 0,
        code_block_height: u16::MAX,
        code_block_style: u8::MAX,
        transform: WaveletTransform::Arbitrary(u8::MAX),
        precincts_defined: false,
        sop_markers: true,
        eph_markers: true,
        precinct_exponents: [(u8::MAX, u8::MAX); 33],
    };
    let styles = core::array::from_fn(|index| CodingStyle {
        layers: u16::try_from(index).unwrap() * 999,
        code_block_style: u8::try_from(index).unwrap(),
        ..style
    });
    let mut table = ComponentCodingStyles {
        components: 0,
        styles,
    };
    for count in 0..=u16::MAX {
        table.components = count;
        for index in [0, 1, 63, 64, 65, u16::MAX - 1, u16::MAX] {
            let expected = if index < count && usize::from(index) < styles.len() {
                Ok(styles[usize::from(index)])
            } else {
                Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::InvalidCodingStyle,
                })
            };
            assert_eq!(table.style(index), expected);
        }
    }
    for count in [0, 1, 63, 64, 65, u16::MAX] {
        table.components = count;
        for index in 0..=u16::MAX {
            let expected = if index < count && usize::from(index) < styles.len() {
                Ok(styles[usize::from(index)])
            } else {
                Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::InvalidCodingStyle,
                })
            };
            assert_eq!(table.style(index), expected);
        }
    }
    for value in 0..=u8::MAX {
        style.code_block_style = value;
        assert_eq!(
            style.tier1_coding_style(),
            Tier1CodingStyle::from_code_block_style(value)
        );
    }
    for length in [0, 1, usize::MAX] {
        for fragments in [0, 1, u16::MAX] {
            let absent = PackedPacketHeaders {
                source: PackedPacketHeaderSource::None,
                length,
                fragments,
            };
            assert!(!absent.is_present());
            for bytes in [&[][..], &[0xff, 0x60][..]] {
                for marker in [0, u16::MAX] {
                    for logical_start in [0, usize::MAX] {
                        let present = PackedPacketHeaders {
                            source: PackedPacketHeaderSource::MarkerSegments {
                                header: bytes,
                                marker,
                                logical_start,
                            },
                            length,
                            fragments,
                        };
                        assert!(present.is_present());
                    }
                }
            }
        }
    }
}

#[test]
fn raw_component_getter_covers_entire_u16_index_domain() {
    let information = core::array::from_fn(|index| {
        let index = u8::try_from(index).unwrap();
        ComponentInfo {
            precision: index % 39,
            signed: index % 2 != 0,
            x_subsampling: index,
            y_subsampling: 255 - index,
            x_registration: u16::from(index) * 997,
            y_registration: u16::MAX - u16::from(index) * 997,
        }
    });
    for components in [0, 1, 63, 64, 65, u16::MAX] {
        let size = ImageSize {
            width: 0,
            height: u32::MAX,
            x_origin: u32::MAX,
            y_origin: 1,
            components,
            uniform_bit_depth: None,
            uniform_signed: None,
            tile_width: 0,
            tile_height: 0,
            tile_x_origin: 0,
            tile_y_origin: 0,
            tiles_across: 0,
            tiles_down: 0,
            component_info: information,
        };
        for index in 0..=u16::MAX {
            let expected = if index < components && usize::from(index) < information.len() {
                Ok(information[usize::from(index)])
            } else {
                Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::InvalidImageGeometry,
                })
            };
            assert_eq!(size.component(index), expected);
            assert_eq!(image_component_info(&size, index), expected);
        }
    }
}

#[test]
fn decomposition_selectors_cover_entire_u8_level_stage_resolution_domains() {
    use DecompositionDirection::{Horizontal, None, TwoDimensional, Vertical};
    for pattern in 0..4 {
        let directions = core::array::from_fn(|index| {
            [None, Horizontal, Vertical, TwoDimensional][(index + pattern) % 4]
        });
        for levels in 0..=u8::MAX {
            let style = CodingStyle {
                progression_order: ProgressionOrder::Lrcp,
                layers: 0,
                multiple_component_transform: false,
                decomposition_levels: levels,
                decomposition_structure: Option::None,
                decomposition_directions: directions,
                code_block_width: 0,
                code_block_height: 0,
                code_block_style: 0,
                transform: WaveletTransform::Reversible5x3,
                precincts_defined: false,
                sop_markers: false,
                eph_markers: false,
                precinct_exponents: [(0, 0); 33],
            };
            let error = DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            };
            for value in 0..=u8::MAX {
                assert_eq!(
                    style.decomposition_direction(value),
                    if value < levels && usize::from(value) < directions.len() {
                        Ok(directions[usize::from(value)])
                    } else {
                        Err(error)
                    }
                );
                let stage = i16::from(levels) - i16::from(value);
                assert_eq!(
                    style.direction_for_resolution(value),
                    if value != 0 && value <= levels && stage < 32 {
                        Ok(directions[usize::try_from(stage).unwrap()])
                    } else {
                        Err(error)
                    }
                );
                let expected = if value == 0 {
                    Ok(1)
                } else if value > levels || levels > 32 {
                    Err(error)
                } else {
                    let increments: usize = directions
                        [usize::from(levels - value)..usize::from(levels)]
                        .iter()
                        .map(|direction| match direction {
                            None => 0,
                            Horizontal | Vertical => 1,
                            TwoDimensional => 3,
                        })
                        .sum();
                    Ok(1 + increments)
                };
                assert_eq!(style.subband_count_through_resolution(value), expected);
            }
        }
    }
}

type MccCollectionFixture<'a> = (&'a [u8], &'a [u8], bool, u8, u8);

fn segment(marker: u16, payload: &[u8]) -> Vec<u8> {
    let length = u16::try_from(payload.len() + 2).unwrap();
    let mut bytes = marker.to_be_bytes().to_vec();
    bytes.extend_from_slice(&length.to_be_bytes());
    bytes.extend_from_slice(payload);
    bytes
}

fn encode_packet_lengths(lengths: &[u32]) -> Vec<u8> {
    let mut encoded = Vec::new();
    for &length in lengths {
        assert_ne!(length, 0);
        let mut groups = [0_u8; 5];
        let mut value = length;
        let mut start = groups.len() - 1;
        groups[start] = u8::try_from(value & 0x7f).unwrap();
        value >>= 7;
        while value != 0 {
            start -= 1;
            groups[start] = u8::try_from(value & 0x7f).unwrap() | 0x80;
            value >>= 7;
        }
        encoded.extend_from_slice(&groups[start..]);
    }
    encoded
}

fn plm(index: u8, groups: &[&[u32]]) -> Vec<u8> {
    let mut payload = vec![index];
    for lengths in groups {
        let encoded = encode_packet_lengths(lengths);
        payload.extend_from_slice(&u32::try_from(encoded.len()).unwrap().to_be_bytes());
        payload.extend(encoded);
    }
    segment(PLM, &payload)
}

fn plt(index: u8, lengths: &[u32]) -> Vec<u8> {
    let mut payload = vec![index];
    payload.extend(encode_packet_lengths(lengths));
    segment(PLT, &payload)
}

fn ppm(index: u8, bytes: &[u8]) -> Vec<u8> {
    let mut payload = vec![index];
    payload.extend_from_slice(bytes);
    segment(PPM, &payload)
}

fn ppt(index: u8, bytes: &[u8]) -> Vec<u8> {
    let mut payload = vec![index];
    payload.extend_from_slice(bytes);
    segment(PPT, &payload)
}

fn siz() -> Vec<u8> {
    siz_with_components(1)
}

fn siz_with_components(components: u16) -> Vec<u8> {
    let mut payload = Vec::new();
    payload.extend_from_slice(&0_u16.to_be_bytes());
    payload.extend_from_slice(&64_u32.to_be_bytes());
    payload.extend_from_slice(&32_u32.to_be_bytes());
    payload.extend_from_slice(&0_u32.to_be_bytes());
    payload.extend_from_slice(&0_u32.to_be_bytes());
    payload.extend_from_slice(&64_u32.to_be_bytes());
    payload.extend_from_slice(&32_u32.to_be_bytes());
    payload.extend_from_slice(&0_u32.to_be_bytes());
    payload.extend_from_slice(&0_u32.to_be_bytes());
    payload.extend_from_slice(&components.to_be_bytes());
    let mut component = 0_u16;
    while component < components {
        payload.extend_from_slice(&[7, 1, 1]);
        component += 1;
    }
    segment(SIZ, &payload)
}

fn codestream_with_headers(
    components: u16,
    main_segments: &[Vec<u8>],
    tile_segments: &[Vec<u8>],
    tile_data: &[u8],
) -> Vec<u8> {
    let mut bytes = SOC.to_be_bytes().to_vec();
    bytes.extend(siz_with_components(components));
    for marker_segment in main_segments {
        bytes.extend(marker_segment);
    }
    let tile_part_start = bytes.len();
    let mut sot_payload = Vec::new();
    sot_payload.extend_from_slice(&0_u16.to_be_bytes());
    sot_payload.extend_from_slice(&0_u32.to_be_bytes());
    sot_payload.extend_from_slice(&[0, 1]);
    bytes.extend(segment(SOT, &sot_payload));
    for marker_segment in tile_segments {
        bytes.extend(marker_segment);
    }
    bytes.extend_from_slice(&SOD.to_be_bytes());
    bytes.extend_from_slice(tile_data);
    let tile_part_length = u32::try_from(bytes.len() - tile_part_start).unwrap();
    bytes[tile_part_start + 6..tile_part_start + 10]
        .copy_from_slice(&tile_part_length.to_be_bytes());
    bytes.extend_from_slice(&EOC.to_be_bytes());
    bytes
}

fn baseline_headers() -> [Vec<u8>; 2] {
    [
        segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]),
        segment(QCD, &[0, 0]),
    ]
}

#[test]
fn main_header_quantization_may_precede_coding_style() {
    let [cod, qcd] = baseline_headers();
    let canonical = codestream_with_headers(1, &[cod.clone(), qcd.clone()], &[], &[]);
    let reordered = codestream_with_headers(1, &[qcd, cod], &[], &[]);
    let limits = ResourceLimits::default();
    let canonical = parse_layout(&canonical, &limits).unwrap();
    let reordered = parse_layout(&reordered, &limits).unwrap();
    assert_eq!(reordered.info.coding_style, canonical.info.coding_style);
    assert_eq!(reordered.info.quantization, canonical.info.quantization);
}

#[test]
fn reordered_main_header_quantization_is_still_validated() {
    let [cod, qcd] = baseline_headers();
    let duplicate = codestream_with_headers(1, &[qcd.clone(), cod.clone(), qcd], &[], &[]);
    assert!(matches!(
        parse_layout(&duplicate, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));
    let malformed = codestream_with_headers(1, &[segment(QCD, &[0]), cod], &[], &[]);
    assert!(matches!(
        parse_layout(&malformed, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerLength,
            ..
        })
    ));
}

#[test]
fn actual_nonlinear_getters_expose_complete_raw_descriptors_without_validation() {
    let mut cases = 0;
    for component in [None, Some(0), Some(u16::MAX)] {
        for precision in [0, 1, 38, 39, u8::MAX] {
            for transform_type in [0, 1, 2, 3, 4, u8::MAX] {
                for signed in [false, true] {
                    let transform = NonlinearPointTransform {
                        component,
                        precision,
                        signed,
                        transform_type,
                        parameters: if signed { vec![] } else { vec![0, u8::MAX, 17] },
                        d_min: Some(u32::MAX),
                        d_max: None,
                        point_bits: Some(u8::MAX),
                        points: if signed {
                            vec![u32::MAX, 0, 17]
                        } else {
                            vec![]
                        },
                        gamma_parameters: Some([0, 17, u32::MAX, 3, 1]),
                    };
                    assert_eq!(transform.component(), component);
                    assert_eq!(transform.precision(), precision);
                    assert_eq!(transform.signed(), signed);
                    assert_eq!(transform.transform_type(), transform_type);
                    assert_eq!(transform.parameters(), transform.parameters);
                    assert_eq!(transform.d_min(), Some(u32::MAX));
                    assert_eq!(transform.d_max(), None);
                    assert_eq!(transform.point_bits(), Some(u8::MAX));
                    assert_eq!(transform.points(), transform.points);
                    assert_eq!(transform.gamma_parameters(), Some([0, 17, u32::MAX, 3, 1]));
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 180);
}

#[test]
fn actual_nonlinear_lookup_preserves_first_specific_then_first_default_and_all_raw_fields() {
    let selectors = [
        vec![],
        vec![None],
        vec![Some(0)],
        vec![Some(u16::MAX)],
        vec![None, Some(0)],
        vec![None, None, Some(0), Some(0)],
        vec![Some(1), Some(u16::MAX), None, Some(0)],
        vec![Some(0), None, Some(0), None],
        vec![None, Some(1), None],
    ];
    let mut cases = 0;
    for selectors in selectors {
        let extensions = Part2Extensions {
            nonlinear_transforms: selectors
                .iter()
                .enumerate()
                .map(|(index, component)| NonlinearPointTransform {
                    component: *component,
                    precision: 0,
                    signed: index % 2 == 0,
                    transform_type: u8::MAX,
                    parameters: vec![0xa5, index as u8],
                    d_min: Some(u32::MAX),
                    d_max: Some(index as u32),
                    point_bits: Some(u8::MAX),
                    points: vec![u32::MAX, 0, index as u32],
                    gamma_parameters: Some([u32::MAX, 17, index as u32, 0, 1]),
                })
                .collect(),
            ..Part2Extensions::default()
        };
        for component in 0..=u16::MAX {
            let mut specific = None;
            let mut default = None;
            for (index, selector) in selectors.iter().enumerate() {
                if *selector == Some(component) && specific.is_none() {
                    specific = Some(index);
                }
                if selector.is_none() && default.is_none() {
                    default = Some(index);
                }
            }
            let expected = specific
                .or(default)
                .map(|index| &extensions.nonlinear_transforms[index]);
            let actual = extensions.nonlinear_transform_for(component);
            assert_eq!(actual, expected);
            if let (Some(actual), Some(expected)) = (actual, expected) {
                assert!(core::ptr::eq(actual, expected));
            }
            cases += 1;
        }
    }
    assert_eq!(cases, 589_824);
}

#[test]
fn retains_selected_part2_marker_families() {
    let [cod, qcd] = baseline_headers();
    let dfs = segment(DFS, &[0, 1, 4, 0x1b]);
    let ads = segment(ADS, &[2, 1, 0x40, 1, 0]);
    let nlt = segment(NLT, &[0xff, 0xff, 7, 0]);
    let cbd = segment(CBD, &[0, 2, 7, 0x87]);
    let atk = segment(ATK, &[0x4a, 2, 0x3f, 0x80, 0, 0, 0]);
    let crg = segment(CRG, &[0, 1, 0, 2, 0, 3, 0, 4]);
    let bytes = codestream_with_headers(2, &[cod, qcd, dfs, ads, nlt, cbd, atk, crg], &[], &[]);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let extensions = &layout.info.part2_extensions;
    assert_eq!(extensions.decomposition_structures().len(), 1);
    assert_eq!(
        extensions.decomposition_structures()[0].directions(),
        &[
            DecompositionDirection::None,
            DecompositionDirection::TwoDimensional,
            DecompositionDirection::Horizontal,
            DecompositionDirection::Vertical,
        ]
    );
    assert_eq!(
        extensions.arbitrary_decompositions()[0].sublevel_depths(),
        &[1]
    );
    assert_eq!(
        extensions.arbitrary_decompositions()[0].subband_splits(),
        &[DecompositionDirection::None]
    );
    assert_eq!(extensions.nonlinear_transforms()[0].component(), None);
    assert_eq!(extensions.component_bit_depths()[1].precision, 8);
    assert!(extensions.component_bit_depths()[1].signed);
    assert_eq!(extensions.arbitrary_kernels()[0].index(), 2);
    assert_eq!(extensions.component_registrations()[1].horizontal, 3);
    assert_eq!(
        layout.info.image_size.component(1).unwrap().x_registration,
        3
    );
    assert_eq!(
        layout.info.image_size.component(1).unwrap().y_registration,
        4
    );
    assert_eq!(layout.tile_parts[0].part2_extensions, *extensions);
}

#[test]
fn tile_header_part2_markers_override_inherited_indexes() {
    let [cod, qcd] = baseline_headers();
    let main_dfs = segment(DFS, &[0, 1, 1, 0x40]);
    let tile_dfs = segment(DFS, &[0, 1, 1, 0xc0]);
    let main_nlt = segment(NLT, &[0, 0, 7, 0]);
    let tile_nlt = segment(NLT, &[0, 0, 8, 0]);
    let bytes = codestream_with_headers(
        1,
        &[cod, qcd, main_dfs, main_nlt],
        &[tile_dfs, tile_nlt],
        &[],
    );
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let tile = &layout.tile_parts[0].part2_extensions;
    assert_eq!(
        tile.decomposition_structures()[0].directions(),
        &[DecompositionDirection::Vertical]
    );
    assert_eq!(tile.nonlinear_transforms()[0].precision(), 9);
}

#[test]
fn parses_bounded_nlt_lookup_table() {
    let [cod, qcd] = baseline_headers();
    let mut payload = vec![0xff, 0xff, 7, 2];
    payload.extend_from_slice(&1_u16.to_be_bytes());
    payload.extend_from_slice(&0_u32.to_be_bytes());
    payload.extend_from_slice(&u32::MAX.to_be_bytes());
    payload.push(8);
    payload.extend_from_slice(&[0, 255]);
    let bytes = codestream_with_headers(1, &[cod, qcd, segment(NLT, &payload)], &[], &[]);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let transform = &layout.info.part2_extensions.nonlinear_transforms()[0];
    assert_eq!(transform.transform_type(), 2);
    assert_eq!(transform.d_min(), Some(0));
    assert_eq!(transform.d_max(), Some(u32::MAX));
    assert_eq!(transform.point_bits(), Some(8));
    assert_eq!(transform.points(), &[0, 255]);
}

#[test]
fn parses_gamma_nlt_fixed_point_parameters() {
    let [cod, qcd] = baseline_headers();
    let one = [1_u8, 0, 0];
    let mut payload = vec![0xff, 0xff, 7, 1];
    payload.extend_from_slice(&one);
    payload.extend_from_slice(&one);
    payload.extend_from_slice(&one);
    payload.extend_from_slice(&one);
    payload.extend_from_slice(&[0, 0, 0]);
    let bytes = codestream_with_headers(1, &[cod, qcd, segment(NLT, &payload)], &[], &[]);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(
        layout.info.part2_extensions.nonlinear_transforms()[0].gamma_parameters(),
        Some([1 << 16, 1 << 16, 1 << 16, 1 << 16, 0])
    );
}

#[test]
fn parses_uniform_cbd_descriptor() {
    let [cod, qcd] = baseline_headers();
    let cbd = segment(CBD, &[0x80, 2, 0x87]);
    let bytes = codestream_with_headers(2, &[cod, qcd, cbd], &[], &[]);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(
        layout.info.part2_extensions.component_bit_depths(),
        &[
            ComponentBitDepth {
                precision: 8,
                signed: true,
            },
            ComponentBitDepth {
                precision: 8,
                signed: true,
            },
        ]
    );
}

#[test]
fn rejects_tile_header_cbd_as_malformed() {
    let [cod, qcd] = baseline_headers();
    let bytes = codestream_with_headers(1, &[cod, qcd], &[segment(CBD, &[0, 1, 7])], &[]);
    assert!(matches!(
        parse_layout(&bytes, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));
}

#[test]
fn parses_and_executes_extended_atk_forms() {
    let [cod, qcd] = baseline_headers();
    let mut binary128 = vec![0x4c, 2];
    binary128.extend_from_slice(&(0x3fff_u128 << 112).to_be_bytes());
    binary128.push(0);
    let bytes = codestream_with_headers(1, &[cod, qcd, segment(ATK, &binary128)], &[], &[]);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let kernel = &layout.info.part2_extensions.arbitrary_kernels()[0];
    assert_eq!(kernel.coefficient_type(), 4);
    assert!(kernel.whole_sample_filter());
    assert!(kernel.whole_sample_extension());
    assert_eq!(
        crate::transform::inverse_arbitrary(&[3, 7], &[2], true, kernel).unwrap(),
        [3, 2, 7]
    );

    let reversible = segment(ATK, &[0x58, 3, 2, 0, 0, 1, 0xff, 1, 1, 1, 1]);
    let bytes = codestream_with_headers(
        1,
        &[
            baseline_headers()[0].clone(),
            baseline_headers()[1].clone(),
            reversible,
        ],
        &[],
        &[],
    );
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let kernel = &layout.info.part2_extensions.arbitrary_kernels()[0];
    assert!(kernel.reversible());
    assert_eq!(
        crate::transform::inverse_arbitrary(&[3, 7], &[2], true, kernel)
            .unwrap()
            .len(),
        3
    );
}

#[test]
fn retains_dfs_and_atk_coding_style_references() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 1, 2, 2, 0, 2]);
    let qcd = segment(QCD, &[0, 0, 0, 0, 0]);
    let dfs = segment(DFS, &[0, 1, 1, 0x40]);
    let atk = segment(ATK, &[0x58, 2, 2, 0, 0, 1, 0xff, 1, 1, 1, 1]);
    let coc = segment(COC, &[0, 0, 0x81, 2, 2, 0, 1]);
    let bytes = codestream_with_headers(1, &[cod, qcd, dfs, atk, coc], &[], &[]);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(
        layout
            .info
            .component_coding_styles
            .style(0)
            .unwrap()
            .decomposition_structure,
        Some(1)
    );
    assert_eq!(
        layout.info.coding_style.transform,
        WaveletTransform::Arbitrary(2)
    );
}

#[test]
fn resolves_mixed_dfs_sequence_into_bounded_topology() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 4, 2, 2, 0, 1]);
    let mut qcd_payload = vec![0];
    qcd_payload.extend_from_slice(&[0x40; 13]);
    let qcd = segment(QCD, &qcd_payload);
    let dfs = segment(DFS, &[0, 1, 4, 0x1b]);
    let coc = segment(COC, &[0, 0, 0x81, 2, 2, 0, 1]);
    let qcc = segment(QCC, &[0, 0, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40]);
    let bytes = codestream_with_headers(1, &[cod, qcd, dfs, coc, qcc], &[], &[]);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let style = layout.info.component_coding_styles.style(0).unwrap();
    assert_eq!(style.subband_count(), 6);
    assert_eq!(style.resolution_downsampling(0).unwrap(), (4, 4));
    assert_eq!(style.resolution_downsampling(2).unwrap(), (2, 2));
    assert_eq!(
        style.direction_for_resolution(1).unwrap(),
        DecompositionDirection::Vertical
    );
    assert_eq!(
        style.direction_for_resolution(2).unwrap(),
        DecompositionDirection::Horizontal
    );
    assert_eq!(
        style.direction_for_resolution(3).unwrap(),
        DecompositionDirection::TwoDimensional
    );
    assert_eq!(
        style.direction_for_resolution(4).unwrap(),
        DecompositionDirection::None
    );
    let quantization = layout.info.component_quantizations.quantization(0).unwrap();
    let subbands =
        crate::decode::derive_component_subbands(&layout.info.image_size, style, &quantization, 0)
            .unwrap();
    assert_eq!(subbands.len(), 6);
    assert_eq!(
        subbands
            .iter()
            .map(|band| (band.resolution, band.orientation))
            .collect::<Vec<_>>(),
        vec![
            (0, crate::tier1::SubbandOrientation::Ll),
            (1, crate::tier1::SubbandOrientation::Lh),
            (2, crate::tier1::SubbandOrientation::Hl),
            (3, crate::tier1::SubbandOrientation::Hl),
            (3, crate::tier1::SubbandOrientation::Lh),
            (3, crate::tier1::SubbandOrientation::Hh),
        ]
    );
    let plan = crate::decode::plan_progression_tile_at_with_component_overrides(
        &layout.info.image_size,
        0,
        layout.info.coding_style,
        &layout.info.component_coding_styles,
        &layout.info.component_quantizations,
        &layout.info.roi_shifts,
        &limits,
    )
    .unwrap();
    assert_eq!(plan.grid().packet_count(), 4);
    assert_eq!(plan.precincts().len(), 4);
    assert_eq!(
        plan.precincts()
            .iter()
            .map(crate::packet::PacketPrecinctDecoder::subband_count)
            .sum::<usize>(),
        6
    );
    let prepared = crate::decode::prepare_tile_component(
        &plan.components()[0],
        plan.precincts(),
        style,
        &limits,
    )
    .unwrap();
    assert_eq!((prepared.width(), prepared.height()), (64, 32));
    assert!(prepared.samples().iter().all(|sample| *sample == 0));
}

#[test]
fn validates_tlm_against_sot_tile_part_length() {
    let [cod, qcd] = baseline_headers();
    let tlm = segment(TLM, &[0, 0x40, 0, 0, 0, 14]);
    let bytes = codestream_with_headers(1, &[cod, qcd, tlm], &[], &[]);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(
        layout.info.part2_extensions.tile_part_lengths(),
        &[TilePartLength {
            tile_index: None,
            length: 14,
        }]
    );

    let [cod, qcd] = baseline_headers();
    let bad_tlm = segment(TLM, &[0, 0x40, 0, 0, 0, 15]);
    let bad = codestream_with_headers(1, &[cod, qcd, bad_tlm], &[], &[]);
    assert!(matches!(
        parse_layout(&bad, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidTilePart,
            ..
        })
    ));
}

#[test]
fn rejects_malformed_selected_part2_markers() {
    let [cod, qcd] = baseline_headers();
    for invalid in [
        segment(DFS, &[0, 0, 1, 0]),
        segment(NLT, &[0, 2, 7, 0]),
        segment(CBD, &[0, 2, 7]),
        segment(ATK, &[0, 1, 0]),
        segment(CRG, &[0, 0, 0]),
    ] {
        let bytes = codestream_with_headers(1, &[cod.clone(), qcd.clone(), invalid], &[], &[]);
        assert!(matches!(
            parse_layout(&bytes, &ResourceLimits::default()),
            Err(DecodeError::MalformedInput { .. })
        ));
    }
}

fn mct_i16(index: u8, kind: u8, values: &[i16]) -> Vec<u8> {
    let descriptor = u16::from(index) | (u16::from(kind) << 8);
    let mut payload = 0_u16.to_be_bytes().to_vec();
    payload.extend_from_slice(&descriptor.to_be_bytes());
    payload.extend_from_slice(&0_u16.to_be_bytes());
    for value in values {
        payload.extend_from_slice(&value.to_be_bytes());
    }
    segment(MCT, &payload)
}

fn mct_i16_segmented(index: u8, kind: u8, values: &[i16], split: usize) -> [Vec<u8>; 2] {
    let descriptor = u16::from(index) | (u16::from(kind) << 8);
    let mut data = Vec::new();
    for value in values {
        data.extend_from_slice(&value.to_be_bytes());
    }
    let mut first = 0_u16.to_be_bytes().to_vec();
    first.extend_from_slice(&descriptor.to_be_bytes());
    first.extend_from_slice(&1_u16.to_be_bytes());
    first.extend_from_slice(&data[..split]);
    let mut second = 1_u16.to_be_bytes().to_vec();
    second.extend_from_slice(&descriptor.to_be_bytes());
    second.extend_from_slice(&data[split..]);
    [segment(MCT, &first), segment(MCT, &second)]
}

fn mct_f32(index: u8, kind: u8, values: &[u32]) -> Vec<u8> {
    let descriptor = u16::from(index) | (u16::from(kind) << 8) | (2_u16 << 10);
    let mut payload = 0_u16.to_be_bytes().to_vec();
    payload.extend_from_slice(&descriptor.to_be_bytes());
    payload.extend_from_slice(&0_u16.to_be_bytes());
    for value in values {
        payload.extend_from_slice(&value.to_be_bytes());
    }
    segment(MCT, &payload)
}

fn mct_f64(index: u8, kind: u8, values: &[u64]) -> Vec<u8> {
    let descriptor = u16::from(index) | (u16::from(kind) << 8) | (3_u16 << 10);
    let mut payload = 0_u16.to_be_bytes().to_vec();
    payload.extend_from_slice(&descriptor.to_be_bytes());
    payload.extend_from_slice(&0_u16.to_be_bytes());
    for value in values {
        payload.extend_from_slice(&value.to_be_bytes());
    }
    segment(MCT, &payload)
}

fn mcc_collections(record: u8, collections: &[MccCollectionFixture<'_>]) -> Vec<u8> {
    let mut payload = 0_u16.to_be_bytes().to_vec();
    payload.push(record);
    payload.extend_from_slice(&0_u16.to_be_bytes());
    payload.extend_from_slice(&u16::try_from(collections.len()).unwrap().to_be_bytes());
    for &(inputs, outputs, reversible, matrix, offsets) in collections {
        payload.push(1);
        payload.extend_from_slice(&u16::try_from(inputs.len()).unwrap().to_be_bytes());
        payload.extend_from_slice(inputs);
        payload.extend_from_slice(&u16::try_from(outputs.len()).unwrap().to_be_bytes());
        payload.extend_from_slice(outputs);
        payload.extend_from_slice(&[u8::from(reversible), offsets, matrix]);
    }
    segment(MCC, &payload)
}

fn mcc(collection: u8, components: u16, reversible: bool, matrix: u8, offsets: u8) -> Vec<u8> {
    let mut payload = 0_u16.to_be_bytes().to_vec();
    payload.push(collection);
    payload.extend_from_slice(&0_u16.to_be_bytes());
    payload.extend_from_slice(&1_u16.to_be_bytes());
    payload.push(1);
    payload.extend_from_slice(&components.to_be_bytes());
    for component in 0..components {
        payload.push(u8::try_from(component).unwrap());
    }
    payload.extend_from_slice(&components.to_be_bytes());
    for component in 0..components {
        payload.push(u8::try_from(component).unwrap());
    }
    payload.extend_from_slice(&[u8::from(reversible), offsets, matrix]);
    segment(MCC, &payload)
}

fn segmented_mcc(marker: &[u8], split: usize) -> [Vec<u8>; 2] {
    let payload = &marker[4..];
    let body = &payload[7..];
    let mut first = payload[..3].to_vec();
    first.extend_from_slice(&1_u16.to_be_bytes());
    first.extend_from_slice(&payload[5..7]);
    first.extend_from_slice(&body[..split]);
    let mut second = 1_u16.to_be_bytes().to_vec();
    second.push(payload[2]);
    second.extend_from_slice(&body[split..]);
    [segment(MCC, &first), segment(MCC, &second)]
}

fn dependency_mcc(
    record: u8,
    components: u16,
    reversible: bool,
    coefficients: u8,
    offsets: u8,
) -> Vec<u8> {
    let mut marker = mcc(record, components, reversible, coefficients, offsets);
    marker[11] = 0;
    marker
}

fn wavelet_mcc(
    record: u8,
    components: u16,
    transform: u8,
    levels: u8,
    component_offset: i32,
) -> Vec<u8> {
    let mut payload = 0_u16.to_be_bytes().to_vec();
    payload.push(record);
    payload.extend_from_slice(&0_u16.to_be_bytes());
    payload.extend_from_slice(&1_u16.to_be_bytes());
    payload.push(3);
    payload.extend_from_slice(&components.to_be_bytes());
    for component in 0..components {
        payload.push(u8::try_from(component).unwrap());
    }
    payload.extend_from_slice(&components.to_be_bytes());
    for component in 0..components {
        payload.push(u8::try_from(component).unwrap());
    }
    payload.extend_from_slice(&[levels & 0x3f, 0, transform]);
    payload.extend_from_slice(&component_offset.to_be_bytes());
    segment(MCC, &payload)
}

fn mco(collections: &[u8]) -> Vec<u8> {
    let mut payload = vec![u8::try_from(collections.len()).unwrap()];
    payload.extend_from_slice(collections);
    segment(MCO, &payload)
}

fn ht_codestream(style: u8) -> Vec<u8> {
    ht_codestream_with_capability(style, 0x0008)
}

fn ht_codestream_with_capability(style: u8, capability: u16) -> Vec<u8> {
    let cap = segment(
        CAP,
        &[
            0x00,
            0x02,
            0x00,
            0x00, // Pcap^15
            capability.to_be_bytes()[0],
            capability.to_be_bytes()[1],
        ],
    );
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, style, 1]);
    let qcd = segment(QCD, &[0, 0x40]);
    let mut bytes = codestream_with_headers(1, &[cap, cod, qcd], &[], &[]);
    bytes[6..8].copy_from_slice(&HT_RSIZ_FLAG.to_be_bytes());
    bytes
}

#[test]
fn detects_ht_and_mixed_profiles_without_entering_the_block_decoder() {
    let ht = parse(&ht_codestream(0x40), &ResourceLimits::default()).unwrap();
    assert_eq!(
        ht.profile.block_coding,
        CodestreamBlockCoding::HighThroughput
    );
    assert!(ht.profile.uses_high_throughput());
    let capabilities = ht.profile.extended_capabilities().unwrap();
    assert_eq!(capabilities.p_cap(), PART_15_CAPABILITY_FLAG);
    assert_eq!(capabilities.c_capabilities(), &[8]);
    assert_eq!(capabilities.capability_for_part(15), Some(8));
    assert!(ht.profile.part15_requires_all_ht_blocks());

    let mixed = parse(&ht_codestream(0xc0), &ResourceLimits::default()).unwrap();
    assert_eq!(mixed.profile.block_coding, CodestreamBlockCoding::Mixed);
}

#[test]
fn rejects_malformed_or_inconsistent_ht_profile_signaling() {
    let invalid_style = ht_codestream(0x80);
    assert!(matches!(
        parse(&invalid_style, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidCodingStyle,
            ..
        })
    ));

    let mut missing_r_siz = ht_codestream(0x40);
    missing_r_siz[6..8].copy_from_slice(&0_u16.to_be_bytes());
    assert!(matches!(
        parse(&missing_r_siz, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidProfile,
            ..
        })
    ));

    let cap = segment(CAP, &[0, 2, 0, 0]);
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0x40, 1]);
    let qcd = segment(QCD, &[0, 0x40]);
    let mut malformed_cap = codestream_with_headers(1, &[cap, cod, qcd], &[], &[]);
    malformed_cap[6..8].copy_from_slice(&HT_RSIZ_FLAG.to_be_bytes());
    assert!(matches!(
        parse(&malformed_cap, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerLength,
            ..
        })
    ));
}

#[test]
fn validates_part15_capability_combinations() {
    let declared_legacy = parse(
        &ht_codestream_with_capability(0x00, 0x8008),
        &ResourceLimits::default(),
    )
    .unwrap();
    assert_eq!(
        declared_legacy
            .profile
            .extended_capabilities()
            .unwrap()
            .part15_block_mode(),
        Some(Part15BlockMode::HtDeclared)
    );
    assert!(!declared_legacy.profile.uses_high_throughput());

    let multi = parse(
        &ht_codestream_with_capability(0x40, 0x2008),
        &ResourceLimits::default(),
    )
    .unwrap();
    let capabilities = multi.profile.extended_capabilities().unwrap();
    assert!(capabilities.part15_allows_multiple_ht_sets());
    assert_eq!(capabilities.part15_magnitude_bound(), Some(16));
    assert!(!capabilities.part15_allows_roi());
    assert!(!capabilities.part15_allows_heterogeneous_headers());

    for malformed in [
        ht_codestream_with_capability(0x40, 0x4008),
        ht_codestream_with_capability(0x40, 0x0048),
        ht_codestream_with_capability(0x00, 0x0008),
        ht_codestream_with_capability(0xc0, 0x8008),
    ] {
        assert!(matches!(
            parse(&malformed, &ResourceLimits::default()),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::InvalidProfile,
                ..
            })
        ));
    }
}

#[test]
fn retains_bounded_profile_numbers_and_rejects_zero_most_significant_words() {
    let prf = segment(PRF, &[0x12, 0x34, 0x56, 0x78]);
    let cpf = segment(CPF, &[0x00, 0x01, 0x00, 0x02]);
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0x40, 1]);
    let qcd = segment(QCD, &[0, 0x40]);
    let cap = segment(CAP, &[0, 2, 0, 0, 0, 8]);
    let mut bytes = codestream_with_headers(
        1,
        &[cap.clone(), prf, cpf, cod.clone(), qcd.clone()],
        &[],
        &[],
    );
    bytes[6..8].copy_from_slice(&HT_RSIZ_FLAG.to_be_bytes());
    let parsed = parse(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(parsed.profile.profile().unwrap().words(), &[0x1234, 0x5678]);
    assert_eq!(
        parsed.profile.corresponding_profile().unwrap().words(),
        &[1, 2]
    );

    let bad_cpf = segment(CPF, &[0, 1, 0, 0]);
    let mut invalid = codestream_with_headers(1, &[cap, bad_cpf, cod, qcd], &[], &[]);
    invalid[6..8].copy_from_slice(&HT_RSIZ_FLAG.to_be_bytes());
    assert!(matches!(
        parse(&invalid, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidProfile,
            ..
        })
    ));
}

#[test]
fn parses_and_retains_bounded_part2_matrix_and_offset_transform() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let bytes = codestream_with_headers(
        2,
        &[
            cod,
            qcd,
            mct_i16(1, 1, &[1, 2, 3, 4]),
            mct_i16(2, 2, &[5, 6]),
            mcc(7, 2, true, 1, 2),
            mco(&[7]),
        ],
        &[],
        &[],
    );
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let transform = layout.info.multiple_component_transform.unwrap();
    let stage = &transform.stages()[0];
    let collection = &stage.collections()[0];
    assert_eq!(stage.index(), 7);
    assert!(collection.reversible());
    assert_eq!(collection.input_components(), &[0, 1]);
    assert_eq!(collection.output_components(), &[0, 1]);
    assert_eq!(collection.matrix().unwrap().index(), 1);
    assert_eq!(collection.matrix().unwrap().values(), &[1, 2, 3, 4]);
    assert_eq!(collection.offsets().unwrap().values(), &[5, 6]);
}

#[test]
fn reassembles_segmented_mct_and_mcc_with_contiguous_indexes() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let matrix = mct_i16_segmented(1, 1, &[1, 2, 3, 4], 3);
    let record = segmented_mcc(&mcc(7, 2, true, 1, 0), 5);
    let bytes = codestream_with_headers(
        2,
        &[
            cod,
            qcd,
            matrix[0].clone(),
            record[0].clone(),
            matrix[1].clone(),
            record[1].clone(),
            mco(&[7]),
        ],
        &[],
        &[],
    );
    let transform = parse_layout(&bytes, &ResourceLimits::default())
        .unwrap()
        .info
        .multiple_component_transform
        .unwrap();
    assert_eq!(
        transform.stages()[0].collections()[0]
            .matrix()
            .unwrap()
            .values(),
        &[1, 2, 3, 4]
    );
}

#[test]
fn rejects_duplicate_discontinuous_and_incomplete_mct_fragments() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let parts = mct_i16_segmented(1, 1, &[1], 1);
    let cases = [
        vec![cod.clone(), qcd.clone(), parts[0].clone(), parts[0].clone()],
        {
            let mut wrong = parts[1].clone();
            wrong[4..6].copy_from_slice(&2_u16.to_be_bytes());
            vec![cod.clone(), qcd.clone(), parts[0].clone(), wrong]
        },
        vec![cod, qcd, parts[0].clone()],
    ];
    for headers in cases {
        let bytes = codestream_with_headers(1, &headers, &[], &[]);
        assert!(matches!(
            parse_layout(&bytes, &ResourceLimits::default()),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::InvalidTransform | MalformedKind::MissingRequiredStructure,
                ..
            })
        ));
    }
}

#[test]
fn resolves_dependency_and_wavelet_collection_semantics() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let dependency = codestream_with_headers(
        2,
        &[
            cod.clone(),
            qcd.clone(),
            mct_i16(1, 0, &[1, 2]),
            dependency_mcc(3, 2, true, 1, 0),
            mco(&[3]),
        ],
        &[],
        &[],
    );
    let transform = parse_layout(&dependency, &ResourceLimits::default())
        .unwrap()
        .info
        .multiple_component_transform
        .unwrap();
    let collection = &transform.stages()[0].collections()[0];
    assert_eq!(collection.kind(), MctCollectionKind::Dependency);
    assert_eq!(collection.matrix().unwrap().values(), &[1, 2]);

    let wavelet = codestream_with_headers(
        3,
        &[cod, qcd, wavelet_mcc(4, 3, 1, 1, -1), mco(&[4])],
        &[],
        &[],
    );
    let transform = parse_layout(&wavelet, &ResourceLimits::default())
        .unwrap()
        .info
        .multiple_component_transform
        .unwrap();
    let collection = &transform.stages()[0].collections()[0];
    assert_eq!(collection.kind(), MctCollectionKind::Wavelet);
    let wavelet = collection.wavelet().unwrap();
    assert_eq!(wavelet.transform(), MctWaveletType::Reversible5x3);
    assert_eq!(wavelet.levels(), 1);
    assert_eq!(wavelet.component_offset(), -1);
}

#[test]
fn rejects_reserved_mcc_transform_type_as_malformed_not_unsupported() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let mut reserved = mcc(3, 1, true, 0, 0);
    reserved[11] = 2;
    let bytes = codestream_with_headers(1, &[cod, qcd, reserved, mco(&[3])], &[], &[]);
    assert!(matches!(
        parse_layout(&bytes, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidTransform,
            ..
        })
    ));
}

#[test]
fn rejects_unknown_or_reserved_markers_as_malformed() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let reserved = segment(0xff65, &[]);
    let main = codestream_with_headers(1, &[cod.clone(), qcd.clone(), reserved.clone()], &[], &[]);
    assert!(matches!(
        parse_layout(&main, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarker,
            ..
        })
    ));
    let tile = codestream_with_headers(1, &[cod, qcd], &[reserved], &[]);
    assert!(matches!(
        parse_layout(&tile, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarker,
            ..
        })
    ));
}

#[test]
fn converts_f32_mct_values_to_deterministic_fixed_point() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let bytes = codestream_with_headers(
        1,
        &[
            cod,
            qcd,
            mct_f32(1, 1, &[1.5_f32.to_bits()]),
            mcc(3, 1, false, 1, 0),
            mco(&[3]),
        ],
        &[],
        &[],
    );
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let transform = layout.info.multiple_component_transform.unwrap();
    let matrix = transform.stages()[0].collections()[0].matrix().unwrap();
    assert_eq!(matrix.fraction_bits(), MCT_FIXED_BITS);
    assert_eq!(matrix.values(), &[6_442_450_944]);
}

#[test]
fn converts_finite_binary64_and_rejects_non_finite_or_overflow() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let valid = codestream_with_headers(
        1,
        &[
            cod.clone(),
            qcd.clone(),
            mct_f64(1, 1, &[1.25_f64.to_bits()]),
            mcc(3, 1, false, 1, 0),
            mco(&[3]),
        ],
        &[],
        &[],
    );
    let transform = parse_layout(&valid, &ResourceLimits::default())
        .unwrap()
        .info
        .multiple_component_transform
        .unwrap();
    let matrix = transform.stages()[0].collections()[0].matrix().unwrap();
    assert_eq!(matrix.numeric_format(), MctNumericFormat::Float64);
    assert_eq!(matrix.fraction_bits(), MCT_FIXED_BITS);
    assert_eq!(matrix.values(), &[5_368_709_120]);

    for bits in [
        f64::INFINITY.to_bits(),
        f64::NAN.to_bits(),
        f64::MAX.to_bits(),
    ] {
        let invalid = codestream_with_headers(
            1,
            &[
                cod.clone(),
                qcd.clone(),
                mct_f64(1, 1, &[bits]),
                mcc(3, 1, false, 1, 0),
                mco(&[3]),
            ],
            &[],
            &[],
        );
        assert!(matches!(
            parse_layout(&invalid, &ResourceLimits::default()),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::InvalidTransform,
                ..
            })
        ));
    }
}

#[test]
fn resolves_multiple_records_collections_subsets_permutations_and_tile_override() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let bytes = codestream_with_headers(
        3,
        &[
            cod,
            qcd,
            mct_i16(1, 1, &[1, 0, 0, 1]),
            mct_i16(2, 1, &[1]),
            mcc_collections(7, &[(&[0, 2], &[2, 0], true, 1, 0)]),
            mcc_collections(8, &[(&[0], &[0], true, 2, 0), (&[1], &[1], true, 2, 0)]),
            mco(&[7, 8]),
        ],
        &[mct_i16(2, 1, &[2]), mco(&[8, 7])],
        &[],
    );
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let main = layout.info.multiple_component_transform.unwrap();
    assert_eq!(main.stages().len(), 2);
    assert_eq!(main.stages()[0].index(), 7);
    assert_eq!(
        main.stages()[0].collections()[0].input_components(),
        &[0, 2]
    );
    assert_eq!(
        main.stages()[0].collections()[0].output_components(),
        &[2, 0]
    );
    assert_eq!(main.stages()[1].collections().len(), 2);
    let tile = layout.tile_parts[0]
        .multiple_component_transform
        .as_ref()
        .unwrap();
    assert_eq!(tile.stages()[0].index(), 8);
    assert_eq!(
        tile.stages()[0].collections()[0].matrix().unwrap().values(),
        &[2]
    );
}

#[test]
fn accepts_combined_part1_and_ordered_part2_inverse_transforms() {
    let cod = segment(COD, &[0, 0, 0, 1, 1, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let bytes = codestream_with_headers(
        3,
        &[
            cod,
            qcd,
            mct_i16(1, 1, &[1, 0, 0, 0, 1, 0, 0, 0, 1]),
            mcc(7, 3, true, 1, 0),
            mco(&[7]),
        ],
        &[],
        &[],
    );
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert!(layout.info.coding_style.multiple_component_transform);
    assert_eq!(
        layout
            .info
            .multiple_component_transform
            .unwrap()
            .stages()
            .len(),
        1
    );
}

#[test]
fn rejects_invalid_or_unsupported_part2_transform_graphs() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let malformed_matrix = codestream_with_headers(
        2,
        &[
            cod.clone(),
            qcd.clone(),
            mct_i16(1, 1, &[1, 0, 1]),
            mcc(7, 2, true, 1, 0),
            mco(&[7]),
        ],
        &[],
        &[],
    );
    assert!(matches!(
        parse_layout(&malformed_matrix, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidTransform,
            ..
        })
    ));

    let dependency_chain = codestream_with_headers(
        2,
        &[
            cod.clone(),
            qcd.clone(),
            mct_i16(1, 1, &[1, 0, 0, 1]),
            mcc(7, 2, true, 1, 0),
            mco(&[7, 7]),
        ],
        &[],
        &[],
    );
    assert!(matches!(
        parse_layout(&dependency_chain, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidTransform,
            ..
        })
    ));

    let nan = codestream_with_headers(
        1,
        &[
            cod,
            qcd,
            mct_f32(1, 1, &[f32::NAN.to_bits()]),
            mcc(3, 1, false, 1, 0),
            mco(&[3]),
        ],
        &[],
        &[],
    );
    assert!(matches!(
        parse_layout(&nan, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidTransform,
            ..
        })
    ));
}

fn codestream(tile_data: &[u8], zero_length_tile_part: bool) -> Vec<u8> {
    codestream_with_styles(
        tile_data,
        zero_length_tile_part,
        &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1],
        &[0, 0],
    )
}

fn codestream_with_styles(
    tile_data: &[u8],
    zero_length_tile_part: bool,
    cod_payload: &[u8],
    qcd_payload: &[u8],
) -> Vec<u8> {
    let mut bytes = SOC.to_be_bytes().to_vec();
    bytes.extend(siz());
    bytes.extend(segment(COD, cod_payload));
    bytes.extend(segment(QCD, qcd_payload));
    let tile_part_start = bytes.len();
    let mut sot_payload = Vec::new();
    sot_payload.extend_from_slice(&0_u16.to_be_bytes());
    sot_payload.extend_from_slice(&0_u32.to_be_bytes());
    sot_payload.extend_from_slice(&[0, 1]);
    bytes.extend(segment(SOT, &sot_payload));
    bytes.extend_from_slice(&SOD.to_be_bytes());
    bytes.extend_from_slice(tile_data);
    let tile_part_length = u32::try_from(bytes.len() - tile_part_start).unwrap();
    if !zero_length_tile_part {
        let length_offset = tile_part_start + 6;
        bytes[length_offset..length_offset + 4].copy_from_slice(&tile_part_length.to_be_bytes());
    }
    bytes.extend_from_slice(&EOC.to_be_bytes());
    bytes
}

fn poc(records: &[[u8; 7]]) -> Vec<u8> {
    let mut payload = Vec::new();
    for record in records {
        payload.extend_from_slice(record);
    }
    segment(POC, &payload)
}

fn two_part_codestream(first_header: &[Vec<u8>], second_header: &[Vec<u8>]) -> Vec<u8> {
    let mut bytes = SOC.to_be_bytes().to_vec();
    bytes.extend(siz());
    bytes.extend(segment(COD, &[0, 0, 0, 2, 0, 0, 2, 2, 0, 1]));
    bytes.extend(segment(QCD, &[0, 0]));
    for (index, header) in [first_header, second_header].iter().enumerate() {
        let start = bytes.len();
        let mut sot = Vec::new();
        sot.extend_from_slice(&0_u16.to_be_bytes());
        sot.extend_from_slice(&0_u32.to_be_bytes());
        sot.extend_from_slice(&[u8::try_from(index).unwrap(), 2]);
        bytes.extend(segment(SOT, &sot));
        for marker in *header {
            bytes.extend(marker);
        }
        bytes.extend_from_slice(&SOD.to_be_bytes());
        bytes.push(0);
        let length = u32::try_from(bytes.len() - start).unwrap();
        bytes[start + 6..start + 10].copy_from_slice(&length.to_be_bytes());
    }
    bytes.extend_from_slice(&EOC.to_be_bytes());
    bytes
}

#[test]
fn parses_bounded_tile_part() {
    let bytes = codestream(&[1, 2, 3], false);
    let info = parse(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(info.image_size.width, 64);
    assert_eq!(info.image_size.height, 32);
    assert_eq!(info.image_size.components, 1);
    assert_eq!(info.coding_style.progression_order, ProgressionOrder::Lrcp);
    assert_eq!(info.coding_style.transform, WaveletTransform::Reversible5x3);
    assert_eq!(info.coding_style.code_block_width, 16);
    assert_eq!(
        info.coding_style.tier1_coding_style().unwrap(),
        Tier1CodingStyle::default()
    );
    assert_eq!(info.quantization.style, QuantizationStyle::None);
    assert_eq!(info.quantization.step_count, 1);
    assert_eq!(
        info.quantization.step(0).unwrap(),
        QuantizationStep {
            exponent: 0,
            mantissa: 0,
        }
    );
    assert_eq!(info.tile_parts, 1);
    let geometry = crate::decode::derive_component_resolution_geometry(
        &info.image_size,
        info.coding_style,
        0,
        0,
    )
    .unwrap();
    assert_eq!(geometry.width, 64);
    assert_eq!(geometry.height, 32);
    assert_eq!(geometry.code_blocks, 8);
    assert_eq!(
        crate::decode::derive_packet_grid(
            &info.image_size,
            info.coding_style,
            &ResourceLimits::default(),
        )
        .unwrap()
        .packet_count(),
        1
    );
    assert_eq!(usize::try_from(info.consumed_bytes).unwrap(), bytes.len());
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(layout.tile_parts.len(), 1);
    assert_eq!(layout.tile_parts[0].tile_index, 0);
    assert_eq!(layout.tile_parts[0].tile_part_index, 0);
    assert_eq!(layout.tile_parts[0].data, [1, 2, 3]);
}

#[test]
fn parses_retains_and_persists_progression_changes() {
    let first = poc(&[[0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 2, 1, 1, 0]]);
    let bytes = two_part_codestream(&[first], &[]);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(layout.info.progression_changes.len(), 0);
    assert_eq!(layout.tile_parts.len(), 2);
    assert_eq!(layout.tile_parts[0].progression_changes.len(), 2);
    assert!(
        layout.tile_parts[0]
            .progression_changes
            .equals(&layout.tile_parts[1].progression_changes)
    );
    let records = layout.tile_parts[1].progression_changes.records();
    assert_eq!(records[0].layer_end, 1);
    assert_eq!(records[0].progression_order, ProgressionOrder::Rlcp);
    assert_eq!(records[1].layer_end, 2);
    assert_eq!(records[1].progression_order, ProgressionOrder::Lrcp);
}

#[test]
fn validates_progression_change_ranges_coverage_duplicates_and_scope() {
    let cod = segment(COD, &[0, 0, 0, 2, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let incomplete = codestream_with_headers(
        1,
        &[cod.clone(), qcd.clone(), poc(&[[0, 0, 0, 1, 1, 1, 0]])],
        &[],
        &[0],
    );
    assert!(matches!(
        parse_layout(&incomplete, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidProgressionOrderChange,
            ..
        })
    ));

    let duplicate_record = codestream_with_headers(
        1,
        &[
            cod.clone(),
            qcd.clone(),
            poc(&[[0, 0, 0, 2, 1, 1, 0], [0, 0, 0, 2, 1, 1, 1]]),
        ],
        &[],
        &[0],
    );
    assert!(matches!(
        parse_layout(&duplicate_record, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidProgressionOrderChange,
            ..
        })
    ));

    let duplicate_marker = codestream_with_headers(
        1,
        &[
            cod,
            qcd,
            poc(&[[0, 0, 0, 2, 1, 1, 0]]),
            poc(&[[0, 0, 0, 2, 1, 1, 0]]),
        ],
        &[],
        &[0],
    );
    assert!(matches!(
        parse_layout(&duplicate_marker, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));

    let second_part =
        two_part_codestream(&[], &[poc(&[[0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 2, 1, 1, 0]])]);
    assert!(matches!(
        parse_layout(&second_part, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));
}

fn reference_two_bit_values(
    bytes: &[u8],
    offset: usize,
    cursor: usize,
    start: usize,
    count: usize,
    allow_zero: bool,
) -> Result<Vec<u8>, DecodeError> {
    let read = |relative: usize| {
        let index = start as u128 + relative as u128;
        if index > usize::MAX as u128 {
            Err(DecodeError::MalformedInput {
                offset: cursor as u64,
                kind: MalformedKind::ArithmeticOverflow,
            })
        } else {
            bytes
                .get(index as usize)
                .copied()
                .ok_or(DecodeError::MalformedInput {
                    offset: offset as u64,
                    kind: MalformedKind::InvalidMarkerLength,
                })
        }
    };
    let mut values = Vec::new();
    for index in 0..count {
        let byte = read(index / 4)?;
        let divisor = 4_u8.pow(u32::try_from(3 - index % 4).unwrap());
        let value = byte / divisor % 4;
        if !allow_zero && value == 0 {
            return Err(DecodeError::MalformedInput {
                offset: offset as u64,
                kind: MalformedKind::InvalidCodingStyle,
            });
        }
        values.push(value);
    }
    if !count.is_multiple_of(4) {
        let last = read(count / 4)?;
        let divisor = 4_u8.pow(u32::try_from(4 - count % 4).unwrap());
        if last % divisor != 0 {
            return Err(DecodeError::MalformedInput {
                offset: offset as u64,
                kind: MalformedKind::InvalidCodingStyle,
            });
        }
    }
    Ok(values)
}

fn reference_decomposition_code(value: u8) -> DecompositionDirection {
    [
        DecompositionDirection::None,
        DecompositionDirection::TwoDimensional,
        DecompositionDirection::Horizontal,
        DecompositionDirection::Vertical,
    ][usize::from(value)]
}

fn reference_dfs_payload(
    bytes: &[u8],
    offset: usize,
) -> Result<DecompositionStructure, DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    if bytes.len() < 3 {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    let descriptor = u16::from_be_bytes([bytes[0], bytes[1]]);
    let levels = usize::from(bytes[2]);
    if !(1..16).contains(&descriptor) || !(1..=32).contains(&levels) {
        return Err(malformed(MalformedKind::InvalidCodingStyle));
    }
    if bytes.len() != 3 + levels.div_ceil(4) {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    let directions = (0..levels)
        .map(|level| {
            let divisor = 4_u8.pow(u32::try_from(3 - level % 4).unwrap());
            reference_decomposition_code(bytes[3 + level / 4] / divisor % 4)
        })
        .collect();
    Ok(DecompositionStructure {
        index: descriptor as u8,
        directions,
    })
}

fn reference_ads_payload(
    bytes: &[u8],
    offset: usize,
    cursor: usize,
) -> Result<ArbitraryDecomposition, DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    if bytes.len() < 3 {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    if !(1..=127).contains(&bytes[0]) {
        return Err(malformed(MalformedKind::InvalidCodingStyle));
    }
    let depth_count = usize::from(bytes[1]);
    let split_position = 2 + depth_count.div_ceil(4);
    let split_count = usize::from(
        *bytes
            .get(split_position)
            .ok_or_else(|| malformed(MalformedKind::InvalidMarkerLength))?,
    );
    if bytes.len() != split_position + 1 + split_count.div_ceil(4) {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    let sublevel_depths = reference_two_bit_values(bytes, offset, cursor, 2, depth_count, false)?;
    let codes =
        reference_two_bit_values(bytes, offset, cursor, split_position + 1, split_count, true)?;
    Ok(ArbitraryDecomposition {
        index: bytes[0],
        sublevel_depths,
        subband_splits: codes
            .into_iter()
            .map(reference_decomposition_code)
            .collect(),
    })
}

fn raw_dfs_payload(descriptor: u16, levels: u8) -> Vec<u8> {
    let mut bytes = descriptor.to_be_bytes().to_vec();
    bytes.push(levels);
    bytes.extend((0..usize::from(levels).div_ceil(4)).map(|index| {
        u8::try_from(index)
            .unwrap()
            .wrapping_mul(17)
            .wrapping_add(0x1b)
    }));
    bytes
}

fn pack_decomposition_values(values: &[u8]) -> Vec<u8> {
    let mut bytes = vec![0; values.len().div_ceil(4)];
    for (index, value) in values.iter().enumerate() {
        bytes[index / 4] += *value * 4_u8.pow(u32::try_from(3 - index % 4).unwrap());
    }
    bytes
}

fn raw_ads_payload(index: u8, depth_count: u8, split_count: u8, pattern: usize) -> Vec<u8> {
    let depths: Vec<u8> = (0..usize::from(depth_count))
        .map(|position| {
            if pattern == 0 {
                1
            } else {
                1 + (position % 3) as u8
            }
        })
        .collect();
    let splits: Vec<u8> = (0..usize::from(split_count))
        .map(|position| {
            if pattern == 0 {
                0
            } else {
                (position % 4) as u8
            }
        })
        .collect();
    let mut bytes = vec![index, depth_count];
    bytes.extend(pack_decomposition_values(&depths));
    bytes.push(split_count);
    bytes.extend(pack_decomposition_values(&splits));
    bytes
}

fn assert_decomposition_owner_case(
    ads: bool,
    bytes: &[u8],
    mode: usize,
    limits: &ResourceLimits,
    budget: (u64, u64),
    offset: usize,
) {
    let (metadata, work) = budget;
    let index = if ads {
        bytes.first().copied().unwrap_or(0)
    } else if bytes.len() >= 2 {
        (u16::from_be_bytes([bytes[0], bytes[1]]) % 16) as u8
    } else {
        0
    };
    let mut extensions = raw_owned_tile_part_fixture(0).part2_extensions;
    if ads {
        extensions.arbitrary_decompositions = if mode == 0 {
            vec![]
        } else {
            vec![
                ArbitraryDecomposition {
                    index: 0,
                    sublevel_depths: vec![0],
                    subband_splits: vec![DecompositionDirection::Vertical],
                },
                ArbitraryDecomposition {
                    index: u8::MAX,
                    sublevel_depths: vec![255],
                    subband_splits: vec![],
                },
            ]
        };
        if mode == 2 {
            extensions.arbitrary_decompositions.insert(
                1,
                ArbitraryDecomposition {
                    index,
                    sublevel_depths: vec![2],
                    subband_splits: vec![DecompositionDirection::Horizontal],
                },
            );
            extensions
                .arbitrary_decompositions
                .push(ArbitraryDecomposition {
                    index,
                    sublevel_depths: vec![3, 3],
                    subband_splits: vec![DecompositionDirection::None],
                });
        }
    } else {
        extensions.decomposition_structures = if mode == 0 {
            vec![]
        } else {
            vec![
                DecompositionStructure {
                    index: 0,
                    directions: vec![DecompositionDirection::Vertical],
                },
                DecompositionStructure {
                    index: u8::MAX,
                    directions: vec![],
                },
            ]
        };
        if mode == 2 {
            extensions.decomposition_structures.insert(
                1,
                DecompositionStructure {
                    index,
                    directions: vec![DecompositionDirection::Horizontal],
                },
            );
            extensions
                .decomposition_structures
                .push(DecompositionStructure {
                    index,
                    directions: vec![
                        DecompositionDirection::None,
                        DecompositionDirection::Vertical,
                    ],
                });
        }
    }
    extensions.metadata_bytes = metadata;
    let mut expected = extensions.clone();
    let (mut result, next_work, next_metadata) =
        reference_extension_charge(bytes.len(), 17, work, metadata, limits);
    expected.metadata_bytes = next_metadata;
    if result.is_ok() {
        if ads {
            result = match reference_ads_payload(bytes, offset, 17) {
                Err(error) => Err(error),
                Ok(replacement) => {
                    if let Some(existing) = expected
                        .arbitrary_decompositions
                        .iter_mut()
                        .find(|entry| entry.index == replacement.index)
                    {
                        *existing = replacement;
                    } else {
                        expected.arbitrary_decompositions.push(replacement);
                    }
                    Ok(())
                }
            };
        } else {
            result = match reference_dfs_payload(bytes, offset) {
                Err(error) => Err(error),
                Ok(replacement) => {
                    if let Some(existing) = expected
                        .decomposition_structures
                        .iter_mut()
                        .find(|entry| entry.index == replacement.index)
                    {
                        *existing = replacement;
                    } else {
                        expected.decomposition_structures.push(replacement);
                    }
                    Ok(())
                }
            };
        }
    }
    let mut parser = new_parser(&[], limits).unwrap();
    parser.position = 17;
    parser.work_units = work;
    parser.packet_length_bytes = u64::MAX;
    parser.packet_lengths = u64::MAX - 1;
    let segment = Segment {
        marker: 0x1234,
        offset,
        payload: bytes,
    };
    if ads {
        assert_eq!(
            parser.decode_ads_payload(segment),
            reference_ads_payload(bytes, offset, 17)
        );
        assert_eq!(parser.parse_ads(segment, &mut extensions), result);
    } else {
        assert_eq!(
            parser.decode_dfs_payload(segment),
            reference_dfs_payload(bytes, offset)
        );
        assert_eq!(parser.parse_dfs(segment, &mut extensions), result);
    }
    assert_eq!(extensions, expected);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (17, next_work, u64::MAX, u64::MAX - 1)
    );
    assert!(core::ptr::eq(parser.limits, limits));
    assert!(parser.input.is_empty());
}

#[test]
fn actual_two_bit_values_preserve_terminal_padding_and_error_order() {
    let limits = ResourceLimits::HARDENED;
    let mut byte_cases = 0;
    for byte in 0..=u8::MAX {
        let bytes = [0xa5, byte, 0];
        for count in 0..=4 {
            for allow in [false, true] {
                for cursor in [0, 17, usize::MAX] {
                    let mut parser = new_parser(&[], &limits).unwrap();
                    parser.position = cursor;
                    for offset in [0, usize::MAX] {
                        assert_eq!(
                            parser.unpack_two_bit_values(
                                Segment {
                                    marker: 0x1234,
                                    offset,
                                    payload: &bytes
                                },
                                1,
                                count,
                                allow
                            ),
                            reference_two_bit_values(&bytes, offset, cursor, 1, count, allow)
                        );
                        byte_cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(byte_cases, 15_360);
    let mut frontiers = 0;
    for count in 0..=255 {
        for pattern in [0, 255, 0x55, 0xaa] {
            for start in [0, 1, 5, usize::MAX] {
                for length in [0, 1, 4, 65, 129] {
                    let bytes = vec![pattern; length];
                    for allow in [false, true] {
                        for cursor in [0, 17, usize::MAX] {
                            let mut parser = new_parser(&[], &limits).unwrap();
                            parser.position = cursor;
                            for offset in [0, usize::MAX] {
                                assert_eq!(
                                    parser.unpack_two_bit_values(
                                        Segment {
                                            marker: 0x1234,
                                            offset,
                                            payload: &bytes
                                        },
                                        start,
                                        count,
                                        allow
                                    ),
                                    reference_two_bit_values(
                                        &bytes, offset, cursor, start, count, allow
                                    )
                                );
                                frontiers += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(frontiers, 245_760);
}

#[test]
fn actual_dfs_preserves_descriptor_bytes_unused_padding_and_first_registry_slot() {
    let base = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &base).unwrap();
    let levels = [0, 1, 2, 3, 4, 31, 32, 33, 255];
    let mut payload_cases = 0;
    for descriptor in 0..=u16::MAX {
        for level in levels {
            let source = raw_dfs_payload(descriptor, level);
            for variant in 0..3 {
                let mut bytes = source.clone();
                if variant == 1 {
                    bytes.pop();
                } else if variant == 2 {
                    bytes.push(0);
                }
                for offset in [0, usize::MAX] {
                    assert_eq!(
                        parser.decode_dfs_payload(Segment {
                            marker: 0x1234,
                            offset,
                            payload: &bytes
                        }),
                        reference_dfs_payload(&bytes, offset)
                    );
                    payload_cases += 1;
                }
            }
        }
    }
    assert_eq!(payload_cases, 3_538_944);
    let limits = [
        base,
        base.with_maximum_metadata_bytes(0).unwrap(),
        base.with_maximum_metadata_bytes(8).unwrap(),
        base.with_maximum_work_units(0).unwrap(),
    ];
    let mut owners = 0;
    for descriptor in [0_u16, 1, 5, 15, 16, 255, 256, u16::MAX] {
        for level in levels {
            for variant in 0..3 {
                let mut bytes = raw_dfs_payload(descriptor, level);
                if variant == 1 {
                    bytes.pop();
                } else if variant == 2 {
                    bytes.push(0);
                }
                for mode in 0..3 {
                    for metadata in [0, u64::MAX - 4, u64::MAX] {
                        for work in [0, u64::MAX - 4, u64::MAX] {
                            for limit in &limits {
                                for offset in [0, usize::MAX] {
                                    assert_decomposition_owner_case(
                                        false,
                                        &bytes,
                                        mode,
                                        limit,
                                        (metadata, work),
                                        offset,
                                    );
                                    owners += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(owners, 46_656);
    let payload = [0, 5, 3, 0x1b];
    let mut input = DFS.to_be_bytes().to_vec();
    input.extend(u16::try_from(payload.len() + 2).unwrap().to_be_bytes());
    input.extend(payload);
    let mut parser = new_parser(&input, &base).unwrap();
    let segment = parser.read_segment().unwrap();
    let mut extensions = Part2Extensions::default();
    parser.parse_dfs(segment, &mut extensions).unwrap();
    assert_eq!(
        extensions.decomposition_structures,
        vec![DecompositionStructure {
            index: 5,
            directions: vec![
                DecompositionDirection::None,
                DecompositionDirection::TwoDimensional,
                DecompositionDirection::Horizontal
            ],
        }]
    );
    assert_eq!(
        (
            extensions.metadata_bytes,
            parser.work_units,
            parser.position
        ),
        (8, 9, input.len())
    );
}

#[test]
fn actual_ads_preserves_all_raw_counts_padding_first_duplicates_and_owner_fields() {
    let base = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &base).unwrap();
    let mut count_pairs = 0;
    for depths in 0..=u8::MAX {
        for splits in 0..=u8::MAX {
            for pattern in 0..2 {
                let bytes = raw_ads_payload(1, depths, splits, pattern);
                for offset in [0, usize::MAX] {
                    assert_eq!(
                        parser.decode_ads_payload(Segment {
                            marker: 0x1234,
                            offset,
                            payload: &bytes
                        }),
                        reference_ads_payload(&bytes, offset, 0)
                    );
                    count_pairs += 1;
                }
            }
        }
    }
    assert_eq!(count_pairs, 262_144);
    let counts = [0, 1, 2, 3, 4, 31, 32, 33, 254, 255];
    let mut headers = 0;
    for index in 0..=u8::MAX {
        for depths in counts {
            for splits in counts {
                for variant in 0..3 {
                    let mut bytes = raw_ads_payload(index, depths, splits, 1);
                    if variant == 1 {
                        bytes.pop();
                    } else if variant == 2 {
                        bytes.push(0);
                    }
                    for offset in [0, usize::MAX] {
                        assert_eq!(
                            parser.decode_ads_payload(Segment {
                                marker: 0x1234,
                                offset,
                                payload: &bytes
                            }),
                            reference_ads_payload(&bytes, offset, 0)
                        );
                        headers += 1;
                    }
                }
            }
        }
    }
    assert_eq!(headers, 153_600);
    let mut mutations = 0;
    for index in [1, 127] {
        for depths in [0, 1, 3, 4, 32, 255] {
            for splits in [0, 1, 3, 4, 32, 255] {
                let source = raw_ads_payload(index, depths, splits, 1);
                for position in 0..source.len() {
                    for byte in 0..=u8::MAX {
                        let mut bytes = source.clone();
                        bytes[position] = byte;
                        for offset in [0, usize::MAX] {
                            assert_eq!(
                                parser.decode_ads_payload(Segment {
                                    marker: 0x1234,
                                    offset,
                                    payload: &bytes
                                }),
                                reference_ads_payload(&bytes, offset, 0)
                            );
                            mutations += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(mutations, 1_032_192);
    let limits = [
        base,
        base.with_maximum_metadata_bytes(0).unwrap(),
        base.with_maximum_metadata_bytes(8).unwrap(),
        base.with_maximum_work_units(0).unwrap(),
    ];
    let mut owners = 0;
    for index in [0, 1, 5, 127, 128, 255] {
        for depths in [0, 1, 4, 255] {
            for splits in [0, 1, 4, 255] {
                for variant in 0..3 {
                    let mut bytes = raw_ads_payload(index, depths, splits, 1);
                    if variant == 1 {
                        bytes.pop();
                    } else if variant == 2 {
                        bytes.push(0);
                    }
                    for mode in 0..3 {
                        for metadata in [0, u64::MAX - 4, u64::MAX] {
                            for work in [0, u64::MAX - 4, u64::MAX] {
                                for limit in &limits {
                                    for offset in [0, usize::MAX] {
                                        assert_decomposition_owner_case(
                                            true,
                                            &bytes,
                                            mode,
                                            limit,
                                            (metadata, work),
                                            offset,
                                        );
                                        owners += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(owners, 62_208);
    let payload = raw_ads_payload(5, 3, 5, 1);
    let mut input = ADS.to_be_bytes().to_vec();
    input.extend(u16::try_from(payload.len() + 2).unwrap().to_be_bytes());
    input.extend(&payload);
    let mut parser = new_parser(&input, &base).unwrap();
    let segment = parser.read_segment().unwrap();
    let mut extensions = Part2Extensions::default();
    parser.parse_ads(segment, &mut extensions).unwrap();
    assert_eq!(
        extensions.arbitrary_decompositions,
        vec![reference_ads_payload(&payload, 0, 0).unwrap()]
    );
    assert_eq!(
        (
            extensions.metadata_bytes,
            parser.work_units,
            parser.position
        ),
        (10, 11, input.len())
    );
}

#[test]
fn actual_raw_roi_preserves_length_component_style_and_full_shift_order() {
    fn reference(bytes: &[u8], offset: usize, components: u16) -> Result<(u16, u8), DecodeError> {
        let malformed = |kind| DecodeError::MalformedInput {
            offset: offset as u64,
            kind,
        };
        let width = if components < 257 { 1 } else { 2 };
        if bytes.len() != width + 2 {
            return Err(malformed(MalformedKind::InvalidMarkerLength));
        }
        let component = if width == 1 {
            u16::from(bytes[0])
        } else {
            u16::from_be_bytes([bytes[0], bytes[1]])
        };
        if component >= components || bytes[width] != 0 {
            return Err(malformed(MalformedKind::InvalidRegionOfInterest));
        }
        Ok((component, bytes[width + 1]))
    }
    fn payload(word: u16, components: u16, style: u8, shift: u8) -> Vec<u8> {
        let mut bytes = if components < 257 {
            vec![(word % 256) as u8]
        } else {
            word.to_be_bytes().to_vec()
        };
        bytes.extend([style, shift]);
        bytes
    }
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let mut words = 0;
    for components in [0, 1, 256, 257, u16::MAX] {
        for component in 0..=u16::MAX {
            for style in [0, 1, 255] {
                let bytes = payload(component, components, style, (component % 256) as u8);
                for offset in [0, usize::MAX] {
                    assert_eq!(
                        parser.parse_rgn(
                            Segment {
                                marker: 0x1234,
                                offset,
                                payload: &bytes
                            },
                            components
                        ),
                        reference(&bytes, offset, components)
                    );
                    words += 1;
                }
            }
        }
    }
    assert_eq!(words, 1_966_080);
    let mut shifts = 0;
    for components in [0, 1, 256, 257, u16::MAX] {
        for style in 0..=u8::MAX {
            for shift in 0..=u8::MAX {
                let bytes = payload(0, components, style, shift);
                for offset in [0, usize::MAX] {
                    assert_eq!(
                        parser.parse_rgn(
                            Segment {
                                marker: 0xff5e,
                                offset,
                                payload: &bytes
                            },
                            components
                        ),
                        reference(&bytes, offset, components)
                    );
                    shifts += 1;
                }
            }
        }
    }
    assert_eq!(shifts, 655_360);
    let mut lengths = 0;
    for components in [0, 1, 256, 257, u16::MAX] {
        for component in [0, 1, 255, 256, u16::MAX] {
            for style in [0, 1, 255] {
                for shift in [0, 255] {
                    for length in 0..=6 {
                        let mut bytes = payload(component, components, style, shift);
                        bytes.resize(length, 0);
                        for offset in [0, usize::MAX] {
                            assert_eq!(
                                parser.parse_rgn(
                                    Segment {
                                        marker: 0x1234,
                                        offset,
                                        payload: &bytes
                                    },
                                    components
                                ),
                                reference(&bytes, offset, components)
                            );
                            lengths += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(lengths, 2_100);
}

#[test]
fn actual_segment_byte_preserves_checked_index_and_error_offset() {
    let limits = ResourceLimits::HARDENED;
    let mut cases = 0;
    for length in 0..=8 {
        let bytes: Vec<u8> = (0..length)
            .map(|index| u8::try_from(index).unwrap().wrapping_mul(37))
            .collect();
        for position in [0, 1, 7, usize::MAX - 1, usize::MAX] {
            for relative in [0, 1, 3, usize::MAX] {
                for cursor in [0, 17, usize::MAX] {
                    let mut parser = new_parser(&[], &limits).unwrap();
                    parser.position = cursor;
                    for offset in [0, usize::MAX] {
                        let index = position as u128 + relative as u128;
                        let expected = if index > usize::MAX as u128 {
                            Err(DecodeError::MalformedInput {
                                offset: cursor as u64,
                                kind: MalformedKind::ArithmeticOverflow,
                            })
                        } else if index >= length as u128 {
                            Err(DecodeError::MalformedInput {
                                offset: offset as u64,
                                kind: MalformedKind::InvalidMarkerLength,
                            })
                        } else {
                            Ok(bytes[index as usize])
                        };
                        assert_eq!(
                            parser.segment_byte(
                                Segment {
                                    marker: 0x1234,
                                    offset,
                                    payload: &bytes
                                },
                                position,
                                relative
                            ),
                            expected
                        );
                        assert_eq!(parser.position, cursor);
                        assert_eq!(parser.work_units, 0);
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 1_080);
}

fn reference_mct_fixed_binary(
    negative: bool,
    significand: u128,
    binary_exponent: i32,
) -> Result<i64, ()> {
    if !(i32::MIN + 32..=i32::MAX - 32).contains(&binary_exponent) {
        return Err(());
    }
    let shift = i64::from(binary_exponent) + 32;
    let magnitude = if shift >= 0 {
        if shift >= 128 {
            return Err(());
        }
        significand.checked_mul(1_u128 << shift).ok_or(())?
    } else {
        let right = -shift;
        if right >= 128 {
            0
        } else {
            let divisor = 1_u128 << right;
            let quotient = significand / divisor;
            let remainder = significand % divisor;
            let half = divisor / 2;
            quotient
                + u128::from(remainder > half || (remainder == half && !quotient.is_multiple_of(2)))
        }
    };
    if negative {
        if magnitude > 1_u128 << 63 {
            Err(())
        } else if magnitude == 1_u128 << 63 {
            Ok(i64::MIN)
        } else {
            Ok(-(magnitude as i64))
        }
    } else {
        i64::try_from(magnitude).map_err(|_| ())
    }
}

fn reference_mct_float32(bits: u32) -> Result<i64, ()> {
    let negative = bits >= 0x80000000;
    let exponent = bits / 0x800000 % 256;
    let fraction = bits % 0x800000;
    if exponent == 255 {
        return Err(());
    }
    if exponent == 0 && fraction == 0 {
        return Ok(0);
    }
    reference_mct_fixed_binary(
        negative,
        if exponent == 0 {
            u128::from(fraction)
        } else {
            0x800000 + u128::from(fraction)
        },
        if exponent == 0 {
            -149
        } else {
            exponent as i32 - 150
        },
    )
}

fn reference_mct_float64(bits: u64) -> Result<i64, ()> {
    let negative = bits >= 0x8000000000000000;
    let exponent = bits / 0x10000000000000 % 2048;
    let fraction = bits % 0x10000000000000;
    if exponent == 2047 {
        return Err(());
    }
    if exponent == 0 && fraction == 0 {
        return Ok(0);
    }
    reference_mct_fixed_binary(
        negative,
        if exponent == 0 {
            u128::from(fraction)
        } else {
            0x10000000000000 + u128::from(fraction)
        },
        if exponent == 0 {
            -1074
        } else {
            exponent as i32 - 1075
        },
    )
}

fn reference_mct_element(
    bytes: &[u8],
    position: usize,
    format: MctNumericFormat,
    offset: usize,
) -> Result<i64, DecodeError> {
    let malformed = || DecodeError::MalformedInput {
        offset: offset as u64,
        kind: MalformedKind::InvalidTransform,
    };
    let width = match format {
        MctNumericFormat::Int16 => 2,
        MctNumericFormat::Int32 | MctNumericFormat::Float32 => 4,
        MctNumericFormat::Float64 => 8,
    };
    if position as u128 + width as u128 > bytes.len() as u128 {
        return Err(malformed());
    }
    let source = &bytes[position..position + width];
    match format {
        MctNumericFormat::Int16 => Ok(i64::from(i16::from_be_bytes(source.try_into().unwrap()))),
        MctNumericFormat::Int32 => Ok(i64::from(i32::from_be_bytes(source.try_into().unwrap()))),
        MctNumericFormat::Float32 => {
            reference_mct_float32(u32::from_be_bytes(source.try_into().unwrap()))
                .map_err(|_| malformed())
        }
        MctNumericFormat::Float64 => {
            reference_mct_float64(u64::from_be_bytes(source.try_into().unwrap()))
                .map_err(|_| malformed())
        }
    }
}

fn reference_mct_array(
    bytes: &[u8],
    limits: &ResourceLimits,
    offset: usize,
) -> Result<MctArray, DecodeError> {
    let malformed = || DecodeError::MalformedInput {
        offset: offset as u64,
        kind: MalformedKind::InvalidTransform,
    };
    if bytes.len() < 8 || bytes[..2] != [0, 0] || bytes[4..6] != [0, 0] {
        return Err(malformed());
    }
    let descriptor = u16::from_be_bytes([bytes[2], bytes[3]]);
    let index = descriptor % 256;
    if descriptor >= 4096 || index == 0 {
        return Err(malformed());
    }
    let kind = match descriptor / 256 % 4 {
        0 => MctArrayKind::Dependency,
        1 => MctArrayKind::Decorrelation,
        2 => MctArrayKind::Offset,
        _ => return Err(malformed()),
    };
    let (format, width, fraction) = match descriptor / 1024 % 4 {
        0 => (MctNumericFormat::Int16, 2, 0),
        1 => (MctNumericFormat::Int32, 4, 0),
        2 => (MctNumericFormat::Float32, 4, 32),
        _ => (MctNumericFormat::Float64, 8, 32),
    };
    let chunks = bytes[6..].chunks_exact(width);
    if !chunks.remainder().is_empty() {
        return Err(malformed());
    }
    let count = chunks.len();
    let maximum = u128::from(limits.maximum_components()).pow(2);
    if count as u128 > maximum {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::TransformElements,
            limit: maximum as u64,
            actual: count as u64,
        });
    }
    let mut values = Vec::new();
    for chunk in chunks {
        values.push(reference_mct_element(chunk, 0, format, offset)?);
    }
    Ok(MctArray {
        index: index as u8,
        kind,
        numeric_format: format,
        fraction_bits: fraction,
        values,
    })
}

fn raw_mct_array_payload(descriptor: u16, elements: &[u64]) -> Vec<u8> {
    let mut bytes = vec![0, 0];
    bytes.extend(descriptor.to_be_bytes());
    bytes.extend([0, 0]);
    let width = match descriptor / 1024 % 4 {
        0 => 2,
        1 | 2 => 4,
        _ => 8,
    };
    for element in elements {
        bytes.extend(&element.to_be_bytes()[8 - width..]);
    }
    bytes
}

fn assert_mct_array_case(parser: &Parser<'_>, bytes: &[u8], offset: usize) {
    assert_eq!(
        parser.parse_mct(Segment {
            marker: 0x1234,
            offset,
            payload: bytes
        }),
        reference_mct_array(bytes, parser.limits, offset)
    );
}

#[test]
fn actual_mct_numeric_scalars_preserve_ieee_fields_ties_underflow_and_full_word_bytes() {
    let significands = [
        0,
        1,
        2,
        3,
        4,
        5,
        (1_u128 << 23) - 1,
        1_u128 << 23,
        1_u128 << 52,
        (1_u128 << 53) - 1,
        (1_u128 << 63) - 1,
        1_u128 << 63,
        (1_u128 << 64) - 1,
        1_u128 << 64,
        (1_u128 << 127) - 1,
        1_u128 << 127,
        u128::MAX,
    ];
    let exponents = [
        i32::MIN,
        i32::MIN + 31,
        i32::MIN + 32,
        i32::MIN + 33,
        -161,
        -160,
        -159,
        -33,
        -32,
        -31,
        -1,
        0,
        1,
        31,
        32,
        63,
        64,
        95,
        96,
        97,
        i32::MAX - 33,
        i32::MAX - 32,
        i32::MAX - 31,
        i32::MAX,
    ];
    let mut binary = 0;
    for negative in [false, true] {
        for significand in significands {
            for exponent in exponents {
                assert_eq!(
                    fixed_from_binary(negative, significand, exponent),
                    reference_mct_fixed_binary(negative, significand, exponent)
                );
                binary += 1;
            }
        }
    }
    assert_eq!(binary, 816);
    let mut ties = 0;
    for right in 1..=127 {
        let divisor = 1_u128 << right;
        let half = divisor / 2;
        let quotient_limit = if right == 127 { 2 } else { 4 };
        for quotient in 0..quotient_limit {
            for remainder in [0, half - 1, half, half + 1, divisor - 1] {
                let significand = quotient * divisor + remainder;
                for negative in [false, true] {
                    assert_eq!(
                        fixed_from_binary(negative, significand, -right - 32),
                        reference_mct_fixed_binary(negative, significand, -right - 32)
                    );
                    ties += 1;
                }
            }
        }
    }
    assert_eq!(ties, 5_060);
    let mut f32_fields = 0;
    for exponent in 0_u32..256 {
        for fraction in [0, 1, 2, 0x3fffff, 0x400000, 0x7ffffe, 0x7fffff] {
            for sign in [0, 0x80000000] {
                let bits = sign + exponent * 0x800000 + fraction;
                assert_eq!(float32_to_fixed(bits), reference_mct_float32(bits));
                f32_fields += 1;
            }
        }
    }
    assert_eq!(f32_fields, 3_584);
    let mut f64_fields = 0;
    for exponent in 0_u64..2048 {
        for fraction in [
            0,
            1,
            2,
            0x7ffffffffffff,
            0x8000000000000,
            0xffffffffffffe,
            0xfffffffffffff,
        ] {
            for sign in [0, 0x8000000000000000] {
                let bits = sign + exponent * 0x10000000000000 + fraction;
                assert_eq!(float64_to_fixed(bits), reference_mct_float64(bits));
                f64_fields += 1;
            }
        }
    }
    assert_eq!(f64_fields, 28_672);
    let mut bit_patterns = 0;
    for half in 0..=u16::MAX {
        let words32 = [
            u32::from(half),
            u32::from(half) << 16,
            (u32::from(half) << 16) | 65535,
            (u32::from(half) << 16) | u32::from(half.wrapping_mul(31337)),
        ];
        let words64 = [
            u64::from(half),
            u64::from(half) << 48,
            (u64::from(half) << 48) | 0x0000ffffffffffff,
            (u64::from(half) << 48) | (u64::from(half.wrapping_mul(31337)) << 16) | u64::from(half),
        ];
        for index in 0..4 {
            assert_eq!(
                float32_to_fixed(words32[index]),
                reference_mct_float32(words32[index])
            );
            assert_eq!(
                float64_to_fixed(words64[index]),
                reference_mct_float64(words64[index])
            );
            bit_patterns += 1;
        }
        let [first, second] = half.to_be_bytes();
        let bytes = [first, second, second, first, 0x80, 0x7f, 255, 0];
        assert_eq!(read_u64(bytes), u64::from_be_bytes(bytes));
        assert_eq!(
            signed_u16(half),
            i64::from(i16::from_be_bytes(half.to_be_bytes()))
        );
    }
    assert_eq!(bit_patterns, 262_144);
    let mut byte_patterns = 0;
    for position in 0..8 {
        for value in 0..=u8::MAX {
            let mut bytes = [1, 2, 3, 4, 5, 6, 7, 8];
            bytes[position] = value;
            assert_eq!(read_u64(bytes), u64::from_be_bytes(bytes));
            byte_patterns += 1;
        }
    }
    assert_eq!(byte_patterns, 2_048);
    assert_eq!(fixed_from_binary(false, u128::MAX, -160), Ok(0));
    assert_eq!(float32_to_fixed(0x4f000000), Err(()));
    assert_eq!(float32_to_fixed(0xcf000000), Ok(i64::MIN));
    assert_eq!(float64_to_fixed(0x41e0000000000000), Err(()));
    assert_eq!(float64_to_fixed(0xc1e0000000000000), Ok(i64::MIN));
}

#[test]
fn actual_mct_arrays_preserve_all_descriptors_formats_limits_and_first_value_errors() {
    let input = [0xa5, 0x5a];
    let mut descriptors = 0;
    for descriptor in 0..=u16::MAX {
        for length in [7, 8, 14] {
            let mut bytes = vec![0; length];
            bytes[2..4].copy_from_slice(&descriptor.to_be_bytes());
            for cap in [1, 64] {
                let limits = mcc_record_test_limits(cap);
                let mut parser = new_parser(&input, &limits).unwrap();
                parser.position = usize::MAX;
                for offset in [0, usize::MAX] {
                    assert_mct_array_case(&parser, &bytes, offset);
                    descriptors += 1;
                }
            }
        }
    }
    assert_eq!(descriptors, 786_432);
    let mut arrays = 0;
    for format in 0_u16..4 {
        let special = if format == 2 {
            vec![
                0, 0x80000000, 0x3f800000, 0xbf800000, 0x4effffff, 0xcf000000,
            ]
        } else if format == 3 {
            vec![
                0,
                0x8000000000000000,
                0x3ff0000000000000,
                0xbff0000000000000,
                0x41dfffffffffffff,
                0xc1e0000000000000,
            ]
        } else {
            vec![0, 1, 0x7fff, 0x8000, 0x7fffffff, 0x80000000]
        };
        let invalid = if format == 2 {
            0x7fc00000
        } else if format == 3 {
            0x7ff8000000000000
        } else {
            u64::MAX
        };
        let vectors = [
            vec![],
            vec![0],
            special,
            vec![invalid],
            vec![0, invalid, 0],
            vec![invalid, 0, invalid],
        ];
        for kind in 0_u16..3 {
            for index in [1, 255] {
                let descriptor = index + (kind << 8) + (format << 10);
                for elements in &vectors {
                    let source = raw_mct_array_payload(descriptor, elements);
                    for cap in [0, 1, 2, 64] {
                        let limits = mcc_record_test_limits(cap)
                            .with_maximum_work_units(0)
                            .unwrap();
                        let mut parser = new_parser(&input, &limits).unwrap();
                        parser.position = usize::MAX;
                        parser.work_units = u64::MAX;
                        parser.packet_length_bytes = u64::MAX - 1;
                        parser.packet_lengths = u64::MAX - 2;
                        for variant in 0..3 {
                            let mut bytes = source.clone();
                            if variant == 0 {
                                bytes.pop();
                            } else if variant == 2 {
                                bytes.push(0);
                            }
                            for offset in [0, usize::MAX] {
                                assert_mct_array_case(&parser, &bytes, offset);
                                assert_eq!(
                                    (
                                        parser.position,
                                        parser.work_units,
                                        parser.packet_length_bytes,
                                        parser.packet_lengths
                                    ),
                                    (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2)
                                );
                                assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
                                assert!(core::ptr::eq(parser.limits, &limits));
                                arrays += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(arrays, 3_456);
    let mut limits_cases = 0;
    for format in 0_u16..4 {
        for count in [1, 2, 4, 5, 4096, 4097] {
            let source = raw_mct_array_payload(1 + 0x0100 + (format << 10), &vec![0; count]);
            for cap in [0, 1, 2, 64] {
                let limits = mcc_record_test_limits(cap);
                let parser = new_parser(&input, &limits).unwrap();
                for variant in 0..3 {
                    let mut bytes = source.clone();
                    if variant == 0 {
                        bytes.pop();
                    } else if variant == 2 {
                        bytes.push(0);
                    }
                    for offset in [0, usize::MAX] {
                        assert_mct_array_case(&parser, &bytes, offset);
                        limits_cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(limits_cases, 576);
}

#[test]
fn actual_mct_element_bounds_and_real_reader_preserve_all_array_fields() {
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&[], &limits).unwrap();
    parser.position = usize::MAX;
    let formats = [
        MctNumericFormat::Int16,
        MctNumericFormat::Int32,
        MctNumericFormat::Float32,
        MctNumericFormat::Float64,
    ];
    let mut bounds = 0;
    for format in formats {
        for position in [0, 1, 2, 8, usize::MAX - 1, usize::MAX] {
            for length in 0..=17 {
                for pattern in [0, 0x7f, 0x80, 255] {
                    let bytes = vec![pattern; length];
                    for offset in [0, usize::MAX] {
                        assert_eq!(
                            parser.decode_mct_element(&bytes, position, format, offset),
                            reference_mct_element(&bytes, position, format, offset)
                        );
                        bounds += 1;
                    }
                }
            }
        }
    }
    assert_eq!(bounds, 3_456);
    let f32_payload = raw_mct_array_payload(0x0907, &[0, 0x80000000, 0x3f800000, 0xcf000000]);
    let f64_payload = raw_mct_array_payload(0x0e09, &[0x3ff0000000000000, 0xc1e0000000000000]);
    let bad_payload = raw_mct_array_payload(0x090b, &[0x7fc00000]);
    let mut input = segment(MCT, &f32_payload);
    input.extend(segment(MCT, &f64_payload));
    let bad_offset = input.len();
    input.extend(segment(MCT, &bad_payload));
    let mut reader = new_parser(&input, &limits).unwrap();
    let raw = reader.read_segment().unwrap();
    let first = reader.parse_mct(raw).unwrap();
    assert_eq!(
        first,
        reference_mct_array(&f32_payload, &limits, 0).unwrap()
    );
    assert_eq!(first.values(), &[0, 0, 1_i64 << 32, i64::MIN]);
    let raw = reader.read_segment().unwrap();
    assert_eq!(
        reader.parse_mct(raw),
        reference_mct_array(&f64_payload, &limits, f32_payload.len() + 4)
    );
    let raw = reader.read_segment().unwrap();
    assert_eq!(
        reader.parse_mct(raw),
        Err(DecodeError::MalformedInput {
            offset: bad_offset as u64,
            kind: MalformedKind::InvalidTransform,
        })
    );
    assert_eq!((reader.position, reader.work_units), (input.len(), 3));
    assert!(core::ptr::eq(reader.input.as_ptr(), input.as_ptr()));
}

#[derive(Clone)]
struct PackedProducerCase<'a> {
    payload: &'a [u8],
    marker: u16,
    expected_marker: u16,
    offset: usize,
    position: usize,
    work: u64,
    header_bytes: u64,
    packet_count: u64,
    next: u16,
    fragments: u16,
    bytes: Vec<u8>,
}

fn raw_packed_producer_case(payload: &[u8], next: u16, fragments: u16) -> PackedProducerCase<'_> {
    PackedProducerCase {
        payload,
        marker: PPM,
        expected_marker: PPM,
        offset: usize::MAX,
        position: 13,
        work: 0,
        header_bytes: 0,
        packet_count: u64::MAX,
        next,
        fragments,
        bytes: vec![0xde, 0, 0xff],
    }
}

fn reference_packed_producer(
    limits: &ResourceLimits,
    case: &mut PackedProducerCase<'_>,
) -> Result<(), DecodeError> {
    let malformed = |offset, kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    if case.marker != case.expected_marker || case.payload.is_empty() {
        return Err(malformed(case.offset, MalformedKind::InvalidMarkerLength));
    }
    if u16::from(case.payload[0]) != case.next {
        return Err(malformed(case.offset, MalformedKind::InvalidMarkerOrder));
    }
    case.next += 1;
    if case.fragments == u16::MAX {
        return Err(malformed(case.offset, MalformedKind::ArithmeticOverflow));
    }
    case.fragments += 1;
    let fragment = &case.payload[1..];
    let length = case.bytes.len() as u128 + fragment.len() as u128;
    if length > usize::MAX as u128 {
        return Err(malformed(case.offset, MalformedKind::ArithmeticOverflow));
    }
    let total = u128::from(case.header_bytes) + fragment.len() as u128;
    if total > u128::from(u64::MAX) {
        return Err(malformed(case.offset, MalformedKind::ArithmeticOverflow));
    }
    if total > u128::from(limits.maximum_packet_header_bytes()) {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::PacketHeaderBytes,
            limit: limits.maximum_packet_header_bytes(),
            actual: total as u64,
        });
    }
    case.header_bytes = total as u64;
    let work = u128::from(case.work) + fragment.len() as u128;
    if work > u128::from(u64::MAX) {
        return Err(malformed(case.position, MalformedKind::ArithmeticOverflow));
    }
    case.work = work as u64;
    if case.work > limits.maximum_work_units() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: case.work,
        });
    }
    case.bytes = [case.bytes.as_slice(), fragment].concat();
    Ok(())
}

fn assert_packed_producer_case(limits: &ResourceLimits, case: PackedProducerCase<'_>) {
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, limits).unwrap();
    parser.position = case.position;
    parser.work_units = case.work;
    parser.packet_length_bytes = case.header_bytes;
    parser.packet_lengths = case.packet_count;
    let mut next = case.next;
    let mut fragments = case.fragments;
    let mut bytes = case.bytes.clone();
    let mut expected = case.clone();
    let expected_result = reference_packed_producer(limits, &mut expected);
    assert_eq!(
        parser.parse_packed_fragment(
            Segment {
                marker: case.marker,
                offset: case.offset,
                payload: case.payload,
            },
            case.expected_marker,
            &mut next,
            &mut fragments,
            &mut bytes,
        ),
        expected_result
    );
    assert_eq!(
        (next, fragments, bytes),
        (expected.next, expected.fragments, expected.bytes)
    );
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (
            expected.position,
            expected.work,
            expected.header_bytes,
            expected.packet_count
        )
    );
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, limits));
}

fn reference_ppm_producer(
    bytes: &[u8],
    fragments: u16,
    limits: &ResourceLimits,
) -> Result<Vec<(usize, usize)>, DecodeError> {
    if fragments == 0 {
        return Ok(Vec::new());
    }
    let malformed = |offset, kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    let mut position = 0_usize;
    let mut frames = Vec::new();
    while position < bytes.len() {
        if bytes.len() - position < 4 {
            return Err(malformed(
                position,
                MalformedKind::InvalidPackedPacketHeader,
            ));
        }
        let length = u32::from_be_bytes(bytes[position..position + 4].try_into().unwrap());
        if u128::from(length) > usize::MAX as u128 {
            return Err(malformed(position, MalformedKind::ArithmeticOverflow));
        }
        let start = position as u128 + 4;
        let end = start + u128::from(length);
        if start > usize::MAX as u128 {
            return Err(malformed(position, MalformedKind::ArithmeticOverflow));
        }
        if end > usize::MAX as u128 {
            return Err(malformed(start as usize, MalformedKind::ArithmeticOverflow));
        }
        if end > bytes.len() as u128 {
            return Err(malformed(
                start as usize,
                MalformedKind::InvalidPackedPacketHeader,
            ));
        }
        frames.push((start as usize, length as usize));
        if frames.len() as u64 > u64::from(limits.maximum_tile_parts()) {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TileParts,
                limit: u64::from(limits.maximum_tile_parts()),
                actual: frames.len() as u64,
            });
        }
        position = end as usize;
    }
    Ok(frames)
}

fn assert_ppm_producer_case(parser: &Parser<'_>, bytes: &[u8], fragments: u16) {
    let actual = parser.parse_ppm_frames(bytes, fragments).map(|frames| {
        frames
            .into_iter()
            .map(|frame| (frame.start, frame.length))
            .collect::<Vec<_>>()
    });
    assert_eq!(
        actual,
        reference_ppm_producer(bytes, fragments, parser.limits)
    );
}

#[derive(Clone, Copy)]
struct PltProducerCase<'a> {
    payload: &'a [u8],
    main: PacketLengths<'a>,
    offset: usize,
    next: u16,
    seen: bool,
    count: u64,
    bytes: u64,
    total: u64,
    state: PacketAdmissionState,
}

fn raw_plt_producer_case(payload: &[u8], next: u16) -> PltProducerCase<'_> {
    PltProducerCase {
        payload,
        main: PacketLengths {
            source: PacketLengthSource::None,
            packet_count: u64::MAX,
            encoded_bytes: u64::MAX,
        },
        offset: usize::MAX,
        next,
        seen: false,
        count: 0,
        bytes: 0,
        total: 0,
        state: raw_packet_admission_state(),
    }
}

fn reference_plt_producer(
    limits: &ResourceLimits,
    case: &mut PltProducerCase<'_>,
) -> Result<(), DecodeError> {
    if case.main.source != PacketLengthSource::None {
        return Err(input_error_literal(
            case.offset,
            MalformedKind::InvalidMarkerOrder,
        ));
    }
    let Some(index) = case.payload.first() else {
        return Err(input_error_literal(
            case.offset,
            MalformedKind::InvalidMarkerLength,
        ));
    };
    if u16::from(*index) != case.next {
        return Err(input_error_literal(
            case.offset,
            MalformedKind::InvalidMarkerOrder,
        ));
    }
    case.next += 1;
    let encoded = &case.payload[1..];
    let (count, total) = reference_packet_admission(limits, &mut case.state, encoded, case.offset)?;
    case.seen = true;
    let packets = u128::from(case.count) + u128::from(count);
    if packets > u128::from(u64::MAX) {
        return Err(input_error_literal(
            case.offset,
            MalformedKind::ArithmeticOverflow,
        ));
    }
    case.count = packets as u64;
    let bytes = u128::from(case.bytes) + encoded.len() as u128;
    if bytes > u128::from(u64::MAX) {
        return Err(input_error_literal(
            case.offset,
            MalformedKind::ArithmeticOverflow,
        ));
    }
    case.bytes = bytes as u64;
    let payload = u128::from(case.total) + u128::from(total);
    if payload > u128::from(u64::MAX) {
        return Err(input_error_literal(
            case.offset,
            MalformedKind::ArithmeticOverflow,
        ));
    }
    case.total = payload as u64;
    Ok(())
}

fn assert_plt_producer_case(limits: &ResourceLimits, case: PltProducerCase<'_>) {
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, limits).unwrap();
    set_packet_admission_state(&mut parser, case.state);
    let mut expected = case;
    let result = reference_plt_producer(limits, &mut expected);
    let (mut next, mut seen, mut count, mut bytes, mut total) =
        (case.next, case.seen, case.count, case.bytes, case.total);
    assert_eq!(
        parser.parse_plt(
            Segment {
                marker: PPM,
                offset: case.offset,
                payload: case.payload
            },
            case.main,
            &mut next,
            &mut seen,
            &mut count,
            &mut bytes,
            &mut total,
        ),
        result
    );
    assert_eq!(
        (next, seen, count, bytes, total),
        (
            expected.next,
            expected.seen,
            expected.count,
            expected.bytes,
            expected.total
        )
    );
    assert_packet_admission_state(&parser, expected.state, &input, limits);
}

fn assert_ppt_producer_case(
    limits: &ResourceLimits,
    main: PackedPacketHeaders<'_>,
    mut case: PackedProducerCase<'_>,
) {
    case.expected_marker = PPT;
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, limits).unwrap();
    set_packet_admission_state(
        &mut parser,
        PacketAdmissionState {
            position: case.position,
            work: case.work,
            header_bytes: case.header_bytes,
            packet_count: case.packet_count,
        },
    );
    let (mut next, mut fragments, mut bytes) = (case.next, case.fragments, case.bytes.clone());
    let mut expected = case.clone();
    let result = if main.source == PackedPacketHeaderSource::None {
        reference_packed_producer(limits, &mut expected)
    } else {
        Err(input_error_literal(
            case.offset,
            MalformedKind::InvalidMarkerOrder,
        ))
    };
    assert_eq!(
        parser.parse_ppt(
            Segment {
                marker: case.marker,
                offset: case.offset,
                payload: case.payload
            },
            main,
            &mut next,
            &mut fragments,
            &mut bytes,
        ),
        result
    );
    assert_eq!(
        (next, fragments, bytes),
        (expected.next, expected.fragments, expected.bytes)
    );
    assert_packet_admission_state(
        &parser,
        PacketAdmissionState {
            position: expected.position,
            work: expected.work,
            header_bytes: expected.header_bytes,
            packet_count: expected.packet_count,
        },
        &input,
        limits,
    );
}

#[test]
fn actual_plt_admission_preserves_raw_main_precedence_all_indexes_and_short_varints() {
    let limits = ResourceLimits::HARDENED;
    let mains = [
        PacketLengths {
            source: PacketLengthSource::None,
            packet_count: u64::MAX,
            encoded_bytes: u64::MAX,
        },
        PacketLengths {
            source: PacketLengthSource::Plm(&[]),
            packet_count: 0,
            encoded_bytes: 0,
        },
        PacketLengths {
            source: PacketLengthSource::Plt(&[0]),
            packet_count: u64::MAX,
            encoded_bytes: u64::MAX,
        },
    ];
    let mut contexts = 0;
    for index in 0..=u8::MAX {
        for encoded in [&[][..], &[1], &[0], &[0x81, 0], &[0x80]] {
            let mut payload = vec![index];
            payload.extend(encoded);
            for next in [0, 1, 254, 255, 256, u16::MAX] {
                for main in mains {
                    for seen in [false, true] {
                        let mut case = raw_plt_producer_case(&payload, next);
                        case.main = main;
                        case.seen = seen;
                        assert_plt_producer_case(&limits, case);
                        contexts += 1;
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 46_080);
    let mut raw_indexes = 0;
    for next in 0..=u16::MAX {
        for payload in [&[][..], &[0], &[255], &[next as u8]] {
            for main in mains {
                let mut case = raw_plt_producer_case(payload, next);
                case.main = main;
                assert_plt_producer_case(&limits, case);
                raw_indexes += 1;
            }
        }
    }
    assert_eq!(raw_indexes, 786_432);
    let mut words = 0;
    for word in 0..=u16::MAX {
        for index in [0, 255] {
            let mut payload = vec![index];
            payload.extend(word.to_be_bytes());
            assert_plt_producer_case(&limits, raw_plt_producer_case(&payload, u16::from(index)));
            words += 1;
        }
    }
    assert_eq!(words, 131_072);
}

#[test]
fn actual_plt_admission_preserves_reader_charges_seen_and_sequential_counter_commits() {
    let mut contexts = 0;
    for (header_cap, work_cap, packet_cap) in
        [(0, 8, 8), (8, 0, 8), (8, 8, 0), (8, 8, 8), (32, 32, 32)]
    {
        let limits = ResourceLimits::HARDENED
            .with_maximum_packet_header_bytes(header_cap)
            .unwrap()
            .with_maximum_work_units(work_cap)
            .unwrap()
            .with_maximum_packets(packet_cap)
            .unwrap();
        let mut states = [raw_packet_admission_state(); 5];
        states[1].work = u64::MAX;
        states[2].header_bytes = u64::MAX;
        states[3].packet_count = u64::MAX;
        states[4].work = u64::MAX - 1;
        states[4].header_bytes = u64::MAX - 1;
        states[4].packet_count = u64::MAX - 1;
        for encoded in [
            &[][..],
            &[1],
            &[0],
            &[1, 2],
            &[0x8f, 0xff, 0xff, 0xff, 0x7f],
        ] {
            for index in [0, 255] {
                let mut payload = vec![index];
                payload.extend(encoded);
                for state in states {
                    for count in [0, u64::MAX - 1, u64::MAX] {
                        for bytes in [0, u64::MAX - 1, u64::MAX] {
                            for total in [0, u64::MAX - 3, u64::MAX] {
                                for seen in [false, true] {
                                    let mut case =
                                        raw_plt_producer_case(&payload, u16::from(index));
                                    case.state = state;
                                    case.count = count;
                                    case.bytes = bytes;
                                    case.total = total;
                                    case.seen = seen;
                                    assert_plt_producer_case(&limits, case);
                                    contexts += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 13_500);
}

#[test]
fn actual_ppt_admission_preserves_main_conflicts_before_all_fragment_errors_and_frames() {
    let mains = [
        PackedPacketHeaders {
            source: PackedPacketHeaderSource::None,
            length: usize::MAX,
            fragments: u16::MAX,
        },
        PackedPacketHeaders {
            source: PackedPacketHeaderSource::MarkerSegments {
                header: &[],
                marker: 0,
                logical_start: usize::MAX,
            },
            length: 0,
            fragments: 0,
        },
        PackedPacketHeaders {
            source: PackedPacketHeaderSource::MarkerSegments {
                header: &[0xff],
                marker: PPM,
                logical_start: 1,
            },
            length: usize::MAX,
            fragments: u16::MAX,
        },
    ];
    let limits = ResourceLimits::HARDENED;
    let mut contexts = 0;
    for index in 0..=u8::MAX {
        for length in [0, 1, 3] {
            let mut payload = vec![index];
            payload.extend(vec![0xa5; length]);
            for main in mains {
                for next in [0, 1, 254, 255, 256, u16::MAX] {
                    for fragments in [0, u16::MAX] {
                        for marker in [PPM, PPT] {
                            let mut case = raw_packed_producer_case(&payload, next, fragments);
                            case.marker = marker;
                            assert_ppt_producer_case(&limits, main, case);
                            contexts += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 55_296);
    let mut raw_indexes = 0;
    for next in 0..=u16::MAX {
        for payload in [&[][..], &[0], &[255], &[next as u8]] {
            for main in mains {
                let mut case = raw_packed_producer_case(payload, next, 0);
                case.marker = PPT;
                assert_ppt_producer_case(&limits, main, case);
                raw_indexes += 1;
            }
        }
    }
    assert_eq!(raw_indexes, 786_432);
    let mut charges = 0;
    for (header_cap, work_cap) in [(0, 8), (8, 0), (8, 8)] {
        let limits = ResourceLimits::HARDENED
            .with_maximum_packet_header_bytes(header_cap)
            .unwrap()
            .with_maximum_work_units(work_cap)
            .unwrap();
        for main in mains {
            for work in [0, u64::MAX] {
                for header_bytes in [0, u64::MAX] {
                    for fragments in [0, u16::MAX] {
                        let mut case = raw_packed_producer_case(&[0, 0xaa], 0, fragments);
                        case.marker = PPT;
                        case.work = work;
                        case.header_bytes = header_bytes;
                        assert_ppt_producer_case(&limits, main, case);
                        charges += 1;
                    }
                }
            }
        }
    }
    assert_eq!(charges, 72);
}

#[test]
fn actual_tile_packet_admission_joins_segment_reader_producers_and_final_metadata() {
    let mut input = segment(PLT, &[0, 3]);
    input.extend(segment(PPT, &[0, 0xab]));
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let raw = parser.read_segment().unwrap();
    let main = PacketLengths {
        source: PacketLengthSource::None,
        packet_count: u64::MAX,
        encoded_bytes: u64::MAX,
    };
    let (mut next_plt, mut seen, mut count, mut encoded, mut total) = (0, false, 0, 0, 0);
    parser
        .parse_plt(
            raw,
            main,
            &mut next_plt,
            &mut seen,
            &mut count,
            &mut encoded,
            &mut total,
        )
        .unwrap();
    let raw = parser.read_segment().unwrap();
    let (mut next_ppt, mut fragments, mut bytes) = (0, 0, Vec::new());
    parser
        .parse_ppt(
            raw,
            PackedPacketHeaders {
                source: PackedPacketHeaderSource::None,
                length: usize::MAX,
                fragments: u16::MAX,
            },
            &mut next_ppt,
            &mut fragments,
            &mut bytes,
        )
        .unwrap();
    let end = parser.position;
    let packed = parser
        .finish_packed_packet_headers(
            0,
            end,
            PackedPacketHeaders::none(),
            fragments,
            bytes.len(),
            17,
        )
        .unwrap();
    let lengths = parser
        .finish_packet_lengths(
            0,
            end,
            main,
            seen,
            count,
            encoded,
            total,
            2,
            packed.length,
            17,
        )
        .unwrap();
    assert_eq!((next_plt, seen, count, encoded, total), (1, true, 1, 1, 3));
    assert_eq!((next_ppt, fragments, bytes), (1, 1, vec![0xab]));
    assert_eq!((lengths.packet_count, lengths.encoded_bytes), (1, 1));
    assert_eq!(lengths.source, PacketLengthSource::Plt(&input[..end]));
    assert_eq!((packed.length, packed.fragments), (1, 1));
    assert_eq!(
        packed.source,
        PackedPacketHeaderSource::MarkerSegments {
            header: &input[..end],
            marker: PPT,
            logical_start: 0,
        }
    );
    if let PacketLengthSource::Plt(header) = lengths.source {
        assert!(core::ptr::eq(header.as_ptr(), input.as_ptr()));
    } else {
        panic!("PLT source was not retained");
    }
    if let PackedPacketHeaderSource::MarkerSegments { header, .. } = packed.source {
        assert!(core::ptr::eq(header.as_ptr(), input.as_ptr()));
    } else {
        panic!("PPT source was not retained");
    }
    assert_packet_admission_state(
        &parser,
        PacketAdmissionState {
            position: input.len(),
            work: 4,
            header_bytes: 2,
            packet_count: 1,
        },
        &input,
        &limits,
    );
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PacketAdmissionState {
    position: usize,
    work: u64,
    header_bytes: u64,
    packet_count: u64,
}

fn raw_packet_admission_state() -> PacketAdmissionState {
    PacketAdmissionState {
        position: 17,
        work: 0,
        header_bytes: 0,
        packet_count: 0,
    }
}

fn reference_sot_reader(
    input: &[u8],
    limits: &ResourceLimits,
    state: &mut PacketAdmissionState,
    tile_count: u64,
) -> Result<(usize, u32, u16, u8, u8), DecodeError> {
    let offset = state.position;
    let malformed = |kind| input_error_literal(offset, kind);
    let start = offset as u128;
    if start + 2 > input.len() as u128 {
        return Err(malformed(MalformedKind::Truncated));
    }
    let word = u16::from_be_bytes([input[offset], input[offset + 1]]);
    if input[offset] != 255 || matches!(input[offset + 1], 0 | 255) {
        return Err(malformed(MalformedKind::InvalidMarker));
    }
    let work = u128::from(state.work) + 1;
    if work > u128::from(u64::MAX) {
        return Err(malformed(MalformedKind::ArithmeticOverflow));
    }
    state.work = work as u64;
    if state.work > limits.maximum_work_units() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: state.work,
        });
    }
    if [0xff4f, 0xff93, 0xffd9, 0xff92].contains(&word) {
        return Err(malformed(MalformedKind::InvalidMarkerOrder));
    }
    if start + 4 > input.len() as u128 {
        return Err(malformed(MalformedKind::Truncated));
    }
    let length = u16::from_be_bytes([input[offset + 2], input[offset + 3]]) as u128;
    if length < 2 {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    let end = start + 2 + length;
    if end > usize::MAX as u128 {
        return Err(malformed(MalformedKind::ArithmeticOverflow));
    }
    if end > input.len() as u128 {
        return Err(malformed(MalformedKind::Truncated));
    }
    state.position = end as usize;
    let payload = &input[offset + 4..end as usize];
    if word != 0xff90 || payload.len() != 8 {
        return Err(malformed(MalformedKind::InvalidTilePart));
    }
    let tile = u16::from_be_bytes(payload[..2].try_into().unwrap());
    let bytes = u32::from_be_bytes(payload[2..6].try_into().unwrap());
    let (part, count) = (payload[6], payload[7]);
    if u64::from(tile) >= tile_count || (count > 0 && part >= count) || (bytes > 0 && bytes < 14) {
        return Err(malformed(MalformedKind::InvalidTilePart));
    }
    Ok((offset, bytes, tile, part, count))
}

fn assert_sot_reader_case(
    input: &[u8],
    limits: &ResourceLimits,
    state: PacketAdmissionState,
    tile_count: u64,
) {
    let mut parser = Parser {
        input,
        limits,
        position: state.position,
        work_units: state.work,
        packet_length_bytes: state.header_bytes,
        packet_lengths: state.packet_count,
    };
    let mut expected = state;
    let result = reference_sot_reader(input, limits, &mut expected, tile_count);
    assert_eq!(
        parser.read_sot(tile_count).map(|header| (
            header.start,
            header.length,
            header.tile_index,
            header.tile_part_index,
            header.tile_part_count,
        )),
        result
    );
    assert_packet_admission_state(&parser, expected, input, limits);
}

#[test]
fn actual_marker_admission_matches_independent_complete_u16_policy_sets() {
    let known = [
        0xff50, 0xff51, 0xff52, 0xff53, 0xff55, 0xff56, 0xff57, 0xff58, 0xff59, 0xff5c, 0xff5d,
        0xff5e, 0xff5f, 0xff60, 0xff61, 0xff63, 0xff64, 0xff72, 0xff73, 0xff74, 0xff75, 0xff76,
        0xff77, 0xff78, 0xff79, 0xff90,
    ];
    let main = [
        0xff50, 0xff52, 0xff53, 0xff55, 0xff56, 0xff57, 0xff59, 0xff5c, 0xff5d, 0xff5e, 0xff5f,
        0xff60, 0xff63, 0xff64, 0xff72, 0xff73, 0xff74, 0xff75, 0xff76, 0xff77, 0xff78, 0xff79,
    ];
    let tile = [
        0xff52, 0xff53, 0xff58, 0xff5c, 0xff5d, 0xff5e, 0xff5f, 0xff61, 0xff64, 0xff72, 0xff73,
        0xff74, 0xff75, 0xff76, 0xff77, 0xff78, 0xff79,
    ];
    for marker in 0..=u16::MAX {
        assert_eq!(is_known_segment_marker(marker), known.contains(&marker));
        assert_eq!(is_allowed_main_header(marker), main.contains(&marker));
        assert_eq!(is_allowed_tile_header(marker), tile.contains(&marker));
    }
}

#[test]
fn actual_sot_reader_preserves_all_marker_words_and_original_reader_errors() {
    let limits = ResourceLimits::HARDENED;
    let mut contexts = 0;
    for marker in 0..=u16::MAX {
        let input = segment(marker, &[0, 0, 0, 0, 0, 14, 0, 1]);
        for work in [0, u64::MAX] {
            assert_sot_reader_case(
                &input,
                &limits,
                PacketAdmissionState {
                    position: 0,
                    work,
                    header_bytes: u64::MAX,
                    packet_count: u64::MAX,
                },
                1,
            );
            contexts += 1;
        }
    }
    assert_eq!(contexts, 131_072);
}

#[test]
fn actual_sot_reader_derives_every_tile_index_and_exact_tile_count_boundary() {
    let limits = ResourceLimits::HARDENED;
    let mut contexts = 0;
    for index in 0..=u16::MAX {
        let mut payload = index.to_be_bytes().to_vec();
        payload.extend([0, 0, 0, 14, 0, 1]);
        let input = segment(SOT, &payload);
        for count in [
            0,
            1,
            u64::from(index),
            u64::from(index) + 1,
            65_535,
            65_536,
            u64::MAX,
        ] {
            let mut state = raw_packet_admission_state();
            state.position = 0;
            assert_sot_reader_case(&input, &limits, state, count);
            contexts += 1;
        }
    }
    assert_eq!(contexts, 458_752);
}

#[test]
fn actual_sot_reader_preserves_zero_count_length_bypasses_and_all_part_indexes() {
    let limits = ResourceLimits::HARDENED;
    let mut contexts = 0;
    for part in 0..=u8::MAX {
        for count in 0..=u8::MAX {
            for length in [0_u32, 1, 13, 14, 15, 65_535, 65_536, u32::MAX] {
                let mut payload = vec![0, 0];
                payload.extend(length.to_be_bytes());
                payload.extend([part, count]);
                let input = segment(SOT, &payload);
                let mut state = raw_packet_admission_state();
                state.position = 0;
                assert_sot_reader_case(&input, &limits, state, 1);
                contexts += 1;
            }
        }
    }
    assert_eq!(contexts, 524_288);
}

#[test]
fn actual_sot_reader_preserves_truncations_work_error_order_full_frames_and_real_sequence() {
    let input = segment(SOT, &[0, 0, 0, 0, 0, 14, 0, 1]);
    let mut contexts = 0;
    for end in 0..=input.len() {
        for position in [0, 1, 2, 12, 13, usize::MAX] {
            for work in [0, 1, u64::MAX - 1, u64::MAX] {
                for cap in [0, 1, 2, ResourceLimits::HARDENED.maximum_work_units()] {
                    let limits = ResourceLimits::HARDENED
                        .with_maximum_work_units(cap)
                        .unwrap();
                    for header_bytes in [0, u64::MAX] {
                        for packet_count in [0, u64::MAX] {
                            assert_sot_reader_case(
                                &input[..end],
                                &limits,
                                PacketAdmissionState {
                                    position,
                                    work,
                                    header_bytes,
                                    packet_count,
                                },
                                u64::MAX,
                            );
                            contexts += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 4_992);
    for length in [0_u16, 1, 2, 9, 10, 11, u16::MAX] {
        let mut bytes = input.clone();
        bytes[2..4].copy_from_slice(&length.to_be_bytes());
        let mut state = raw_packet_admission_state();
        state.position = 0;
        assert_sot_reader_case(&bytes, &ResourceLimits::HARDENED, state, 1);
    }
    for payload_len in (0..=16).chain([255, 65_533]) {
        let bytes = segment(SOT, &vec![0; payload_len]);
        let mut state = raw_packet_admission_state();
        state.position = 0;
        assert_sot_reader_case(&bytes, &ResourceLimits::HARDENED, state, 1);
    }
    let limits = ResourceLimits::HARDENED;
    let mut sequence = vec![0x11, 0x22, 0x33];
    sequence.extend(&input);
    sequence.extend(segment(COM, &[0, 1, b'x']));
    sequence.extend(SOD.to_be_bytes());
    sequence.extend(segment(SOT, &[0, 1, 0, 0, 0, 0, u8::MAX, 0]));
    let mut parser = new_parser(&sequence, &limits).unwrap();
    parser.position = 3;
    assert_eq!(
        parser.read_sot(2).unwrap(),
        TilePart {
            start: 3,
            length: 14,
            tile_index: 0,
            tile_part_index: 0,
            tile_part_count: 1,
        }
    );
    let comment = parser.read_segment().unwrap();
    assert_eq!(
        (comment.marker, comment.offset, comment.payload),
        (COM, 15, &[0, 1, b'x'][..])
    );
    assert!(is_allowed_tile_header(comment.marker));
    parser.expect_standalone(SOD).unwrap();
    assert_eq!(
        parser.read_sot(2).unwrap(),
        TilePart {
            start: 24,
            length: 0,
            tile_index: 1,
            tile_part_index: u8::MAX,
            tile_part_count: 0,
        }
    );
    assert_packet_admission_state(
        &parser,
        PacketAdmissionState {
            position: sequence.len(),
            work: 4,
            header_bytes: 0,
            packet_count: 0,
        },
        &sequence,
        &limits,
    );
    let data = [1, 2, 3];
    let bytes = codestream_with_headers(
        1,
        &baseline_headers(),
        &[segment(COM, &[0, 1, b'x'])],
        &data,
    );
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(layout.tile_parts.len(), 1);
    let tile = &layout.tile_parts[0];
    assert_eq!(
        (
            tile.tile_index,
            tile.tile_part_index,
            tile.tile_part_count,
            tile.data
        ),
        (0, 0, 1, &data[..])
    );
    assert!(
        bytes
            .windows(tile.data.len())
            .any(|window| core::ptr::eq(window.as_ptr(), tile.data.as_ptr()))
    );
}

fn reference_packet_admission(
    limits: &ResourceLimits,
    state: &mut PacketAdmissionState,
    encoded: &[u8],
    offset: usize,
) -> Result<(u64, u64), DecodeError> {
    let malformed = |position, kind| DecodeError::MalformedInput {
        offset: position as u64,
        kind,
    };
    let bytes = u128::from(state.header_bytes) + encoded.len() as u128;
    if bytes > u128::from(u64::MAX) {
        return Err(malformed(offset, MalformedKind::ArithmeticOverflow));
    }
    state.header_bytes = bytes as u64;
    if state.header_bytes > limits.maximum_packet_header_bytes() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::PacketHeaderBytes,
            limit: limits.maximum_packet_header_bytes(),
            actual: state.header_bytes,
        });
    }
    let work = u128::from(state.work) + encoded.len() as u128;
    if work > u128::from(u64::MAX) {
        return Err(malformed(state.position, MalformedKind::ArithmeticOverflow));
    }
    state.work = work as u64;
    if state.work > limits.maximum_work_units() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: state.work,
        });
    }
    let mut values = Vec::new();
    let mut position = 0;
    while position < encoded.len() {
        let (value, next) = packet_length_wide_window(encoded, position, encoded.len())
            .map_err(|_| malformed(offset, MalformedKind::InvalidPacketLength))?;
        values.push(value);
        position = next;
    }
    let count = values.len() as u128;
    let total: u128 = values.into_iter().map(u128::from).sum();
    let packets = u128::from(state.packet_count) + count;
    if count > u128::from(u64::MAX)
        || total > u128::from(u64::MAX)
        || packets > u128::from(u64::MAX)
    {
        return Err(malformed(offset, MalformedKind::ArithmeticOverflow));
    }
    state.packet_count = packets as u64;
    if state.packet_count > limits.maximum_packets() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: limits.maximum_packets(),
            actual: state.packet_count,
        });
    }
    Ok((count as u64, total as u64))
}

fn set_packet_admission_state(parser: &mut Parser<'_>, state: PacketAdmissionState) {
    parser.position = state.position;
    parser.work_units = state.work;
    parser.packet_length_bytes = state.header_bytes;
    parser.packet_lengths = state.packet_count;
}

fn assert_packet_admission_state(
    parser: &Parser<'_>,
    expected: PacketAdmissionState,
    input: &[u8],
    limits: &ResourceLimits,
) {
    assert_eq!(
        PacketAdmissionState {
            position: parser.position,
            work: parser.work_units,
            header_bytes: parser.packet_length_bytes,
            packet_count: parser.packet_lengths,
        },
        expected
    );
    assert_eq!(parser.input, input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, limits));
}

fn assert_packet_admission_case(
    limits: &ResourceLimits,
    state: PacketAdmissionState,
    encoded: &[u8],
    offset: usize,
) {
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, limits).unwrap();
    set_packet_admission_state(&mut parser, state);
    let mut expected = state;
    let result = reference_packet_admission(limits, &mut expected, encoded, offset);
    assert_eq!(parser.validate_packet_lengths(encoded, offset), result);
    assert_packet_admission_state(&parser, expected, &input, limits);
}

#[derive(Clone)]
struct PlmProducerCase<'a> {
    payload: &'a [u8],
    marker: u16,
    offset: usize,
    next: u16,
    groups: Vec<PacketLengths<'a>>,
    state: PacketAdmissionState,
}

fn raw_plm_producer_case(payload: &[u8], next: u16) -> PlmProducerCase<'_> {
    PlmProducerCase {
        payload,
        marker: PLM,
        offset: usize::MAX,
        next,
        groups: vec![
            PacketLengths {
                source: PacketLengthSource::None,
                packet_count: u64::MAX,
                encoded_bytes: 19,
            },
            PacketLengths {
                source: PacketLengthSource::Plt(&[0, 0xff]),
                packet_count: 7,
                encoded_bytes: u64::MAX,
            },
        ],
        state: raw_packet_admission_state(),
    }
}

fn reference_plm_producer(
    limits: &ResourceLimits,
    case: &mut PlmProducerCase<'_>,
) -> Result<(), DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: case.offset as u64,
        kind,
    };
    if case.payload.len() < 5 {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    if u16::from(case.payload[0]) != case.next {
        return Err(malformed(MalformedKind::InvalidMarkerOrder));
    }
    case.next += 1;
    let mut remaining = &case.payload[1..];
    while !remaining.is_empty() {
        if remaining.len() < 4 {
            return Err(malformed(MalformedKind::InvalidMarkerLength));
        }
        let length = u32::from_be_bytes(remaining[..4].try_into().unwrap()) as u128;
        let start = case.payload.len() as u128 - remaining.len() as u128 + 4;
        if length > usize::MAX as u128 || start + length > usize::MAX as u128 {
            return Err(malformed(MalformedKind::ArithmeticOverflow));
        }
        remaining = &remaining[4..];
        if length > remaining.len() as u128 {
            return Err(malformed(MalformedKind::InvalidMarkerLength));
        }
        let (encoded, tail) = remaining.split_at(length as usize);
        let (packet_count, _) =
            reference_packet_admission(limits, &mut case.state, encoded, case.offset)?;
        case.groups.push(PacketLengths {
            source: PacketLengthSource::Plm(encoded),
            packet_count,
            encoded_bytes: length as u64,
        });
        if case.groups.len() as u64 > u64::from(limits.maximum_tile_parts()) {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TileParts,
                limit: u64::from(limits.maximum_tile_parts()),
                actual: case.groups.len() as u64,
            });
        }
        remaining = tail;
    }
    Ok(())
}

fn assert_plm_producer_case(limits: &ResourceLimits, case: PlmProducerCase<'_>) {
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, limits).unwrap();
    set_packet_admission_state(&mut parser, case.state);
    let mut next = case.next;
    let mut groups = case.groups.clone();
    let mut expected = case.clone();
    let result = reference_plm_producer(limits, &mut expected);
    assert_eq!(
        parser.parse_plm(
            Segment {
                marker: case.marker,
                offset: case.offset,
                payload: case.payload,
            },
            &mut next,
            &mut groups,
        ),
        result
    );
    assert_eq!(next, expected.next);
    assert_eq!(groups, expected.groups);
    for (actual, expected) in groups.iter().zip(&expected.groups) {
        if let (PacketLengthSource::Plm(actual), PacketLengthSource::Plm(expected)) =
            (actual.source, expected.source)
        {
            assert!(core::ptr::eq(actual.as_ptr(), expected.as_ptr()));
        }
    }
    assert_packet_admission_state(&parser, expected.state, &input, limits);
}

pub(super) fn reference_packet_sum(source: PacketLengthSource<'_>) -> Result<u64, DecodeError> {
    let bytes = match source {
        PacketLengthSource::None => return Ok(0),
        PacketLengthSource::Plt(_) => {
            return Err(input_error_literal(0, MalformedKind::InvalidPacketLength));
        }
        PacketLengthSource::Plm(bytes) => bytes,
    };
    let mut position = 0;
    let mut values = Vec::new();
    while position < bytes.len() {
        let (value, next) = packet_length_wide_window(bytes, position, bytes.len())?;
        values.push(value);
        position = next;
    }
    let total: u128 = values.into_iter().map(u128::from).sum();
    if total > u128::from(u64::MAX) {
        Err(input_error_literal(0, MalformedKind::ArithmeticOverflow))
    } else {
        Ok(total as u64)
    }
}

#[derive(Clone, Copy)]
struct LengthFinalizationCase<'a> {
    range: (usize, usize),
    main: PacketLengths<'a>,
    seen: bool,
    plt_count: u64,
    plt_bytes: u64,
    plt_payload: u64,
    data_length: usize,
    packed_length: usize,
    offset: usize,
}

fn reference_length_finalization<'a>(
    input: &'a [u8],
    case: LengthFinalizationCase<'a>,
) -> Result<PacketLengths<'a>, DecodeError> {
    let lengths = if case.seen {
        let header = input
            .get(case.range.0..case.range.1)
            .ok_or_else(|| input_error_literal(case.offset, MalformedKind::InvalidTilePart))?;
        PacketLengths {
            source: PacketLengthSource::Plt(header),
            packet_count: case.plt_count,
            encoded_bytes: case.plt_bytes,
        }
    } else {
        case.main
    };
    if lengths.source == PacketLengthSource::None {
        return Ok(lengths);
    }
    let declared = if case.seen {
        case.plt_payload
    } else {
        reference_packet_sum(lengths.source)?
    };
    let logical = case.data_length as u128 + case.packed_length as u128;
    if logical > u128::from(u64::MAX) {
        Err(input_error_literal(
            case.offset,
            MalformedKind::ArithmeticOverflow,
        ))
    } else if u128::from(declared) != logical {
        Err(input_error_literal(
            case.offset,
            MalformedKind::InvalidPacketLength,
        ))
    } else {
        Ok(lengths)
    }
}

#[test]
fn actual_length_finalization_preserves_precedence_raw_fields_bounds_sums_and_reader() {
    let input = [0xde, 0, 1, 0xff];
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let state = PacketAdmissionState {
        position: usize::MAX,
        work: u64::MAX,
        header_bytes: u64::MAX,
        packet_count: u64::MAX,
    };
    set_packet_admission_state(&mut parser, state);
    let mut contexts = 0;
    for source in [
        PacketLengthSource::None,
        PacketLengthSource::Plm(&[1, 2]),
        PacketLengthSource::Plm(&[0]),
        PacketLengthSource::Plm(&[]),
        PacketLengthSource::Plt(&[]),
    ] {
        for (count, bytes) in [(0, 0), (u64::MAX, u64::MAX), (9, 17)] {
            for start in [0, 1, 4, 5, usize::MAX] {
                for end in [0, 1, 4, 5, usize::MAX] {
                    for seen in [false, true] {
                        for payload in [0, 1, 3, u64::MAX] {
                            for data in [0, 1, 3, usize::MAX] {
                                for packed in [0, 1, usize::MAX] {
                                    for offset in [0, usize::MAX] {
                                        let case = LengthFinalizationCase {
                                            range: (start, end),
                                            main: PacketLengths {
                                                source,
                                                packet_count: count,
                                                encoded_bytes: bytes,
                                            },
                                            seen,
                                            plt_count: bytes,
                                            plt_bytes: count,
                                            plt_payload: payload,
                                            data_length: data,
                                            packed_length: packed,
                                            offset,
                                        };
                                        let expected = reference_length_finalization(&input, case);
                                        let actual = parser.finish_packet_lengths(
                                            start, end, case.main, seen, bytes, count, payload,
                                            data, packed, offset,
                                        );
                                        assert_eq!(actual, expected);
                                        if let (Ok(actual), Ok(expected)) = (actual, expected) {
                                            match (actual.source, expected.source) {
                                                (
                                                    PacketLengthSource::Plm(actual),
                                                    PacketLengthSource::Plm(expected),
                                                )
                                                | (
                                                    PacketLengthSource::Plt(actual),
                                                    PacketLengthSource::Plt(expected),
                                                ) => assert!(core::ptr::eq(
                                                    actual.as_ptr(),
                                                    expected.as_ptr()
                                                )),
                                                _ => {}
                                            }
                                        }
                                        assert_packet_admission_state(
                                            &parser, state, &input, &limits,
                                        );
                                        contexts += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 72_000);
}

#[test]
fn actual_packed_finalization_preserves_zero_bypass_raw_main_and_exact_source_borrows() {
    let input = [0xde, 0, 1, 0xff];
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let state = PacketAdmissionState {
        position: usize::MAX,
        work: u64::MAX,
        header_bytes: u64::MAX,
        packet_count: u64::MAX,
    };
    set_packet_admission_state(&mut parser, state);
    let mut contexts = 0;
    for main in [
        PackedPacketHeaders {
            source: PackedPacketHeaderSource::None,
            length: usize::MAX,
            fragments: u16::MAX,
        },
        PackedPacketHeaders {
            source: PackedPacketHeaderSource::MarkerSegments {
                header: &[0, 0xff],
                marker: u16::MAX,
                logical_start: usize::MAX,
            },
            length: usize::MAX,
            fragments: u16::MAX,
        },
        PackedPacketHeaders {
            source: PackedPacketHeaderSource::MarkerSegments {
                header: &[],
                marker: PPM,
                logical_start: 17,
            },
            length: 0,
            fragments: 0,
        },
    ] {
        for start in [0, 1, 4, 5, usize::MAX] {
            for end in [0, 1, 4, 5, usize::MAX] {
                for fragments in [0, 1, u16::MAX] {
                    for length in [0, 1, usize::MAX] {
                        for offset in [0, usize::MAX] {
                            let expected = if fragments == 0 {
                                Ok(main)
                            } else {
                                input.get(start..end).map_or_else(
                                    || {
                                        Err(input_error_literal(
                                            offset,
                                            MalformedKind::InvalidTilePart,
                                        ))
                                    },
                                    |header| {
                                        Ok(PackedPacketHeaders {
                                            source: PackedPacketHeaderSource::MarkerSegments {
                                                header,
                                                marker: PPT,
                                                logical_start: 0,
                                            },
                                            length,
                                            fragments,
                                        })
                                    },
                                )
                            };
                            let actual = parser.finish_packed_packet_headers(
                                start, end, main, fragments, length, offset,
                            );
                            assert_eq!(actual, expected);
                            if let (Ok(actual), Ok(expected)) = (actual, expected)
                                && let (
                                    PackedPacketHeaderSource::MarkerSegments {
                                        header: actual, ..
                                    },
                                    PackedPacketHeaderSource::MarkerSegments {
                                        header: expected,
                                        ..
                                    },
                                ) = (actual.source, expected.source)
                            {
                                assert!(core::ptr::eq(actual.as_ptr(), expected.as_ptr()));
                            }
                            assert_packet_admission_state(&parser, state, &input, &limits);
                            contexts += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 1_350);
}

#[test]
fn actual_packet_metadata_joins_real_plm_and_ppt_producers_without_prepared_results() {
    let mut input = segment(PLM, &[0, 0, 0, 0, 1, 3]);
    input.extend(segment(PPT, &[0, 0xab]));
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let raw = parser.read_segment().unwrap();
    let mut groups = Vec::new();
    let mut next_plm = 0;
    parser.parse_plm(raw, &mut next_plm, &mut groups).unwrap();
    let start = parser.position;
    let raw = parser.read_segment().unwrap();
    let end = parser.position;
    let (mut next_ppt, mut fragments, mut bytes) = (0, 0, Vec::new());
    parser
        .parse_packed_fragment(raw, PPT, &mut next_ppt, &mut fragments, &mut bytes)
        .unwrap();
    let state = PacketAdmissionState {
        position: parser.position,
        work: parser.work_units,
        header_bytes: parser.packet_length_bytes,
        packet_count: parser.packet_lengths,
    };
    let packed = parser
        .finish_packed_packet_headers(
            start,
            end,
            PackedPacketHeaders::none(),
            fragments,
            bytes.len(),
            17,
        )
        .unwrap();
    let lengths = parser
        .finish_packet_lengths(
            usize::MAX,
            0,
            groups[0],
            false,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            2,
            packed.length,
            17,
        )
        .unwrap();
    assert_eq!((next_plm, next_ppt, fragments), (1, 1, 1));
    assert_eq!(bytes, [0xab]);
    assert_eq!(lengths, groups[0]);
    assert_eq!((lengths.packet_count, lengths.encoded_bytes), (1, 1));
    assert_eq!(packed.length, 1);
    assert_eq!(packed.fragments, 1);
    assert_eq!(
        packed.source,
        PackedPacketHeaderSource::MarkerSegments {
            header: &input[start..end],
            marker: PPT,
            logical_start: 0,
        }
    );
    if let PackedPacketHeaderSource::MarkerSegments { header, .. } = packed.source {
        assert!(core::ptr::eq(header.as_ptr(), input[start..end].as_ptr()));
    } else {
        panic!("actual PPT source was discarded");
    }
    assert_packet_admission_state(&parser, state, &input, &limits);
}

#[test]
fn actual_packet_length_admission_derives_all_short_varints_and_full_reader_results() {
    let limits = ResourceLimits::HARDENED;
    let mut contexts = 0;
    for word in 0..=u16::MAX {
        let bytes = word.to_be_bytes();
        for end in 0..=bytes.len() {
            for packet_count in [0, u64::MAX] {
                for offset in [0, usize::MAX] {
                    let mut state = raw_packet_admission_state();
                    state.packet_count = packet_count;
                    assert_packet_admission_case(&limits, state, &bytes[..end], offset);
                    contexts += 1;
                }
            }
        }
    }
    assert_eq!(contexts, 786_432);
}

#[test]
fn actual_packet_length_admission_preserves_byte_work_packet_overflow_and_limit_commits() {
    let payloads: &[&[u8]] = &[
        &[],
        &[1],
        &[0],
        &[0x81, 0],
        &[0x80],
        &[0x8f, 0xff, 0xff, 0xff, 0x7f],
        &[0xff, 0xff, 0xff, 0xff, 0x7f],
        &[0x80, 0x80, 0x80, 0x80, 0x80, 1],
    ];
    let mut contexts = 0;
    for cap in [0, 1, 3, 8, 32] {
        let limits = ResourceLimits::HARDENED
            .with_maximum_packet_header_bytes(cap)
            .unwrap()
            .with_maximum_work_units(cap)
            .unwrap()
            .with_maximum_packets(cap)
            .unwrap();
        for work in [0, 1, 2, 8, u64::MAX - 1, u64::MAX] {
            for header_bytes in [0, 1, 8, u64::MAX - 1, u64::MAX] {
                for packet_count in [0, 1, 8, u64::MAX - 1, u64::MAX] {
                    for encoded in payloads {
                        for offset in [0, usize::MAX] {
                            assert_packet_admission_case(
                                &limits,
                                PacketAdmissionState {
                                    position: 17,
                                    work,
                                    header_bytes,
                                    packet_count,
                                },
                                encoded,
                                offset,
                            );
                            contexts += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 12_000);
}

#[test]
fn actual_plm_groups_derive_raw_lengths_indexes_borrowed_sources_and_partial_commits() {
    let mut contexts = 0;
    for index in 0..=u8::MAX {
        let mut payload = vec![index];
        for encoded in [&[1, 2][..], &[][..], &[0][..]] {
            payload.extend((encoded.len() as u32).to_be_bytes());
            payload.extend(encoded);
        }
        for end in 0..=payload.len() {
            for next in [0, 1, 254, 255, 256, u16::MAX] {
                for initial in [0, 2] {
                    for cap in [0, 1, 3] {
                        let limits = ResourceLimits::HARDENED
                            .with_maximum_tile_parts(cap)
                            .unwrap();
                        let mut case = raw_plm_producer_case(&payload[..end], next);
                        case.groups.truncate(initial);
                        case.marker = PPT;
                        assert_plm_producer_case(&limits, case);
                        contexts += 1;
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 156_672);
    let mut lengths = 0;
    for low in 0..=u16::MAX {
        for high in [0_u32, 0xffff0000] {
            for index in [0, 255] {
                let mut payload = vec![index];
                payload.extend((high | u32::from(low)).to_be_bytes());
                payload.extend([1, 2]);
                assert_plm_producer_case(
                    &ResourceLimits::HARDENED,
                    raw_plm_producer_case(&payload, u16::from(index)),
                );
                lengths += 1;
            }
        }
    }
    assert_eq!(lengths, 262_144);
}

#[test]
fn actual_plm_groups_preserve_charge_errors_append_caps_and_real_segment_reader_join() {
    let mut payload = vec![0];
    for encoded in [&[3][..], &[][..], &[0x81, 0][..]] {
        payload.extend((encoded.len() as u32).to_be_bytes());
        payload.extend(encoded);
    }
    let mut contexts = 0;
    for cap in [0, 1, 2, 3, 32] {
        for charge_cap in [0, 1, 2, 8] {
            let limits = ResourceLimits::HARDENED
                .with_maximum_tile_parts(cap)
                .unwrap()
                .with_maximum_packet_header_bytes(charge_cap)
                .unwrap()
                .with_maximum_work_units(charge_cap)
                .unwrap()
                .with_maximum_packets(charge_cap)
                .unwrap();
            for initial in [0, 2] {
                for work in [0, 1, u64::MAX] {
                    for header_bytes in [0, 1, u64::MAX] {
                        for packet_count in [0, 1, u64::MAX] {
                            let mut case = raw_plm_producer_case(&payload, 0);
                            case.groups.truncate(initial);
                            case.state.work = work;
                            case.state.header_bytes = header_bytes;
                            case.state.packet_count = packet_count;
                            assert_plm_producer_case(&limits, case);
                            contexts += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 1_080);
    let input = segment(PLM, &payload);
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let raw = parser.read_segment().unwrap();
    let before = parser.work_units;
    let mut next = 0;
    let mut groups = Vec::new();
    parser.parse_plm(raw, &mut next, &mut groups).unwrap();
    assert_eq!((next, groups.len()), (1, 3));
    assert_eq!(
        groups
            .iter()
            .map(|group| group.packet_count)
            .collect::<Vec<_>>(),
        [1, 0, 1]
    );
    assert_eq!(
        groups
            .iter()
            .map(|group| group.encoded_bytes)
            .collect::<Vec<_>>(),
        [1, 0, 2]
    );
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths,
        ),
        (input.len(), before + 3, 3, 2)
    );
    for (group, expected) in groups.iter().zip([&[3][..], &[][..], &[0x81, 0][..]]) {
        assert_eq!(group.source, PacketLengthSource::Plm(expected));
    }
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));
}

#[test]
fn actual_packed_fragments_preserve_all_indexes_counter_frames_and_source_bytes() {
    let limits = ResourceLimits::HARDENED;
    let mut contexts = 0;
    for index in 0..=u8::MAX {
        for next in [0, 1, 254, 255, 256, u16::MAX] {
            for fragments in [0, 1, u16::MAX - 1, u16::MAX] {
                for length in [0, 1, 3, 9] {
                    let mut payload = vec![index];
                    payload.extend((0..length).map(|value| value as u8 ^ index));
                    for (marker, expected) in [(PPM, PPM), (PPT, PPT), (PPT, PPM)] {
                        for offset in [0, usize::MAX] {
                            let mut case = raw_packed_producer_case(&payload, next, fragments);
                            case.marker = marker;
                            case.expected_marker = expected;
                            case.offset = offset;
                            assert_packed_producer_case(&limits, case);
                            contexts += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 147_456);
    for next in [0, 1, 254, 255, 256, u16::MAX] {
        for fragments in [0, 1, u16::MAX - 1, u16::MAX] {
            assert_packed_producer_case(&limits, raw_packed_producer_case(&[], next, fragments));
        }
    }
}

#[test]
fn actual_packed_fragments_preserve_header_work_limit_and_overflow_commit_order() {
    let mut contexts = 0;
    for work in [0, 1, 2, u64::MAX - 2, u64::MAX - 1, u64::MAX] {
        for header_bytes in [0, 1, 2, u64::MAX - 1, u64::MAX] {
            for initial_length in [0, 3] {
                for next in [0, 255] {
                    for fragments in [0, u16::MAX] {
                        for length in [0, 1, 3] {
                            let mut payload = vec![next as u8];
                            payload.extend(vec![0xa5; length]);
                            for byte_limit in [
                                0,
                                1,
                                2,
                                8,
                                ResourceLimits::HARDENED.maximum_packet_header_bytes(),
                            ] {
                                for work_limit in
                                    [0, 1, 2, 8, ResourceLimits::HARDENED.maximum_work_units()]
                                {
                                    let limits = ResourceLimits::HARDENED
                                        .with_maximum_packet_header_bytes(byte_limit)
                                        .unwrap()
                                        .with_maximum_work_units(work_limit)
                                        .unwrap();
                                    let mut case =
                                        raw_packed_producer_case(&payload, next, fragments);
                                    case.work = work;
                                    case.header_bytes = header_bytes;
                                    case.bytes = vec![0xff; initial_length];
                                    case.position = 17;
                                    case.offset = usize::MAX;
                                    assert_packed_producer_case(&limits, case);
                                    contexts += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 18_000);
}

#[test]
fn actual_ppm_frames_preserve_zero_bypass_lengths_caps_offsets_and_reader() {
    let mut words = 0;
    for low in 0..=u16::MAX {
        for high in [0_u32, 0xffff0000] {
            let length = high | u32::from(low);
            let mut bytes = length.to_be_bytes().to_vec();
            bytes.extend([0, 1, 2]);
            for cap in [0, 1, 2] {
                let limits = ResourceLimits::HARDENED
                    .with_maximum_tile_parts(cap)
                    .unwrap();
                let parser = new_parser(&[], &limits).unwrap();
                for fragments in [0, 1, u16::MAX] {
                    assert_ppm_producer_case(&parser, &bytes, fragments);
                    words += 1;
                }
            }
        }
    }
    assert_eq!(words, 1_179_648);
    let mut compound = Vec::new();
    for length in [0_u32, 1, 3, 8] {
        compound.extend(length.to_be_bytes());
        compound.extend(vec![0xa5; length as usize]);
    }
    let mut cuts = 0;
    for end in 0..=compound.len() {
        for cap in [0, 1, 3, 4, ResourceLimits::HARDENED.maximum_tile_parts()] {
            let limits = ResourceLimits::HARDENED
                .with_maximum_tile_parts(cap)
                .unwrap();
            let parser = new_parser(&[], &limits).unwrap();
            for fragments in [0, 1, u16::MAX] {
                assert_ppm_producer_case(&parser, &compound[..end], fragments);
                cuts += 1;
            }
        }
    }
    assert_eq!(cuts, 435);
    let mut data = 2_u32.to_be_bytes().to_vec();
    data.extend([0xaa, 0xbb]);
    data.extend(0_u32.to_be_bytes());
    data.extend(1_u32.to_be_bytes());
    data.push(0xff);
    let mut first = vec![0];
    first.extend(&data[..3]);
    let mut second = vec![1];
    second.extend(&data[3..]);
    let mut input = segment(PPM, &first);
    input.extend(segment(PPM, &second));
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let (mut next, mut fragments, mut bytes) = (0, 0, Vec::new());
    for _ in 0..2 {
        let raw = parser.read_segment().unwrap();
        parser
            .parse_packed_fragment(raw, PPM, &mut next, &mut fragments, &mut bytes)
            .unwrap();
    }
    assert_eq!((next, fragments, &bytes), (2, 2, &data));
    let frames: Vec<(usize, usize)> = parser
        .parse_ppm_frames(&bytes, fragments)
        .unwrap()
        .into_iter()
        .map(|frame| (frame.start, frame.length))
        .collect();
    assert_eq!(frames, vec![(4, 2), (10, 0), (14, 1)]);
    assert_eq!(parser.position, input.len());
    assert_eq!(parser.work_units, 17);
    assert_eq!(parser.packet_length_bytes, 15);
    assert_eq!(parser.packet_lengths, 0);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
}

fn reference_mct_graph_element_count(
    rows: usize,
    columns: usize,
    kind: MctArrayKind,
    reversible: bool,
) -> Result<usize, DecodeError> {
    let error = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let wide = rows as u128;
    let maximum = usize::MAX as u128;
    let result = if kind == MctArrayKind::Decorrelation {
        let product = wide * columns as u128;
        if product > maximum {
            return Err(error);
        }
        product
    } else if reversible {
        let product = wide * (wide + 1);
        if rows == usize::MAX || product > maximum || product / 2 == 0 {
            return Err(error);
        }
        product / 2 - 1
    } else {
        let product = wide * wide.saturating_sub(1);
        if product > maximum {
            return Err(error);
        }
        product / 2
    };
    Ok(usize::try_from(result).unwrap())
}

fn reference_mct_graph_array(
    arrays: &[MctArray],
    index: u8,
    kind: MctArrayKind,
) -> Result<MctArray, DecodeError> {
    let matches: Vec<&MctArray> = arrays
        .iter()
        .filter(|array| array.index == index && array.kind == kind)
        .collect();
    if matches.len() == 1 {
        Ok(matches[0].clone())
    } else {
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidTransform,
        })
    }
}

fn reference_mct_graph_collection(
    reference: &MctCollectionReference,
    arrays: &[MctArray],
) -> Result<MctCollection, DecodeError> {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    let rows = reference.input_components.len();
    let columns = reference.output_components.len();
    if rows == 0 || rows != columns {
        return Err(invalid);
    }
    match reference.transform {
        MctCollectionReferenceTransform::Wavelet(wavelet) => Ok(MctCollection {
            reversible: wavelet.transform == MctWaveletType::Reversible5x3,
            input_components: reference.input_components.clone(),
            output_components: reference.output_components.clone(),
            kind: MctCollectionKind::Wavelet,
            matrix: None,
            offsets: None,
            wavelet: Some(wavelet),
        }),
        MctCollectionReferenceTransform::Array {
            kind,
            reversible,
            transform_index,
            offset_index,
        } => {
            let offsets = if offset_index == 0 {
                None
            } else {
                Some(reference_mct_graph_array(
                    arrays,
                    offset_index,
                    MctArrayKind::Offset,
                )?)
            };
            let matrix = if transform_index == 0 {
                None
            } else {
                Some(reference_mct_graph_array(arrays, transform_index, kind)?)
            };
            let expected = reference_mct_graph_element_count(rows, columns, kind, reversible)?;
            if offsets.as_ref().is_some_and(|array| {
                array.values.len() != rows || (reversible && array.fraction_bits != 0)
            }) || matrix.as_ref().is_some_and(|array| {
                array.values.len() != expected || (reversible && array.fraction_bits != 0)
            }) {
                return Err(invalid);
            }
            Ok(MctCollection {
                reversible,
                input_components: reference.input_components.clone(),
                output_components: reference.output_components.clone(),
                kind: if kind == MctArrayKind::Dependency {
                    MctCollectionKind::Dependency
                } else {
                    MctCollectionKind::Decorrelation
                },
                matrix,
                offsets,
                wavelet: None,
            })
        }
    }
}

fn reference_mct_graph_stage(
    record: &MctRecord,
    arrays: &[MctArray],
) -> Result<MctStage, DecodeError> {
    let collections = record
        .collections
        .iter()
        .map(|reference| reference_mct_graph_collection(reference, arrays))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(MctStage {
        index: record.index,
        collections,
    })
}

fn reference_mct_graph(
    parameters: &MctParameters,
) -> Result<Option<MultipleComponentTransform>, DecodeError> {
    if parameters.order.is_empty() {
        return Ok(None);
    }
    let mut stages = Vec::new();
    for index in &parameters.order {
        let record = parameters
            .records
            .iter()
            .find(|record| record.index == *index)
            .ok_or(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidTransform,
            })?;
        stages.push(reference_mct_graph_stage(record, &parameters.arrays)?);
    }
    Ok(Some(MultipleComponentTransform { stages }))
}

fn raw_mct_graph_reference(
    rows: usize,
    columns: usize,
    kind: MctArrayKind,
    reversible: bool,
    transform_index: u8,
    offset_index: u8,
) -> MctCollectionReference {
    MctCollectionReference {
        input_components: (0..rows)
            .map(|position| {
                if position.is_multiple_of(2) {
                    0
                } else {
                    u16::MAX
                }
            })
            .collect(),
        output_components: vec![u16::MAX; columns],
        transform: MctCollectionReferenceTransform::Array {
            kind,
            reversible,
            transform_index,
            offset_index,
        },
    }
}

#[test]
fn actual_mct_graph_element_counts_preserve_checked_intermediate_overflow() {
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let boundary = 1_usize << (usize::BITS / 2);
    let mut rows: Vec<usize> = (0..=256).collect();
    rows.extend([
        65535,
        65536,
        65537,
        boundary - 1,
        boundary,
        boundary + 1,
        usize::MAX / 2,
        usize::MAX / 2 + 1,
        usize::MAX - 1,
        usize::MAX,
    ]);
    rows.sort_unstable();
    rows.dedup();
    let columns = [
        0,
        1,
        2,
        255,
        256,
        65535,
        65536,
        usize::MAX / 2,
        usize::MAX - 1,
        usize::MAX,
    ];
    let mut cases = 0;
    for row in &rows {
        for column in columns {
            for kind in [
                MctArrayKind::Dependency,
                MctArrayKind::Decorrelation,
                MctArrayKind::Offset,
            ] {
                for reversible in [false, true] {
                    assert_eq!(
                        parser.expected_mct_elements(*row, column, kind, reversible),
                        reference_mct_graph_element_count(*row, column, kind, reversible)
                    );
                    cases += 1;
                }
            }
        }
    }
    assert!(rows.len() >= 264);
    assert_eq!(cases, rows.len() * columns.len() * 6);
}

#[test]
fn actual_mct_graph_collections_preserve_lookup_shape_flags_and_all_fields() {
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&[], &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    let mut arrays_checked = 0;
    for rows in 0..=5 {
        for columns in 0..=5 {
            for kind in [
                MctArrayKind::Dependency,
                MctArrayKind::Decorrelation,
                MctArrayKind::Offset,
            ] {
                for reversible in [false, true] {
                    for transform_index in [0, 7, 8, 255] {
                        for offset_index in [0, 7, 8, 255] {
                            let reference = raw_mct_graph_reference(
                                rows,
                                columns,
                                kind,
                                reversible,
                                transform_index,
                                offset_index,
                            );
                            let expected = if rows == 0 {
                                0
                            } else {
                                reference_mct_graph_element_count(rows, columns, kind, reversible)
                                    .unwrap()
                            };
                            for variant in 0..12 {
                                let mut matrix = raw_mct_registry_array(7, variant);
                                matrix.kind = kind;
                                matrix.fraction_bits = [0, 32, 255][variant / 4];
                                matrix.values = vec![
                                    i64::MIN;
                                    match variant % 4 {
                                        0 => 0,
                                        1 => expected.saturating_sub(1),
                                        2 => expected,
                                        _ => expected + 1,
                                    }
                                ];
                                let mut offsets = raw_mct_registry_array(8, variant + 1);
                                offsets.kind = MctArrayKind::Offset;
                                offsets.fraction_bits =
                                    if variant.is_multiple_of(2) { 0 } else { 32 };
                                offsets.values = vec![
                                    i64::MAX;
                                    match variant / 4 {
                                        0 => rows,
                                        1 => rows + 1,
                                        _ => 0,
                                    }
                                ];
                                let mut other_kind = matrix.clone();
                                other_kind.kind = if kind == MctArrayKind::Dependency {
                                    MctArrayKind::Decorrelation
                                } else {
                                    MctArrayKind::Dependency
                                };
                                for duplicate in 0..4 {
                                    let mut arrays =
                                        vec![matrix.clone(), offsets.clone(), other_kind.clone()];
                                    match duplicate {
                                        0 => {}
                                        1 => arrays.push(matrix.clone()),
                                        2 => arrays.push(offsets.clone()),
                                        _ => arrays.clear(),
                                    }
                                    assert_eq!(
                                        parser.resolve_mct_collection(&reference, &arrays),
                                        reference_mct_graph_collection(&reference, &arrays)
                                    );
                                    arrays_checked += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(arrays_checked, 165_888);
    let mut wavelets = 0;
    for rows in 0..=5 {
        for columns in 0..=5 {
            for transform in [
                MctWaveletType::Reversible5x3,
                MctWaveletType::Irreversible9x7,
            ] {
                for levels in [0, 1, 255] {
                    for component_offset in [i32::MIN, 0, i32::MAX] {
                        let reference = MctCollectionReference {
                            input_components: vec![u16::MAX; rows],
                            output_components: vec![0; columns],
                            transform: MctCollectionReferenceTransform::Wavelet(MctWavelet {
                                transform,
                                levels,
                                component_offset,
                            }),
                        };
                        assert_eq!(
                            parser.resolve_mct_collection(&reference, &[]),
                            reference_mct_graph_collection(&reference, &[])
                        );
                        wavelets += 1;
                    }
                }
            }
        }
    }
    assert_eq!(wavelets, 648);
    assert_eq!((parser.position, parser.work_units), (usize::MAX, u64::MAX));
}

#[test]
fn actual_mct_graph_complete_parameters_preserve_order_first_records_and_empty_bypass() {
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let mut dependency = raw_mct_registry_array(7, 3);
    dependency.kind = MctArrayKind::Dependency;
    dependency.fraction_bits = 0;
    dependency.values = vec![i64::MIN];
    let mut decorrelation = dependency.clone();
    decorrelation.kind = MctArrayKind::Decorrelation;
    decorrelation.values = vec![i64::MAX; 4];
    let mut reversible = dependency.clone();
    reversible.index = 9;
    reversible.values = vec![0; 2];
    let mut offsets = dependency.clone();
    offsets.index = 8;
    offsets.kind = MctArrayKind::Offset;
    offsets.values = vec![i64::MAX; 2];
    let arrays = vec![dependency, decorrelation, reversible, offsets];
    let mut cases = 0;
    for index in 0..=u8::MAX {
        for variant in 0..9 {
            let reference = match variant {
                0 => None,
                1 => Some(raw_mct_graph_reference(
                    2,
                    2,
                    MctArrayKind::Dependency,
                    false,
                    7,
                    8,
                )),
                2 => Some(raw_mct_graph_reference(
                    2,
                    2,
                    MctArrayKind::Decorrelation,
                    true,
                    7,
                    8,
                )),
                3 => Some(raw_mct_graph_reference(
                    2,
                    2,
                    MctArrayKind::Dependency,
                    true,
                    9,
                    8,
                )),
                4 | 5 => Some(MctCollectionReference {
                    input_components: vec![0, u16::MAX],
                    output_components: vec![9, 9],
                    transform: MctCollectionReferenceTransform::Wavelet(MctWavelet {
                        transform: if variant == 4 {
                            MctWaveletType::Reversible5x3
                        } else {
                            MctWaveletType::Irreversible9x7
                        },
                        levels: 255,
                        component_offset: i32::MIN,
                    }),
                }),
                6 => Some(raw_mct_graph_reference(
                    2,
                    2,
                    MctArrayKind::Dependency,
                    false,
                    7,
                    255,
                )),
                7 => Some(raw_mct_graph_reference(
                    2,
                    1,
                    MctArrayKind::Dependency,
                    false,
                    7,
                    8,
                )),
                _ => Some(raw_mct_graph_reference(
                    2,
                    2,
                    MctArrayKind::Offset,
                    false,
                    8,
                    0,
                )),
            };
            let record = MctRecord {
                index,
                collections: reference.into_iter().collect(),
            };
            let bad = MctRecord {
                index,
                collections: vec![raw_mct_graph_reference(
                    0,
                    0,
                    MctArrayKind::Dependency,
                    true,
                    0,
                    0,
                )],
            };
            let other = MctRecord {
                index: index.wrapping_add(1),
                collections: vec![],
            };
            for records in [
                vec![record.clone()],
                vec![record.clone(), bad.clone()],
                vec![other, record.clone(), bad.clone()],
                vec![bad, record.clone()],
            ] {
                assert_eq!(
                    parser.resolve_mct_stage(&record, &arrays),
                    reference_mct_graph_stage(&record, &arrays)
                );
                for order in [
                    vec![],
                    vec![index],
                    vec![index, index],
                    vec![index.wrapping_add(1), index],
                    vec![index, index.wrapping_add(1)],
                    vec![0],
                    vec![255],
                    vec![index, index.wrapping_add(1), index],
                ] {
                    let parameters = MctParameters {
                        arrays: arrays.clone(),
                        records: records.clone(),
                        order,
                    };
                    assert_eq!(
                        parser.resolve_multiple_component_transform(&parameters),
                        reference_mct_graph(&parameters)
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 73_728);
}

fn raw_mct_registry_array(index: u8, variant: usize) -> MctArray {
    MctArray {
        index,
        kind: [
            MctArrayKind::Dependency,
            MctArrayKind::Decorrelation,
            MctArrayKind::Offset,
        ][variant % 3],
        numeric_format: [
            MctNumericFormat::Int16,
            MctNumericFormat::Int32,
            MctNumericFormat::Float32,
            MctNumericFormat::Float64,
        ][variant / 3 % 4],
        fraction_bits: [0, 32, 255][variant / 12 % 3],
        values: match variant % 4 {
            0 => vec![],
            1 => vec![i64::MIN],
            2 => vec![0, variant as i64],
            _ => vec![i64::MIN, variant as i64, i64::MAX],
        },
    }
}

fn raw_mct_registry_record(index: u8, variant: usize) -> MctRecord {
    let collections = (0..variant % 4)
        .map(|position| {
            let value = variant + position;
            MctCollectionReference {
                input_components: vec![0, u16::MAX, value as u16, 0],
                output_components: if value.is_multiple_of(2) {
                    vec![]
                } else {
                    vec![u16::MAX, 0]
                },
                transform: if value.is_multiple_of(3) {
                    MctCollectionReferenceTransform::Array {
                        kind: [
                            MctArrayKind::Dependency,
                            MctArrayKind::Decorrelation,
                            MctArrayKind::Offset,
                        ][value / 3 % 3],
                        reversible: value.is_multiple_of(2),
                        transform_index: [0, 7, 255][value / 3 % 3],
                        offset_index: [255, 0, 7][value / 6 % 3],
                    }
                } else {
                    MctCollectionReferenceTransform::Wavelet(MctWavelet {
                        transform: if value % 3 == 1 {
                            MctWaveletType::Reversible5x3
                        } else {
                            MctWaveletType::Irreversible9x7
                        },
                        levels: [0, 1, 255][value % 3],
                        component_offset: if value.is_multiple_of(2) {
                            i32::MIN
                        } else {
                            i32::MAX
                        },
                    })
                },
            }
        })
        .collect();
    MctRecord { index, collections }
}

fn raw_mct_registry_index_cases(index: u8) -> [Vec<u8>; 6] {
    [
        vec![],
        vec![index],
        vec![index.wrapping_add(1)],
        vec![index, index.wrapping_add(1), index],
        vec![index.wrapping_add(1), index, 0, index],
        vec![index, index, index.wrapping_add(1)],
    ]
}

#[test]
fn actual_mct_registry_preserves_last_only_admission_and_all_array_replacements() {
    let mut contexts = 0;
    let mut replacements = 0;
    for index in 0..=u8::MAX {
        for indices in raw_mct_registry_index_cases(index) {
            for variant in 0..36 {
                let arrays: Vec<MctArray> = indices
                    .iter()
                    .enumerate()
                    .map(|(position, value)| raw_mct_registry_array(*value, variant + position))
                    .collect();
                let expected_first = arrays.iter().position(|array| array.index == index);
                assert_eq!(find_mct_array_index(&arrays, index), expected_first);
                for offset in [0, usize::MAX] {
                    let duplicate_last = arrays.last().is_some_and(|last| {
                        arrays[..arrays.len() - 1]
                            .iter()
                            .any(|array| array.index == last.index)
                    });
                    let expected = if duplicate_last {
                        Err(DecodeError::MalformedInput {
                            offset: offset as u64,
                            kind: MalformedKind::InvalidTransform,
                        })
                    } else {
                        Ok(())
                    };
                    assert_eq!(validate_unique_mct_array_indexes(&arrays, offset), expected);
                }
                for value in [0, 3, 7, 11, 12, 23, 24, 35] {
                    let replacement = raw_mct_registry_array(index, value);
                    let mut actual = arrays.clone();
                    let mut expected = arrays.clone();
                    match expected_first {
                        Some(position) => expected[position] = replacement.clone(),
                        None => expected.push(replacement.clone()),
                    }
                    replace_mct_array(&mut actual, replacement);
                    assert_eq!(actual, expected);
                    replacements += 1;
                }
                contexts += 1;
            }
        }
    }
    assert_eq!(contexts, 55_296);
    assert_eq!(replacements, 442_368);
}

#[test]
fn actual_mct_registry_preserves_complete_raw_record_replacements() {
    let mut contexts = 0;
    let mut replacements = 0;
    for index in 0..=u8::MAX {
        for indices in raw_mct_registry_index_cases(index) {
            for variant in 0..12 {
                let records: Vec<MctRecord> = indices
                    .iter()
                    .enumerate()
                    .map(|(position, value)| raw_mct_registry_record(*value, variant + position))
                    .collect();
                let expected_first = records.iter().position(|record| record.index == index);
                assert_eq!(find_mct_record_index(&records, index), expected_first);
                for offset in [0, usize::MAX] {
                    let duplicate_last = records.last().is_some_and(|last| {
                        records[..records.len() - 1]
                            .iter()
                            .any(|record| record.index == last.index)
                    });
                    let expected = if duplicate_last {
                        Err(DecodeError::MalformedInput {
                            offset: offset as u64,
                            kind: MalformedKind::InvalidTransform,
                        })
                    } else {
                        Ok(())
                    };
                    assert_eq!(
                        validate_unique_mct_record_indexes(&records, offset),
                        expected
                    );
                }
                for value in [0, 1, 2, 3, 5, 7, 11, 12] {
                    let replacement = raw_mct_registry_record(index, value);
                    let mut actual = records.clone();
                    let mut expected = records.clone();
                    match expected_first {
                        Some(position) => expected[position] = replacement.clone(),
                        None => expected.push(replacement.clone()),
                    }
                    replace_mct_record(&mut actual, replacement);
                    assert_eq!(actual, expected);
                    replacements += 1;
                }
                contexts += 1;
            }
        }
    }
    assert_eq!(contexts, 18_432);
    assert_eq!(replacements, 147_456);
}

#[test]
fn actual_mct_registry_references_require_exactly_one_matching_index_and_kind() {
    let mut contexts = 0;
    for index in 0..=u8::MAX {
        let mut cases = raw_mct_registry_index_cases(index).to_vec();
        cases.push(vec![index; 4]);
        cases.push(vec![
            index.wrapping_add(1),
            index,
            index.wrapping_add(1),
            index,
        ]);
        for indices in cases {
            for variant in 0..12 {
                let arrays: Vec<MctArray> = indices
                    .iter()
                    .enumerate()
                    .map(|(position, value)| raw_mct_registry_array(*value, variant + position))
                    .collect();
                for kind in [
                    MctArrayKind::Dependency,
                    MctArrayKind::Decorrelation,
                    MctArrayKind::Offset,
                ] {
                    let matches: Vec<usize> = arrays
                        .iter()
                        .enumerate()
                        .filter(|(_, array)| array.index == index && array.kind == kind)
                        .map(|(position, _)| position)
                        .collect();
                    let result = referenced_mct_array(&arrays, index, kind);
                    if matches.len() == 1 {
                        let actual = result.unwrap();
                        assert_eq!(actual, &arrays[matches[0]]);
                        assert!(core::ptr::eq(actual, &arrays[matches[0]]));
                    } else {
                        assert_eq!(
                            result,
                            Err(DecodeError::MalformedInput {
                                offset: 0,
                                kind: MalformedKind::InvalidTransform,
                            })
                        );
                    }
                    contexts += 1;
                }
            }
        }
    }
    assert_eq!(contexts, 73_728);
}

fn reference_prepare_mct_fragment(
    bytes: &[u8],
    limits: &ResourceLimits,
    pending: &mut Vec<MctFragment>,
    completed: &[u8],
    offset: usize,
) -> Result<(usize, u64), DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    if bytes.len() < 4 || bytes[3] == 0 {
        return Err(malformed(MalformedKind::InvalidTransform));
    }
    let fragment = u16::from_be_bytes([bytes[0], bytes[1]]);
    let descriptor = u16::from_be_bytes([bytes[2], bytes[3]]);
    let index = bytes[3];
    let maximum = u64::try_from(u128::from(limits.maximum_components()).pow(2) * 8).unwrap();
    let found = pending
        .iter()
        .position(|state| state.descriptor.to_be_bytes()[1] == index);
    if fragment == 0 {
        if bytes.len() < 6 || found.is_some() || completed.contains(&index) {
            return Err(malformed(MalformedKind::InvalidTransform));
        }
        let final_index = u16::from_be_bytes([bytes[4], bytes[5]]);
        if u64::from(final_index) + 1 > maximum {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TransformElements,
                limit: maximum,
                actual: u64::from(final_index) + 1,
            });
        }
        if bytes[6..].len() as u64 > maximum {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TransformElements,
                limit: maximum,
                actual: bytes[6..].len() as u64,
            });
        }
        let active = pending.len();
        pending.push(MctFragment {
            descriptor,
            next_index: 1,
            final_index,
            offset,
            data: bytes[6..].to_vec(),
        });
        Ok((active, maximum))
    } else {
        let active = found.ok_or_else(|| malformed(MalformedKind::InvalidTransform))?;
        let state = &mut pending[active];
        if state.descriptor != descriptor
            || fragment != state.next_index
            || fragment > state.final_index
        {
            return Err(malformed(MalformedKind::InvalidTransform));
        }
        state.data = [state.data.as_slice(), &bytes[4..]].concat();
        if state.data.len() as u64 > maximum {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TransformElements,
                limit: maximum,
                actual: state.data.len() as u64,
            });
        }
        if state.next_index == u16::MAX {
            return Err(malformed(MalformedKind::ArithmeticOverflow));
        }
        state.next_index += 1;
        Ok((active, maximum))
    }
}

fn reference_consume_mct_fragment(
    bytes: &[u8],
    limits: &ResourceLimits,
    pending: &mut Vec<MctFragment>,
    completed: &mut Vec<u8>,
    offset: usize,
) -> Result<Option<MctArray>, DecodeError> {
    let (active, maximum) =
        reference_prepare_mct_fragment(bytes, limits, pending, completed, offset)?;
    if u32::from(pending[active].next_index) != u32::from(pending[active].final_index) + 1 {
        return Ok(None);
    }
    let state = pending[active].clone();
    let last = pending.pop().unwrap();
    if active < pending.len() {
        pending[active] = last;
    }
    if state.data.len() as u64 > maximum {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::TransformElements,
            limit: maximum,
            actual: state.data.len() as u64,
        });
    }
    let mut payload = vec![0, 0];
    payload.extend(state.descriptor.to_be_bytes());
    payload.extend([0, 0]);
    payload.extend(&state.data);
    let array = reference_mct_array(&payload, limits, state.offset)?;
    completed.push(bytes[3]);
    Ok(Some(array))
}

fn raw_mct_fragment_state(descriptor: u16, variant: usize) -> MctFragment {
    MctFragment {
        descriptor,
        next_index: if variant == 0 { 1 } else { u16::MAX },
        final_index: if variant == 0 { 1 } else { 0 },
        offset: usize::MAX - variant,
        data: vec![255, variant as u8, 17],
    }
}

fn raw_mct_fragment_payload(
    descriptor: u16,
    fragment: u16,
    final_index: u16,
    data: &[u8],
) -> Vec<u8> {
    let mut bytes = fragment.to_be_bytes().to_vec();
    bytes.extend(descriptor.to_be_bytes());
    if fragment == 0 {
        bytes.extend(final_index.to_be_bytes());
    }
    bytes.extend(data);
    bytes
}

fn assert_mct_fragment_case(
    parser: &Parser<'_>,
    bytes: &[u8],
    pending: &[MctFragment],
    completed: &[u8],
    offset: usize,
) -> (
    Result<Option<MctArray>, DecodeError>,
    Vec<MctFragment>,
    Vec<u8>,
) {
    let mut actual_prepared = pending.to_vec();
    let mut expected_prepared = pending.to_vec();
    let expected = reference_prepare_mct_fragment(
        bytes,
        parser.limits,
        &mut expected_prepared,
        completed,
        offset,
    );
    assert_eq!(
        parser.prepare_mct_fragment(
            Segment {
                marker: 0x1234,
                offset,
                payload: bytes,
            },
            &mut actual_prepared,
            completed,
        ),
        expected
    );
    assert_eq!(actual_prepared, expected_prepared);
    let mut actual_pending = pending.to_vec();
    let mut expected_pending = pending.to_vec();
    let mut actual_completed = completed.to_vec();
    let mut expected_completed = completed.to_vec();
    let expected = reference_consume_mct_fragment(
        bytes,
        parser.limits,
        &mut expected_pending,
        &mut expected_completed,
        offset,
    );
    let actual = parser.consume_mct_fragment(
        Segment {
            marker: 0x1234,
            offset,
            payload: bytes,
        },
        &mut actual_pending,
        &mut actual_completed,
    );
    assert_eq!(actual, expected);
    assert_eq!(actual_pending, expected_pending);
    assert_eq!(actual_completed, expected_completed);
    (actual, actual_pending, actual_completed)
}

#[test]
fn actual_mct_fragments_preserve_descriptors_first_matches_and_partial_commits() {
    let limits = ResourceLimits::HARDENED;
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let mut descriptors = 0;
    for descriptor in 0..=u16::MAX {
        let index = descriptor.to_be_bytes()[1];
        let first = raw_mct_fragment_payload(descriptor, 0, 1, &[0, 1]);
        let _ = assert_mct_fragment_case(&parser, &first, &[], &[], 13);
        let duplicate = [
            raw_mct_fragment_state(descriptor, 0),
            raw_mct_fragment_state(descriptor ^ 0x0100, 1),
        ];
        let _ = assert_mct_fragment_case(&parser, &first, &duplicate, &[index], usize::MAX);
        let active = MctFragment {
            descriptor,
            next_index: 1,
            final_index: 1,
            offset: 13,
            data: vec![0, 1],
        };
        let other = raw_mct_fragment_state(u16::from(index.wrapping_add(1)), 1);
        let next = raw_mct_fragment_payload(descriptor, 1, 0, &[0, 2]);
        let _ = assert_mct_fragment_case(
            &parser,
            &next,
            &[other.clone(), active.clone(), duplicate[1].clone()],
            &[index, index],
            usize::MAX,
        );
        let wrong_first = MctFragment {
            descriptor: descriptor ^ 0x0100,
            ..active.clone()
        };
        let _ = assert_mct_fragment_case(&parser, &next, &[wrong_first, active, other], &[], 0);
        descriptors += 4;
    }
    assert_eq!(descriptors, 262_144);
    let mut headers = 0;
    for length in 0..=6 {
        for fragment in [0_u16, 1, u16::MAX] {
            for descriptor in [0_u16, 7, 0x0407, 0x0e07, u16::MAX] {
                let mut bytes = fragment.to_be_bytes().to_vec();
                bytes.extend(descriptor.to_be_bytes());
                bytes.extend([0, 1]);
                let _ = assert_mct_fragment_case(&parser, &bytes[..length], &[], &[], usize::MAX);
                headers += 1;
            }
        }
    }
    assert_eq!(headers, 105);
    assert_eq!((parser.position, parser.work_units), (usize::MAX, u64::MAX));
    assert_eq!(
        (parser.packet_length_bytes, parser.packet_lengths),
        (u64::MAX - 1, u64::MAX - 2)
    );
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
}

#[test]
fn actual_mct_fragments_compose_numeric_arrays_swap_order_offsets_and_reader() {
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let mut splits = 0;
    for format in 0_u16..4 {
        for kind in 0_u16..3 {
            for index in [1_u8, 7, 255] {
                let descriptor = format * 1024 + kind * 256 + u16::from(index);
                for elements in [
                    vec![0_u64],
                    vec![1, u64::MAX],
                    vec![0x3f800000, 0x7f800000],
                    vec![0x3ff0000000000000, 0x7ff8000000000000],
                ] {
                    let payload = raw_mct_array_payload(descriptor, &elements);
                    let data = &payload[6..];
                    for split in 0..=data.len() {
                        let first = raw_mct_fragment_payload(descriptor, 0, 1, &data[..split]);
                        let other = raw_mct_fragment_state(u16::from(index.wrapping_add(1)), 1);
                        let (result, mut pending, _) =
                            assert_mct_fragment_case(&parser, &first, &[other], &[], 13);
                        assert_eq!(result, Ok(None));
                        pending.push(raw_mct_fragment_state(u16::from(index.wrapping_add(2)), 0));
                        let next = raw_mct_fragment_payload(descriptor, 1, 0, &data[split..]);
                        let (result, remaining, completed) = assert_mct_fragment_case(
                            &parser,
                            &next,
                            &pending,
                            &[index, 0, index],
                            usize::MAX,
                        );
                        assert_eq!(remaining, vec![pending[0].clone(), pending[2].clone()]);
                        match reference_mct_array(&payload, &limits, 13) {
                            Ok(array) => {
                                assert_eq!(result, Ok(Some(array)));
                                assert_eq!(completed, vec![index, 0, index, index]);
                            }
                            Err(error) => {
                                assert_eq!(result, Err(error));
                                assert_eq!(completed, vec![index, 0, index]);
                            }
                        }
                        splits += 1;
                    }
                }
            }
        }
    }
    assert_eq!(splits, 1_278);
    let good = raw_mct_array_payload(0x0d07, &[0x3ff0000000000000, 0x8000000000000000]);
    let bad = raw_mct_array_payload(0x0909, &[0x3f800000, 0x7fc00000]);
    let first = raw_mct_fragment_payload(0x0d07, 0, 1, &good[6..11]);
    let next = raw_mct_fragment_payload(0x0d07, 1, 0, &good[11..]);
    let bad_first = raw_mct_fragment_payload(0x0909, 0, 1, &bad[6..9]);
    let bad_next = raw_mct_fragment_payload(0x0909, 1, 0, &bad[9..]);
    let mut input = segment(MCT, &first);
    input.extend(segment(MCT, &next));
    let bad_offset = input.len();
    input.extend(segment(MCT, &bad_first));
    input.extend(segment(MCT, &bad_next));
    let mut reader = new_parser(&input, &limits).unwrap();
    let mut pending = Vec::new();
    let mut completed = Vec::new();
    let raw = reader.read_segment().unwrap();
    assert_eq!(
        reader.consume_mct_fragment(raw, &mut pending, &mut completed),
        Ok(None)
    );
    let raw = reader.read_segment().unwrap();
    assert_eq!(
        reader.consume_mct_fragment(raw, &mut pending, &mut completed),
        Ok(Some(reference_mct_array(&good, &limits, 0).unwrap()))
    );
    let raw = reader.read_segment().unwrap();
    assert_eq!(
        reader.consume_mct_fragment(raw, &mut pending, &mut completed),
        Ok(None)
    );
    let raw = reader.read_segment().unwrap();
    assert_eq!(
        reader.consume_mct_fragment(raw, &mut pending, &mut completed),
        Err(DecodeError::MalformedInput {
            offset: bad_offset as u64,
            kind: MalformedKind::InvalidTransform,
        })
    );
    assert!(pending.is_empty());
    assert_eq!(completed, vec![7]);
    assert_eq!((reader.position, reader.work_units), (input.len(), 4));
    assert!(core::ptr::eq(reader.input.as_ptr(), input.as_ptr()));
}

#[test]
fn actual_mct_fragment_lookup_caps_and_overflow_preserve_raw_prior_state() {
    let mut lookups = 0;
    for index in 0..=u8::MAX {
        for indices in [
            vec![],
            vec![index],
            vec![index.wrapping_add(1)],
            vec![0, index, 255, index],
            vec![255, 0],
        ] {
            let pending: Vec<MctFragment> = indices
                .iter()
                .enumerate()
                .map(|(variant, value)| raw_mct_fragment_state(0xf000 | u16::from(*value), variant))
                .collect();
            assert_eq!(
                find_mct_fragment(&pending, index),
                pending
                    .iter()
                    .position(|state| state.descriptor.to_be_bytes()[1] == index)
            );
            lookups += 1;
        }
    }
    assert_eq!(lookups, 1_280);
    let mut bounds = 0;
    for cap in [0_u16, 1, 2, 3, 255, u16::MAX] {
        let limits = mcc_record_test_limits(cap);
        let parser = new_parser(&[], &limits).unwrap();
        let maximum = u128::from(cap).pow(2) * 8;
        let lengths = if maximum <= 72 {
            vec![0, maximum as usize, maximum as usize + 1]
        } else {
            vec![0, 1, 73]
        };
        for length in &lengths {
            for final_index in [0, 1, 7, 8, u16::MAX - 1, u16::MAX] {
                let bytes = raw_mct_fragment_payload(7, 0, final_index, &vec![0; *length]);
                let _ = assert_mct_fragment_case(&parser, &bytes, &[], &[], usize::MAX);
                bounds += 1;
            }
            for next in [1, u16::MAX - 1, u16::MAX] {
                for tail in [0, 1, 8] {
                    let pending = [MctFragment {
                        descriptor: 7,
                        next_index: next,
                        final_index: u16::MAX,
                        offset: 17,
                        data: vec![0; *length],
                    }];
                    let bytes = raw_mct_fragment_payload(7, next, 0, &vec![0; tail]);
                    let _ = assert_mct_fragment_case(&parser, &bytes, &pending, &[7], usize::MAX);
                    bounds += 1;
                }
            }
        }
    }
    assert_eq!(bounds, 270);
    let bytes = raw_mct_fragment_payload(7, 0, 1, &[]);
    let mut component_words = 0;
    for cap in 0..=u16::MAX {
        let limits = mcc_record_test_limits(cap);
        let parser = new_parser(&[], &limits).unwrap();
        let mut pending = Vec::new();
        let actual = parser.prepare_mct_fragment(
            Segment {
                marker: MCT,
                offset: 13,
                payload: &bytes,
            },
            &mut pending,
            &[],
        );
        let maximum = u64::try_from(u128::from(cap).pow(2) * 8).unwrap();
        if cap == 0 {
            assert_eq!(
                actual,
                Err(DecodeError::LimitExceeded {
                    resource: Resource::TransformElements,
                    limit: 0,
                    actual: 2,
                })
            );
            assert!(pending.is_empty());
        } else {
            assert_eq!(actual, Ok((0, maximum)));
            assert_eq!(pending.len(), 1);
            assert_eq!(pending[0].descriptor, 7);
        }
        component_words += 1;
    }
    assert_eq!(component_words, 65_536);
    let mut finals = 0;
    for cap in [0, 1, 2] {
        let limits = mcc_record_test_limits(cap);
        let parser = new_parser(&[], &limits).unwrap();
        for final_index in 0..=u16::MAX {
            let bytes = raw_mct_fragment_payload(7, 0, final_index, &[]);
            let _ = assert_mct_fragment_case(&parser, &bytes, &[], &[], 13);
            finals += 1;
        }
    }
    assert_eq!(finals, 196_608);
}

fn reference_prepare_mcc_fragment(
    bytes: &[u8],
    components: u16,
    pending: &mut Vec<MccFragment>,
    completed: &[u8],
    offset: usize,
) -> Result<(usize, u64), DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    if bytes.len() < 3 || bytes[2] == 0 {
        return Err(malformed(MalformedKind::InvalidTransform));
    }
    let fragment = u16::from_be_bytes([bytes[0], bytes[1]]);
    let index = bytes[2];
    let wide = u128::from(components);
    let maximum = u64::try_from(wide * (wide * 4 + 12)).unwrap();
    let found = pending.iter().position(|state| state.record_index == index);
    if fragment == 0 {
        if bytes.len() < 7 || found.is_some() || completed.contains(&index) {
            return Err(malformed(MalformedKind::InvalidTransform));
        }
        let final_index = u16::from_be_bytes([bytes[3], bytes[4]]);
        if u64::from(final_index) + 1 > maximum {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TransformElements,
                limit: maximum,
                actual: u64::from(final_index) + 1,
            });
        }
        if bytes[7..].len() as u64 > maximum {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TransformElements,
                limit: maximum,
                actual: bytes[7..].len() as u64,
            });
        }
        let active = pending.len();
        pending.push(MccFragment {
            record_index: index,
            next_index: 1,
            final_index,
            collection_count: u16::from_be_bytes([bytes[5], bytes[6]]),
            offset,
            data: bytes[7..].to_vec(),
        });
        Ok((active, maximum))
    } else {
        let active = found.ok_or_else(|| malformed(MalformedKind::InvalidTransform))?;
        let state = &mut pending[active];
        if fragment != state.next_index || fragment > state.final_index {
            return Err(malformed(MalformedKind::InvalidTransform));
        }
        state.data = [state.data.as_slice(), &bytes[3..]].concat();
        if state.data.len() as u64 > maximum {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TransformElements,
                limit: maximum,
                actual: state.data.len() as u64,
            });
        }
        if state.next_index == u16::MAX {
            return Err(malformed(MalformedKind::ArithmeticOverflow));
        }
        state.next_index += 1;
        Ok((active, maximum))
    }
}

fn reference_consume_mcc_fragment(
    bytes: &[u8],
    components: u16,
    limits: &ResourceLimits,
    pending: &mut Vec<MccFragment>,
    completed: &mut Vec<u8>,
    offset: usize,
) -> Result<Option<MctRecord>, DecodeError> {
    let (active, maximum) =
        reference_prepare_mcc_fragment(bytes, components, pending, completed, offset)?;
    if u32::from(pending[active].next_index) != u32::from(pending[active].final_index) + 1 {
        return Ok(None);
    }
    let state = pending[active].clone();
    let last = pending.pop().unwrap();
    if active < pending.len() {
        pending[active] = last;
    }
    if state.data.len() as u64 > maximum {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::TransformElements,
            limit: maximum,
            actual: state.data.len() as u64,
        });
    }
    let mut payload = vec![0, 0, state.record_index, 0, 0];
    payload.extend(state.collection_count.to_be_bytes());
    payload.extend(&state.data);
    let record = reference_mcc_record(&payload, components, limits, state.offset)?;
    completed.push(bytes[2]);
    Ok(Some(record))
}

fn raw_mcc_fragment_state(index: u8, variant: usize) -> MccFragment {
    MccFragment {
        record_index: index,
        next_index: if variant == 0 { 0 } else { u16::MAX },
        final_index: if variant == 0 { u16::MAX } else { 0 },
        collection_count: u16::MAX,
        offset: usize::MAX - variant,
        data: vec![255, variant as u8, 17],
    }
}

fn raw_mcc_first_fragment(index: u8, final_index: u16, count: u16, data: &[u8]) -> Vec<u8> {
    let mut bytes = vec![0, 0, index];
    bytes.extend(final_index.to_be_bytes());
    bytes.extend(count.to_be_bytes());
    bytes.extend(data);
    bytes
}

fn raw_mcc_next_fragment(index: u8, fragment: u16, data: &[u8]) -> Vec<u8> {
    let mut bytes = fragment.to_be_bytes().to_vec();
    bytes.push(index);
    bytes.extend(data);
    bytes
}

fn assert_mcc_fragment_case(
    parser: &Parser<'_>,
    bytes: &[u8],
    components: u16,
    pending: &[MccFragment],
    completed: &[u8],
    offset: usize,
) -> (
    Result<Option<MctRecord>, DecodeError>,
    Vec<MccFragment>,
    Vec<u8>,
) {
    let mut actual_prepared = pending.to_vec();
    let mut expected_prepared = pending.to_vec();
    let expected = reference_prepare_mcc_fragment(
        bytes,
        components,
        &mut expected_prepared,
        completed,
        offset,
    );
    assert_eq!(
        parser.prepare_mcc_fragment(
            Segment {
                marker: 0x1234,
                offset,
                payload: bytes
            },
            components,
            &mut actual_prepared,
            completed
        ),
        expected
    );
    assert_eq!(actual_prepared, expected_prepared);
    let mut actual_pending = pending.to_vec();
    let mut expected_pending = pending.to_vec();
    let mut actual_completed = completed.to_vec();
    let mut expected_completed = completed.to_vec();
    let expected = reference_consume_mcc_fragment(
        bytes,
        components,
        parser.limits,
        &mut expected_pending,
        &mut expected_completed,
        offset,
    );
    let actual = parser.consume_mcc_fragment(
        Segment {
            marker: 0x1234,
            offset,
            payload: bytes,
        },
        components,
        &mut actual_pending,
        &mut actual_completed,
    );
    assert_eq!(actual, expected);
    assert_eq!(actual_pending, expected_pending);
    assert_eq!(actual_completed, expected_completed);
    (actual, actual_pending, actual_completed)
}

#[test]
fn actual_mcc_fragments_preserve_all_index_headers_first_matches_and_partial_failure_commits() {
    let limits = ResourceLimits::HARDENED;
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let mut headers = 0;
    for fragment in 0..=u16::MAX {
        for record in [0, 7, 255] {
            let [first, second] = fragment.to_be_bytes();
            let bytes = [first, second, record, 0, 1, 0, 1];
            for components in [0, 1, 64] {
                for offset in [0, usize::MAX] {
                    let _ = assert_mcc_fragment_case(&parser, &bytes, components, &[], &[], offset);
                    headers += 1;
                }
            }
        }
    }
    assert_eq!(headers, 1_179_648);
    let mut initials = 0;
    for components in [0, 1, 2, 64, u16::MAX] {
        for final_index in [0, 1, 15, 16, u16::MAX - 1, u16::MAX] {
            for count in [0, 1, 64, u16::MAX] {
                for length in [0, 1, 15, 16, 17, 72, 73] {
                    let bytes = raw_mcc_first_fragment(7, final_index, count, &vec![0; length]);
                    for completed in [vec![], vec![7], vec![0, 7, 255, 7]] {
                        for pending in [vec![], vec![raw_mcc_fragment_state(7, 0)]] {
                            for offset in [0, usize::MAX] {
                                let _ = assert_mcc_fragment_case(
                                    &parser, &bytes, components, &pending, &completed, offset,
                                );
                                initials += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(initials, 10_080);
    let mut continuations = 0;
    for components in [0, 1, 2, 64, u16::MAX] {
        for next in [0, 1, 2, u16::MAX - 1, u16::MAX] {
            for final_index in [0, 1, 2, u16::MAX - 1, u16::MAX] {
                for fragment in [0, 1, 2, u16::MAX] {
                    for old_length in [0, 1, 15, 16, 17] {
                        for tail_length in [0, 1, 17] {
                            let bytes = raw_mcc_next_fragment(7, fragment, &vec![0; tail_length]);
                            for mode in 0..3 {
                                let active = MccFragment {
                                    record_index: 7,
                                    next_index: next,
                                    final_index,
                                    collection_count: 1,
                                    offset: 13,
                                    data: vec![0; old_length],
                                };
                                let pending = match mode {
                                    0 => vec![active],
                                    1 => vec![
                                        raw_mcc_fragment_state(8, 0),
                                        active,
                                        raw_mcc_fragment_state(9, 1),
                                    ],
                                    _ => vec![
                                        raw_mcc_fragment_state(8, 0),
                                        active,
                                        raw_mcc_fragment_state(7, 1),
                                    ],
                                };
                                for completed in [vec![], vec![7], vec![0, 7, 255, 7]] {
                                    for offset in [0, usize::MAX] {
                                        let _ = assert_mcc_fragment_case(
                                            &parser, &bytes, components, &pending, &completed,
                                            offset,
                                        );
                                        continuations += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(continuations, 135_000);
    for length in 0..=7 {
        for byte in [0, 255] {
            let _ = assert_mcc_fragment_case(
                &parser,
                &vec![byte; length],
                1,
                &[raw_mcc_fragment_state(7, 1)],
                &[7, 7],
                usize::MAX,
            );
        }
    }
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2)
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));
}

#[test]
fn actual_mcc_fragments_compose_real_records_swap_order_offsets_and_completed_policy() {
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let collection = raw_mcc_collection_bytes(0, (false, false), &[0], &[0], 0x010001, None);
    let mut sequences = 0;
    for components in [1, 2, 64] {
        for split in 0..=collection.len() {
            let initial = raw_mcc_first_fragment(7, 1, 1, &collection[..split]);
            let pending = vec![raw_mcc_fragment_state(8, 0), raw_mcc_fragment_state(9, 1)];
            let (result, pending, completed) =
                assert_mcc_fragment_case(&parser, &initial, components, &pending, &[3, 3], 11);
            assert_eq!(result, Ok(None));
            let continuation = raw_mcc_next_fragment(7, 1, &collection[split..]);
            let (result, pending, completed) = assert_mcc_fragment_case(
                &parser,
                &continuation,
                components,
                &pending,
                &completed,
                77,
            );
            assert!(result.unwrap().is_some());
            assert_eq!(pending.len(), 2);
            assert_eq!(completed, vec![3, 3, 7]);
            sequences += 1;
        }
    }
    assert_eq!(sequences, 33);
    for offset in [0, usize::MAX] {
        let active = MccFragment {
            record_index: 7,
            next_index: 1,
            final_index: 1,
            collection_count: 1,
            offset,
            data: collection[..3].to_vec(),
        };
        let pending = [
            raw_mcc_fragment_state(8, 0),
            active,
            raw_mcc_fragment_state(9, 1),
        ];
        let bytes = raw_mcc_next_fragment(7, 1, &collection[3..]);
        let (result, next, completed) =
            assert_mcc_fragment_case(&parser, &bytes, 1, &pending, &[7], 77);
        assert!(result.unwrap().is_some());
        assert_eq!(
            next.iter()
                .map(|state| state.record_index)
                .collect::<Vec<_>>(),
            vec![8, 9]
        );
        assert_eq!(completed, vec![7, 7]);
        let mut bad = pending.to_vec();
        bad[1].data = vec![2];
        let (result, next, completed) = assert_mcc_fragment_case(
            &parser,
            &raw_mcc_next_fragment(7, 1, &[]),
            1,
            &bad,
            &[7],
            77,
        );
        assert_eq!(
            result,
            Err(DecodeError::MalformedInput {
                offset: offset as u64,
                kind: MalformedKind::InvalidTransform
            })
        );
        assert_eq!(
            next.iter()
                .map(|state| state.record_index)
                .collect::<Vec<_>>(),
            vec![8, 9]
        );
        assert_eq!(completed, vec![7]);
        let mut limited = bad.clone();
        limited[1].collection_count = 65;
        let (result, next, completed) = assert_mcc_fragment_case(
            &parser,
            &raw_mcc_next_fragment(7, 1, &[]),
            1,
            &limited,
            &[],
            77,
        );
        assert_eq!(
            result,
            Err(DecodeError::LimitExceeded {
                resource: Resource::TransformElements,
                limit: 64,
                actual: 65
            })
        );
        assert_eq!(next.len(), 2);
        assert!(completed.is_empty());
    }
    let initial = raw_mcc_first_fragment(7, 1, 1, &collection[..4]);
    let continuation = raw_mcc_next_fragment(7, 1, &collection[4..]);
    let mut input = segment(MCC, &initial);
    input.extend(segment(MCC, &continuation));
    let mut reader = new_parser(&input, &limits).unwrap();
    let mut pending = vec![];
    let mut completed = vec![];
    let raw = reader.read_segment().unwrap();
    assert_eq!(
        reader.consume_mcc_fragment(raw, 1, &mut pending, &mut completed),
        Ok(None)
    );
    let raw = reader.read_segment().unwrap();
    let record = reader
        .consume_mcc_fragment(raw, 1, &mut pending, &mut completed)
        .unwrap()
        .unwrap();
    assert_eq!(record.index, 7);
    assert_eq!(record.collections[0].input_components, vec![0]);
    assert_eq!(record.collections[0].output_components, vec![0]);
    assert!(pending.is_empty());
    assert_eq!(completed, vec![7]);
    assert_eq!((reader.position, reader.work_units), (input.len(), 2));
    assert!(core::ptr::eq(reader.input.as_ptr(), input.as_ptr()));
}

#[test]
fn actual_mcc_fragment_lookup_and_component_byte_bounds_preserve_raw_prior_state() {
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let mut lookups = 0;
    for index in 0..=u8::MAX {
        for indices in [
            vec![],
            vec![index],
            vec![index.wrapping_add(1)],
            vec![0, index, 255, index],
            vec![255, 0],
        ] {
            let pending: Vec<MccFragment> = indices
                .iter()
                .enumerate()
                .map(|(variant, value)| raw_mcc_fragment_state(*value, variant))
                .collect();
            assert_eq!(
                find_mcc_fragment(&pending, index),
                pending.iter().position(|state| state.record_index == index)
            );
            assert_eq!(u8_list_contains(&indices, index), indices.contains(&index));
            lookups += 1;
        }
    }
    assert_eq!(lookups, 1_280);
    let collection = raw_mcc_collection_bytes(0, (false, false), &[0], &[0], 0x010001, None);
    let mut bounds = 0;
    for components in [0_u16, 1, 2, 3, 64, u16::MAX] {
        let c = u128::from(components);
        let maximum = usize::try_from(c * (c * 4 + 12)).unwrap();
        let lengths: Vec<usize> = if maximum <= 72 {
            vec![0, maximum, maximum + 1]
        } else {
            vec![0, 1, 73]
        };
        for length in lengths {
            for final_index in [0, 1, 15, 16, u16::MAX - 1, u16::MAX] {
                let bytes = raw_mcc_first_fragment(7, final_index, 1, &vec![0; length]);
                let _ = assert_mcc_fragment_case(&parser, &bytes, components, &[], &[], usize::MAX);
                bounds += 1;
            }
        }
        for next in [u16::MAX - 1, u16::MAX] {
            let pending = [MccFragment {
                record_index: 7,
                next_index: next,
                final_index: u16::MAX,
                collection_count: 1,
                offset: 13,
                data: collection.clone(),
            }];
            let bytes = raw_mcc_next_fragment(7, next, &[0]);
            let _ =
                assert_mcc_fragment_case(&parser, &bytes, components, &pending, &[7], usize::MAX);
            bounds += 1;
        }
    }
    assert_eq!(bounds, 120);
}

fn reference_mcc_collection(
    bytes: &[u8],
    components: u16,
    start: usize,
    offset: usize,
) -> Result<(MctCollectionReference, usize), DecodeError> {
    let malformed = || DecodeError::MalformedInput {
        offset: offset as u64,
        kind: MalformedKind::InvalidTransform,
    };
    let kind = *bytes.get(start).ok_or_else(malformed)?;
    if ![0, 1, 3].contains(&kind) {
        return Err(malformed());
    }
    let mut position = start + 1;
    let inputs = reference_mcc_component_list(bytes, &mut position, components, offset)?;
    let outputs = reference_mcc_component_list(bytes, &mut position, components, offset)?;
    if inputs.is_empty() || position as u128 + 3 > bytes.len() as u128 {
        return Err(malformed());
    }
    let word = u32::from_be_bytes([0, bytes[position], bytes[position + 1], bytes[position + 2]]);
    position += 3;
    let transform = if kind <= 1 {
        if word >= 131072 || inputs.len() != outputs.len() || (kind == 0 && inputs != outputs) {
            return Err(malformed());
        }
        MctCollectionReferenceTransform::Array {
            kind: if kind == 0 {
                MctArrayKind::Dependency
            } else {
                MctArrayKind::Decorrelation
            },
            reversible: word / 65536 == 1,
            transform_index: (word % 256) as u8,
            offset_index: (word / 256 % 256) as u8,
        }
    } else {
        let middle = word / 256 % 256;
        if word >= 4194304
            || middle != 0
            || inputs.len() != outputs.len()
            || position as u128 + 4 > bytes.len() as u128
        {
            return Err(malformed());
        }
        let wavelet = match word % 256 {
            0 => MctWaveletType::Irreversible9x7,
            1 => MctWaveletType::Reversible5x3,
            _ => return Err(malformed()),
        };
        let levels = (word / 65536) as u8;
        if levels > 32 {
            return Err(malformed());
        }
        let component_offset =
            i32::from_be_bytes(bytes[position..position + 4].try_into().unwrap());
        position += 4;
        MctCollectionReferenceTransform::Wavelet(MctWavelet {
            transform: wavelet,
            levels,
            component_offset,
        })
    };
    Ok((
        MctCollectionReference {
            input_components: inputs,
            output_components: outputs,
            transform,
        },
        position,
    ))
}

fn reference_mcc_parallel(
    collections: &[MctCollectionReference],
    offset: usize,
) -> Result<(), DecodeError> {
    let mut previous: Vec<std::collections::BTreeSet<u16>> = Vec::new();
    for collection in collections {
        let values: std::collections::BTreeSet<_> = collection
            .input_components
            .iter()
            .chain(&collection.output_components)
            .copied()
            .collect();
        if previous.iter().any(|prior| !values.is_disjoint(prior)) {
            return Err(DecodeError::MalformedInput {
                offset: offset as u64,
                kind: MalformedKind::InvalidTransform,
            });
        }
        previous.push(values);
    }
    Ok(())
}

fn reference_mcc_record(
    bytes: &[u8],
    components: u16,
    limits: &ResourceLimits,
    offset: usize,
) -> Result<MctRecord, DecodeError> {
    let malformed = || DecodeError::MalformedInput {
        offset: offset as u64,
        kind: MalformedKind::InvalidTransform,
    };
    if bytes.len() < 7 || bytes[..2] != [0, 0] || bytes[3..5] != [0, 0] {
        return Err(malformed());
    }
    let index = bytes[2];
    let count = u16::from_be_bytes([bytes[5], bytes[6]]);
    if index == 0 || count == 0 {
        return Err(malformed());
    }
    if count > limits.maximum_components() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::TransformElements,
            limit: u64::from(limits.maximum_components()),
            actual: u64::from(count),
        });
    }
    let mut position = 7;
    let mut collections = Vec::new();
    for _ in 0..count {
        let (collection, next) = reference_mcc_collection(bytes, components, position, offset)?;
        position = next;
        collections.push(collection);
    }
    if position != bytes.len() {
        return Err(malformed());
    }
    reference_mcc_parallel(&collections, offset)?;
    Ok(MctRecord { index, collections })
}

fn raw_mcc_collection_bytes(
    kind: u8,
    wide: (bool, bool),
    inputs: &[u16],
    outputs: &[u16],
    word: u32,
    component_offset: Option<u32>,
) -> Vec<u8> {
    let mut bytes = vec![kind];
    bytes
        .extend(&raw_mcc_reference_list(wide.0, u16::try_from(inputs.len()).unwrap(), inputs)[1..]);
    bytes.extend(
        &raw_mcc_reference_list(wide.1, u16::try_from(outputs.len()).unwrap(), outputs)[1..],
    );
    bytes.extend(&word.to_be_bytes()[1..]);
    if let Some(value) = component_offset {
        bytes.extend(value.to_be_bytes());
    }
    bytes
}

fn raw_mcc_record_bytes(index: u8, collections: &[Vec<u8>]) -> Vec<u8> {
    let mut bytes = vec![0, 0, index, 0, 0];
    bytes.extend(u16::try_from(collections.len()).unwrap().to_be_bytes());
    for collection in collections {
        bytes.extend(collection);
    }
    bytes
}

fn assert_mcc_collection_case(
    parser: &Parser<'_>,
    bytes: &[u8],
    components: u16,
    start: usize,
    offset: usize,
) {
    assert_eq!(
        parser.decode_mcc_collection(
            Segment {
                marker: 0x1234,
                offset,
                payload: bytes
            },
            components,
            start
        ),
        reference_mcc_collection(bytes, components, start, offset)
    );
}

fn assert_mcc_record_case(parser: &Parser<'_>, bytes: &[u8], components: u16, offset: usize) {
    assert_eq!(
        parser.parse_mcc(
            Segment {
                marker: 0x1234,
                offset,
                payload: bytes
            },
            components
        ),
        reference_mcc_record(bytes, components, parser.limits, offset)
    );
}

fn mcc_record_test_limits(cap: u16) -> ResourceLimits {
    let base = ResourceLimits::HARDENED;
    base.with_geometry_limits_for_test(
        cap,
        base.maximum_width(),
        base.maximum_height(),
        base.maximum_pixels(),
        base.maximum_tiles(),
    )
}

#[test]
fn actual_mcc_collections_preserve_all_kind_bytes_flags_routes_wavelets_and_offsets() {
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let widths = [(false, false), (true, false), (false, true), (true, true)];
    let mut kinds = 0;
    for kind in 0..=u8::MAX {
        for components in [0, 1, 2, 257, u16::MAX] {
            for wide in widths {
                let source = raw_mcc_collection_bytes(
                    kind,
                    wide,
                    &[0, 1],
                    &[0, 1],
                    0x010201,
                    Some(0x80000000),
                );
                for mode in 0..4 {
                    let mut bytes = source.clone();
                    let start = match mode {
                        1 => {
                            bytes.insert(0, 0xa5);
                            1
                        }
                        2 => bytes.len(),
                        3 => usize::MAX,
                        _ => 0,
                    };
                    for offset in [0, usize::MAX] {
                        assert_mcc_collection_case(&parser, &bytes, components, start, offset);
                        kinds += 1;
                    }
                }
            }
        }
    }
    assert_eq!(kinds, 40_960);
    let mut flags = 0;
    for kind in [0, 1, 3] {
        for word in [0, 0x010201, 0x200001] {
            for wide in [false, true] {
                let source = raw_mcc_collection_bytes(
                    kind,
                    (wide, wide),
                    &[0, 1],
                    &[0, 1],
                    word,
                    Some(0x80000000),
                );
                let descriptor =
                    1 + 2 + 2 * if wide { 2 } else { 1 } + 2 + 2 * if wide { 2 } else { 1 };
                for byte in 0..3 {
                    for value in 0..=u8::MAX {
                        let mut bytes = source.clone();
                        bytes[descriptor + byte] = value;
                        for offset in [0, usize::MAX] {
                            assert_mcc_collection_case(&parser, &bytes, 257, 0, offset);
                            flags += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(flags, 27_648);
    let routes = [
        vec![],
        vec![0],
        vec![1],
        vec![0, 1],
        vec![1, 0],
        vec![0, 0],
        vec![256],
    ];
    let mut lists = 0;
    for inputs in &routes {
        for outputs in &routes {
            for wide in widths {
                for kind in [0, 1, 3] {
                    for components in [0, 1, 2, 257, u16::MAX] {
                        for word in if kind == 3 {
                            [0, 0x200001]
                        } else {
                            [0, 0x010201]
                        } {
                            let source = raw_mcc_collection_bytes(
                                kind,
                                wide,
                                inputs,
                                outputs,
                                word,
                                if kind == 3 { Some(u32::MAX) } else { None },
                            );
                            for variant in 0..3 {
                                let mut bytes = source.clone();
                                if variant == 0 {
                                    bytes.pop();
                                } else if variant == 2 {
                                    bytes.push(255);
                                }
                                for offset in [0, usize::MAX] {
                                    assert_mcc_collection_case(
                                        &parser, &bytes, components, 0, offset,
                                    );
                                    lists += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(lists, 35_280);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2)
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));
}

#[test]
fn actual_mcc_records_preserve_header_limits_terminal_parallel_order_and_all_fields() {
    let input = [0xa5, 0x5a];
    let mut counts = 0;
    for cap in [1, 64] {
        let limits = mcc_record_test_limits(cap);
        let mut parser = new_parser(&input, &limits).unwrap();
        parser.position = usize::MAX;
        for count in 0..=u16::MAX {
            let [first, second] = count.to_be_bytes();
            for offset in [0, usize::MAX] {
                assert_mcc_record_case(&parser, &[0, 0, 1, 0, 0, first, second], 2, offset);
                counts += 1;
            }
        }
    }
    assert_eq!(counts, 262_144);
    let mut headers = 0;
    for index in 0..=u8::MAX {
        for z in [0_u16, 1, u16::MAX] {
            for y in [0_u16, 1, u16::MAX] {
                for count in [0_u16, 1, 2, 64, 65, u16::MAX] {
                    let mut bytes = z.to_be_bytes().to_vec();
                    bytes.push(index);
                    bytes.extend(y.to_be_bytes());
                    bytes.extend(count.to_be_bytes());
                    for cap in [1, 2, 64] {
                        let limits = mcc_record_test_limits(cap);
                        let parser = new_parser(&input, &limits).unwrap();
                        for components in [0, 2, 257] {
                            for offset in [0, usize::MAX] {
                                assert_mcc_record_case(&parser, &bytes, components, offset);
                                headers += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(headers, 248_832);
    let pool = [
        raw_mcc_collection_bytes(0, (false, false), &[0], &[0], 1, None),
        raw_mcc_collection_bytes(0, (true, true), &[0], &[0], 0x010001, None),
        raw_mcc_collection_bytes(1, (false, true), &[0, 1], &[1, 0], 0x010201, None),
        raw_mcc_collection_bytes(3, (false, false), &[2], &[2], 0, Some(0x80000000)),
        raw_mcc_collection_bytes(3, (true, true), &[2], &[2], 0x200001, Some(0x7fffffff)),
        raw_mcc_collection_bytes(2, (false, false), &[0], &[0], 0, None),
        raw_mcc_collection_bytes(1, (true, false), &[0], &[0, 1], 1, None),
        raw_mcc_collection_bytes(1, (false, false), &[], &[0], 1, None),
    ];
    let mut sequences = vec![vec![]];
    for first in &pool {
        sequences.push(vec![first.clone()]);
        for second in &pool {
            sequences.push(vec![first.clone(), second.clone()]);
        }
    }
    assert_eq!(sequences.len(), 73);
    let mut records = 0;
    for collections in sequences {
        let source = raw_mcc_record_bytes(7, &collections);
        for components in [0, 1, 2, 3, 257, u16::MAX] {
            for cap in [1, 2, 64] {
                let limits = mcc_record_test_limits(cap)
                    .with_maximum_work_units(0)
                    .unwrap();
                let mut parser = new_parser(&input, &limits).unwrap();
                parser.position = usize::MAX;
                parser.work_units = u64::MAX;
                parser.packet_length_bytes = u64::MAX - 1;
                parser.packet_lengths = u64::MAX - 2;
                for variant in 0..3 {
                    let mut bytes = source.clone();
                    if variant == 0 {
                        bytes.pop();
                    } else if variant == 2 {
                        bytes.push(0);
                    }
                    for offset in [0, usize::MAX] {
                        assert_mcc_record_case(&parser, &bytes, components, offset);
                        assert_eq!(
                            (
                                parser.position,
                                parser.work_units,
                                parser.packet_length_bytes,
                                parser.packet_lengths
                            ),
                            (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2)
                        );
                        assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
                        assert!(core::ptr::eq(parser.limits, &limits));
                        records += 1;
                    }
                }
            }
        }
    }
    assert_eq!(records, 7_884);
}

#[test]
fn actual_mcc_parallel_and_signed_offsets_match_independent_sets_and_full_width_reference() {
    let mut signed = 0;
    let mut overlaps = 0;
    for half in 0..=u16::MAX {
        for bits in [
            u32::from(half),
            u32::from(half) << 16,
            (u32::from(half) << 16) | 65535,
            (u32::from(half) << 16) | u32::from(half.wrapping_mul(31337)),
        ] {
            assert_eq!(
                signed_u32(bits),
                i64::from(i32::from_be_bytes(bits.to_be_bytes()))
            );
            signed += 1;
        }
        let left = [half, half ^ u16::MAX];
        let left_set: std::collections::BTreeSet<_> = left.into_iter().collect();
        for right in [
            vec![],
            vec![half],
            vec![half.wrapping_add(1)],
            vec![0, u16::MAX],
        ] {
            let right_set: std::collections::BTreeSet<_> = right.iter().copied().collect();
            assert_eq!(
                component_lists_overlap(&left, &right),
                !left_set.is_disjoint(&right_set)
            );
            overlaps += 1;
        }
    }
    assert_eq!(signed, 262_144);
    assert_eq!(overlaps, 262_144);
    let routes = [
        vec![],
        vec![0],
        vec![1],
        vec![0, 1],
        vec![u16::MAX],
        vec![0, 0],
    ];
    let mut pool = Vec::new();
    for input in &routes {
        for output in &routes {
            pool.push(MctCollectionReference {
                input_components: input.clone(),
                output_components: output.clone(),
                transform: if pool.len().is_multiple_of(2) {
                    MctCollectionReferenceTransform::Array {
                        kind: MctArrayKind::Offset,
                        reversible: true,
                        transform_index: 0,
                        offset_index: 255,
                    }
                } else {
                    MctCollectionReferenceTransform::Wavelet(MctWavelet {
                        transform: MctWaveletType::Reversible5x3,
                        levels: u8::MAX,
                        component_offset: i32::MIN,
                    })
                },
            });
        }
    }
    assert_eq!(pool.len(), 36);
    let mut parallels = 0;
    for first in &pool {
        for second in &pool {
            for offset in [0, usize::MAX] {
                let values = [first.clone(), second.clone()];
                assert_eq!(
                    validate_parallel_collections(&values, offset),
                    reference_mcc_parallel(&values, offset)
                );
                parallels += 1;
            }
        }
    }
    assert_eq!(parallels, 2_592);
    for offset in [0, usize::MAX] {
        assert_eq!(validate_parallel_collections(&[], offset), Ok(()));
        for first in &pool {
            assert_eq!(
                validate_parallel_collections(core::slice::from_ref(first), offset),
                Ok(())
            );
            let values = [pool[0].clone(), first.clone(), first.clone()];
            assert_eq!(
                validate_parallel_collections(&values, offset),
                reference_mcc_parallel(&values, offset)
            );
        }
    }
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let mut offsets = 0;
    for bits in [0, 1, 0x7fffffff, 0x80000000, 0x80000001, u32::MAX] {
        for levels in [0_u32, 1, 31, 32, 33, 63] {
            for kind in [0, 1, 2, 255] {
                for reserved in [0, 1] {
                    for wide in [false, true] {
                        let word = (levels << 16) | (reserved << 8) | kind;
                        let bytes =
                            raw_mcc_collection_bytes(3, (wide, wide), &[0], &[0], word, Some(bits));
                        for offset in [0, usize::MAX] {
                            assert_mcc_collection_case(&parser, &bytes, 1, 0, offset);
                            offsets += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(offsets, 1_152);
    let good = raw_mcc_record_bytes(
        7,
        &[
            raw_mcc_collection_bytes(0, (false, true), &[0], &[0], 1, None),
            raw_mcc_collection_bytes(3, (true, false), &[1], &[1], 0x200001, Some(0x80000000)),
        ],
    );
    let bad = raw_mcc_record_bytes(
        8,
        &[
            raw_mcc_collection_bytes(1, (false, false), &[0], &[1], 1, None),
            raw_mcc_collection_bytes(3, (true, true), &[1], &[2], 0, Some(u32::MAX)),
        ],
    );
    let mut input = segment(MCC, &good);
    let bad_offset = input.len();
    input.extend(segment(MCC, &bad));
    let mut reader = new_parser(&input, &limits).unwrap();
    let raw = reader.read_segment().unwrap();
    assert_eq!(
        reader.parse_mcc(raw, 3),
        reference_mcc_record(&good, 3, &limits, 0)
    );
    let raw = reader.read_segment().unwrap();
    assert_eq!(
        reader.parse_mcc(raw, 3),
        Err(DecodeError::MalformedInput {
            offset: bad_offset as u64,
            kind: MalformedKind::InvalidTransform,
        })
    );
    assert_eq!((reader.position, reader.work_units), (input.len(), 2));
    assert!(core::ptr::eq(reader.input.as_ptr(), input.as_ptr()));
}

fn reference_mco_order(bytes: &[u8], offset: usize) -> Result<Vec<u8>, DecodeError> {
    let malformed = || DecodeError::MalformedInput {
        offset: offset as u64,
        kind: MalformedKind::InvalidTransform,
    };
    let Some(count) = bytes.first() else {
        return Err(malformed());
    };
    if bytes.len() != usize::from(*count) + 1 {
        return Err(malformed());
    }
    let order = &bytes[1..];
    let unique: std::collections::BTreeSet<_> = order.iter().copied().collect();
    if order.contains(&0) || unique.len() != order.len() {
        return Err(malformed());
    }
    Ok(order.to_vec())
}

fn reference_mcc_component_list(
    bytes: &[u8],
    position: &mut usize,
    components: u16,
    offset: usize,
) -> Result<Vec<u16>, DecodeError> {
    let malformed = || DecodeError::MalformedInput {
        offset: offset as u64,
        kind: MalformedKind::InvalidTransform,
    };
    if *position as u128 + 2 > bytes.len() as u128 {
        return Err(malformed());
    }
    let encoded = u16::from_be_bytes([bytes[*position], bytes[*position + 1]]);
    *position += 2;
    let count = encoded % 32768;
    let width = if encoded / 32768 == 0 { 1 } else { 2 };
    if count == 0 || count > components {
        return Err(malformed());
    }
    if *position as u128 + u128::from(count) * width as u128 > bytes.len() as u128 {
        return Err(malformed());
    }
    let mut references = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for _ in 0..count {
        let value = if width == 1 {
            u16::from(bytes[*position])
        } else {
            u16::from_be_bytes([bytes[*position], bytes[*position + 1]])
        };
        if value >= components || !seen.insert(value) {
            return Err(malformed());
        }
        references.push(value);
        *position += width;
    }
    Ok(references)
}

fn raw_mcc_reference_list(wide: bool, count: u16, references: &[u16]) -> Vec<u8> {
    assert!(count <= 32767);
    let encoded = count + if wide { 32768 } else { 0 };
    let mut bytes = vec![0xa5];
    bytes.extend(encoded.to_be_bytes());
    for reference in references {
        if wide {
            bytes.extend(reference.to_be_bytes());
        } else {
            bytes.push(*reference as u8);
        }
    }
    bytes
}

fn assert_mcc_reference_case(bytes: &[u8], start: usize, components: u16, offset: usize) {
    let mut actual_position = start;
    let mut expected_position = start;
    let expected = reference_mcc_component_list(bytes, &mut expected_position, components, offset);
    assert_eq!(
        parse_mcc_component_list(bytes, &mut actual_position, components, offset),
        expected
    );
    assert_eq!(actual_position, expected_position);
}

#[test]
fn actual_mco_preserves_zero_order_all_stage_pairs_and_count_frontiers() {
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let mut counts = 0;
    for count in 0..=u8::MAX {
        let mut source = vec![count];
        source.extend(1..=count);
        for variant in 0..7 {
            let mut bytes = source.clone();
            match variant {
                0 => {
                    bytes.pop();
                }
                2 => bytes.push(0),
                3 if count > 0 => bytes[1] = 0,
                4 if count > 0 => bytes[usize::from(count) / 2 + 1] = 0,
                5 if count > 0 => bytes[usize::from(count)] = 0,
                6 if count > 1 => bytes[usize::from(count)] = bytes[1],
                _ => {}
            }
            for offset in [0, usize::MAX] {
                assert_eq!(
                    parser.parse_mco(Segment {
                        marker: 0x1234,
                        offset,
                        payload: &bytes
                    }),
                    reference_mco_order(&bytes, offset)
                );
                counts += 1;
            }
        }
    }
    assert_eq!(counts, 3_584);
    let mut pairs = 0;
    for first in 0..=u8::MAX {
        for second in 0..=u8::MAX {
            let bytes = [2, first, second];
            for offset in [0, usize::MAX] {
                assert_eq!(
                    parser.parse_mco(Segment {
                        marker: 0x1234,
                        offset,
                        payload: &bytes
                    }),
                    reference_mco_order(&bytes, offset)
                );
                pairs += 1;
            }
        }
    }
    assert_eq!(pairs, 131_072);
    let mut mutations = 0;
    for count in [1_u8, 2, 3, 16] {
        let mut source = vec![count];
        source.extend((1..=count).rev());
        for position in 1..source.len() {
            for value in 0..=u8::MAX {
                let mut bytes = source.clone();
                bytes[position] = value;
                for offset in [0, usize::MAX] {
                    assert_eq!(
                        parser.parse_mco(Segment {
                            marker: 0x1234,
                            offset,
                            payload: &bytes
                        }),
                        reference_mco_order(&bytes, offset)
                    );
                    mutations += 1;
                }
            }
        }
    }
    assert_eq!(mutations, 11_264);
    assert_eq!(
        parser.parse_mco(Segment {
            marker: 0x1234,
            offset: usize::MAX,
            payload: &[0]
        }),
        Ok(vec![])
    );
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2)
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));
}

#[test]
fn actual_mcc_component_lists_preserve_all_headers_words_and_partial_cursors() {
    let mut frontiers = 0;
    for length in [0, 1, 2, 3, 8, 12] {
        for pattern in [0, 1, 0x7f, 0x80, 255] {
            let bytes = vec![pattern; length];
            for start in [0, 1, 2, 7, length, length + 1, usize::MAX - 1, usize::MAX] {
                for components in [0, 1, 64, 256, u16::MAX] {
                    for offset in [0, usize::MAX] {
                        assert_mcc_reference_case(&bytes, start, components, offset);
                        frontiers += 1;
                    }
                }
            }
        }
    }
    assert_eq!(frontiers, 2_400);
    let mut headers = 0;
    for encoded in 0..=u16::MAX {
        let [first, second] = encoded.to_be_bytes();
        let bytes = [0xa5, first, second, 0, 1, 2, 3, 4, 5, 6, 7];
        for components in [0, 1, 63, 64, 255, 256, 257, 32767, 32768, u16::MAX] {
            for offset in [0, usize::MAX] {
                assert_mcc_reference_case(&bytes, 1, components, offset);
                headers += 1;
            }
        }
    }
    assert_eq!(headers, 1_310_720);
    let mut words = 0;
    for word in 0..=u16::MAX {
        let [first, second] = word.to_be_bytes();
        let bytes = [0xa5, 0x80, 1, first, second, 255];
        for components in [0, 1, 255, 256, 257, u16::MAX] {
            for offset in [0, usize::MAX] {
                assert_mcc_reference_case(&bytes, 1, components, offset);
                words += 1;
            }
        }
    }
    assert_eq!(words, 786_432);
    let mut lists = 0;
    for wide in [false, true] {
        for count in [1_u16, 2, 3, 63, 64, 255, 256, 257] {
            for components in [0, 1, 64, 256, 257, u16::MAX] {
                for pattern in 0..5 {
                    let mut values: Vec<u16> = (0..count).collect();
                    match pattern {
                        1 => values.reverse(),
                        2 if count > 1 => values[usize::from(count) - 1] = values[0],
                        3 => values[usize::from(count) - 1] = components,
                        4 => values[0] = components,
                        _ => {}
                    }
                    let source = raw_mcc_reference_list(wide, count, &values);
                    for variant in 0..3 {
                        let mut bytes = source.clone();
                        if variant == 0 {
                            bytes.pop();
                        } else if variant == 2 {
                            bytes.extend([255, 0]);
                        }
                        for offset in [0, usize::MAX] {
                            assert_mcc_reference_case(&bytes, 1, components, offset);
                            lists += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(lists, 2_880);
}

#[test]
fn actual_transform_routing_membership_and_real_mcc_mco_callers_preserve_order() {
    let mut memberships = 0;
    for value in 0..=u16::MAX {
        for values in [
            vec![],
            vec![value],
            vec![u16::MAX],
            vec![value.wrapping_add(1)],
            vec![0, value, u16::MAX, value],
        ] {
            assert_eq!(u16_list_contains(&values, value), values.contains(&value));
            memberships += 1;
        }
    }
    assert_eq!(memberships, 327_680);
    let mut input = mco(&[7, 1]);
    input.extend(mcc(7, 2, true, 1, 2));
    let mut wide_payload = vec![0, 0, 9, 0, 0, 0, 1, 1];
    wide_payload.extend(&raw_mcc_reference_list(true, 2, &[0, 256])[1..]);
    wide_payload.extend(&raw_mcc_reference_list(true, 2, &[256, 0])[1..]);
    wide_payload.extend([1, 2, 1]);
    input.extend(segment(MCC, &wide_payload));
    let bad_offset = input.len();
    input.extend(mco(&[7, 7]));
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&input, &limits).unwrap();
    let raw = parser.read_segment().unwrap();
    assert_eq!(parser.parse_mco(raw).unwrap(), vec![7, 1]);
    let raw = parser.read_segment().unwrap();
    let record = parser.parse_mcc(raw, 2).unwrap();
    assert_eq!(record.index, 7);
    assert_eq!(record.collections.len(), 1);
    assert_eq!(record.collections[0].input_components, vec![0, 1]);
    assert_eq!(record.collections[0].output_components, vec![0, 1]);
    let raw = parser.read_segment().unwrap();
    let record = parser.parse_mcc(raw, 257).unwrap();
    assert_eq!(record.index, 9);
    assert_eq!(record.collections[0].input_components, vec![0, 256]);
    assert_eq!(record.collections[0].output_components, vec![256, 0]);
    let raw = parser.read_segment().unwrap();
    assert_eq!(
        parser.parse_mco(raw),
        Err(DecodeError::MalformedInput {
            offset: bad_offset as u64,
            kind: MalformedKind::InvalidTransform,
        })
    );
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (input.len(), 4, 0, 0)
    );
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
}

fn raw_progression_styles(components: u16, depths: &[u8]) -> ComponentCodingStyles {
    assert!(!depths.is_empty());
    let mut seed = raw_owned_tile_part_fixture(0).coding_style;
    seed.layers = u16::MAX;
    seed.decomposition_levels = u8::MAX;
    seed.code_block_width = 0;
    seed.code_block_style = u8::MAX;
    let mut styles = ComponentCodingStyles {
        components,
        styles: [seed; MAX_COMPONENTS],
    };
    for index in 0..usize::from(components).min(MAX_COMPONENTS) {
        styles.styles[index].decomposition_levels = depths[index % depths.len()];
    }
    styles
}

fn reference_progression_shape(
    layers: u16,
    styles: &ComponentCodingStyles,
    offset: usize,
) -> Result<(usize, u8), DecodeError> {
    let overflow = || DecodeError::MalformedInput {
        offset: offset as u64,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let mut active = 0_u128;
    let mut maximum = 0;
    for component in 0..usize::from(styles.components) {
        let style = styles
            .styles
            .get(component)
            .ok_or(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            })?;
        if style.decomposition_levels == u8::MAX {
            return Err(overflow());
        }
        let resolutions = style.decomposition_levels + 1;
        active += u128::from(layers) * u128::from(resolutions);
        if active > usize::MAX as u128 {
            return Err(overflow());
        }
        maximum = maximum.max(resolutions);
    }
    Ok((active as usize, maximum))
}

fn reference_progression_contains(
    record: ProgressionChange,
    component: u16,
    layer: u16,
    resolution: u8,
) -> bool {
    (0..record.layer_end).contains(&layer)
        && (record.resolution_start..record.resolution_end).contains(&resolution)
        && (record.component_start..record.component_end).contains(&component)
}

fn reference_mark_progression_resolutions(
    record: ProgressionChange,
    coordinate: (u16, u16, u8),
    owners: &mut [bool],
    progress: (usize, bool),
    offset: usize,
) -> Result<(usize, bool), DecodeError> {
    let overflow = || DecodeError::MalformedInput {
        offset: offset as u64,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let (mut linear, mut contributed) = progress;
    for resolution in 0..coordinate.2 {
        if reference_progression_contains(record, coordinate.0, coordinate.1, resolution) {
            let owner = owners.get_mut(linear).ok_or_else(overflow)?;
            if !*owner {
                *owner = true;
                contributed = true;
            }
        }
        let next = linear as u128 + 1;
        if next > usize::MAX as u128 {
            return Err(overflow());
        }
        linear = next as usize;
    }
    Ok((linear, contributed))
}

fn reference_mark_progression_layers(
    record: ProgressionChange,
    coordinate: (u16, u8),
    owners: &mut [bool],
    progress: (usize, bool),
    layers: u16,
    offset: usize,
) -> Result<(usize, bool), DecodeError> {
    let mut progress = progress;
    for layer in 0..layers {
        progress = reference_mark_progression_resolutions(
            record,
            (coordinate.0, layer, coordinate.1),
            owners,
            progress,
            offset,
        )?;
    }
    Ok(progress)
}

fn reference_mark_progression_record(
    record: ProgressionChange,
    layers: u16,
    styles: &ComponentCodingStyles,
    owners: &mut [bool],
    offset: usize,
) -> Result<bool, DecodeError> {
    let mut progress = (0, false);
    for component in 0..styles.components {
        let style =
            styles
                .styles
                .get(usize::from(component))
                .ok_or(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::InvalidCodingStyle,
                })?;
        if style.decomposition_levels == u8::MAX {
            return Err(DecodeError::MalformedInput {
                offset: offset as u64,
                kind: MalformedKind::ArithmeticOverflow,
            });
        }
        progress = reference_mark_progression_layers(
            record,
            (component, style.decomposition_levels + 1),
            owners,
            progress,
            layers,
            offset,
        )?;
    }
    Ok(progress.1)
}

fn reference_progression_admission(
    records: &[ProgressionChange],
    layers: u16,
    styles: &ComponentCodingStyles,
    limits: &ResourceLimits,
    offset: usize,
) -> Result<(), DecodeError> {
    if records.is_empty() {
        return Ok(());
    }
    let malformed = || DecodeError::MalformedInput {
        offset: offset as u64,
        kind: MalformedKind::InvalidProgressionOrderChange,
    };
    let (active, maximum) = reference_progression_shape(layers, styles, offset)?;
    let cost = records.len() as u128 * active as u128;
    if cost > u128::from(u64::MAX) {
        return Err(DecodeError::MalformedInput {
            offset: offset as u64,
            kind: MalformedKind::ArithmeticOverflow,
        });
    }
    if cost > u128::from(limits.maximum_work_units()) {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: cost as u64,
        });
    }
    let coordinates: Vec<(u16, u16, u8)> = (0..styles.components)
        .flat_map(|component| {
            let resolutions = styles.styles[usize::from(component)].decomposition_levels + 1;
            (0..layers).flat_map(move |layer| {
                (0..resolutions).map(move |resolution| (component, layer, resolution))
            })
        })
        .collect();
    assert_eq!(coordinates.len(), active);
    let mut owned = std::collections::BTreeSet::new();
    for record in records {
        if record.layer_end == 0
            || record.layer_end > layers
            || record.component_start >= record.component_end
            || record.component_end > styles.components
            || record.resolution_start >= record.resolution_end
            || record.resolution_end > maximum
        {
            return Err(malformed());
        }
        let selected: std::collections::BTreeSet<_> = coordinates
            .iter()
            .copied()
            .filter(|(component, layer, resolution)| {
                reference_progression_contains(*record, *component, *layer, *resolution)
            })
            .collect();
        if selected.difference(&owned).next().is_none() {
            return Err(malformed());
        }
        owned.extend(selected);
    }
    if owned.len() == active {
        Ok(())
    } else {
        Err(malformed())
    }
}

fn raw_progression_windows() -> [ProgressionChange; 4] {
    [
        ProgressionChange {
            resolution_start: 0,
            resolution_end: u8::MAX,
            component_start: 0,
            component_end: u16::MAX,
            layer_end: u16::MAX,
            progression_order: ProgressionOrder::Lrcp,
        },
        ProgressionChange {
            resolution_start: 1,
            resolution_end: 2,
            component_start: 1,
            component_end: 2,
            layer_end: 1,
            progression_order: ProgressionOrder::Cprl,
        },
        ProgressionChange {
            resolution_start: 2,
            resolution_end: 1,
            component_start: u16::MAX,
            component_end: 0,
            layer_end: u16::MAX,
            progression_order: ProgressionOrder::Rpcl,
        },
        ProgressionChange {
            resolution_start: 0,
            resolution_end: u8::MAX,
            component_start: 0,
            component_end: u16::MAX,
            layer_end: 0,
            progression_order: ProgressionOrder::Pcrl,
        },
    ]
}

fn raw_progression_bitmap(length: usize, pattern: usize) -> Vec<bool> {
    (0..length)
        .map(|index| pattern == 1 || (pattern == 2 && index % 2 != 0))
        .collect()
}

#[test]
fn actual_progression_shape_preserves_raw_styles_empty_bypass_and_work_thresholds() {
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let patterns: &[&[u8]] = &[&[0], &[1], &[31], &[254], &[255], &[0, 254], &[255, 0]];
    let empty = ProgressionChanges::from_records(vec![]);
    let changes = ProgressionChanges::from_records(vec![raw_progression_windows()[0]]);
    let mut cases = 0;
    for components in [0, 1, 2, 3, 63, 64, 65, 255, 256, 257, u16::MAX] {
        for layers in [0, 1, 2, 4, u16::MAX] {
            for depths in patterns {
                let styles = raw_progression_styles(components, depths);
                for offset in [0, usize::MAX] {
                    assert_eq!(
                        parser.progression_validation_shape(layers, &styles, offset),
                        reference_progression_shape(layers, &styles, offset)
                    );
                    assert_eq!(
                        parser.validate_progression_changes(&empty, layers, &styles, offset),
                        Ok(())
                    );
                    assert_eq!(
                        parser.validate_progression_changes(&changes, layers, &styles, offset),
                        reference_progression_admission(
                            changes.records(),
                            layers,
                            &styles,
                            &limits,
                            offset
                        )
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 770);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2)
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));
}

#[test]
fn actual_progression_marking_preserves_arbitrary_bitmaps_and_partial_failure_prefixes() {
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&[], &limits).unwrap();
    parser.position = usize::MAX;
    let mut rows = 0;
    for record in raw_progression_windows() {
        for component in [0, 1, u16::MAX] {
            for layer in [0, 1, u16::MAX] {
                for resolutions in [0, 1, 2, 3, u8::MAX] {
                    for length in [0, 1, 2, 4, 8] {
                        for pattern in 0..3 {
                            for linear in [0, 1, 2, usize::MAX - 1, usize::MAX] {
                                for marked in [false, true] {
                                    for offset in [0, usize::MAX] {
                                        let mut owners = raw_progression_bitmap(length, pattern);
                                        let mut expected = owners.clone();
                                        let result = reference_mark_progression_resolutions(
                                            record,
                                            (component, layer, resolutions),
                                            &mut expected,
                                            (linear, marked),
                                            offset,
                                        );
                                        assert_eq!(
                                            parser.mark_progression_resolutions(
                                                record,
                                                (component, layer, resolutions),
                                                &mut owners,
                                                (linear, marked),
                                                offset
                                            ),
                                            result
                                        );
                                        assert_eq!(owners, expected);
                                        rows += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(rows, 54_000);
    let mut layer_cases = 0;
    for record in raw_progression_windows() {
        for component in [0, 1, u16::MAX] {
            for resolutions in 0..=3 {
                for layers in 0..=3 {
                    for length in [0, 1, 2, 4, 8] {
                        for pattern in 0..3 {
                            for linear in [0, 1, 2, usize::MAX - 1, usize::MAX] {
                                for marked in [false, true] {
                                    for offset in [0, usize::MAX] {
                                        let mut owners = raw_progression_bitmap(length, pattern);
                                        let mut expected = owners.clone();
                                        let result = reference_mark_progression_layers(
                                            record,
                                            (component, resolutions),
                                            &mut expected,
                                            (linear, marked),
                                            layers,
                                            offset,
                                        );
                                        assert_eq!(
                                            parser.mark_progression_layers(
                                                record,
                                                (component, resolutions),
                                                &mut owners,
                                                (linear, marked),
                                                layers,
                                                offset
                                            ),
                                            result
                                        );
                                        assert_eq!(owners, expected);
                                        layer_cases += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(layer_cases, 57_600);
    let mut records = 0;
    for components in [0, 1, 2, 3, 63, 64, 65, u16::MAX] {
        let patterns: &[&[u8]] = if components <= 3 {
            &[&[0], &[1], &[0, 2], &[254], &[255], &[0, 255]]
        } else {
            &[&[0], &[0, 2], &[0, 255]]
        };
        for depths in patterns {
            let styles = raw_progression_styles(components, depths);
            for layers in 0..=2 {
                for record in raw_progression_windows() {
                    for length in [0, 1, 2, 4, 64] {
                        for pattern in 0..3 {
                            for offset in [0, usize::MAX] {
                                let mut owners = raw_progression_bitmap(length, pattern);
                                let mut expected = owners.clone();
                                let result = reference_mark_progression_record(
                                    record,
                                    layers,
                                    &styles,
                                    &mut expected,
                                    offset,
                                );
                                assert_eq!(
                                    parser.mark_progression_record(
                                        record,
                                        layers,
                                        &styles,
                                        &mut owners,
                                        offset
                                    ),
                                    result
                                );
                                assert_eq!(owners, expected);
                                records += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(records, 12_960);
    for marked in [false, true] {
        for offset in [0, usize::MAX] {
            let mut owners = vec![];
            assert_eq!(
                parser.mark_progression_layers(
                    raw_progression_windows()[0],
                    (u16::MAX, 0),
                    &mut owners,
                    (usize::MAX, marked),
                    u16::MAX,
                    offset
                ),
                Ok((usize::MAX, marked))
            );
            assert!(owners.is_empty());
        }
    }
    let mut completions = 0;
    for length in 0..=12 {
        for mask in 0..1_usize << length {
            let owners: Vec<bool> = (0..length).map(|index| mask & (1 << index) != 0).collect();
            assert_eq!(
                progression_owners_complete(&owners),
                owners.iter().all(|value| *value)
            );
            completions += 1;
        }
    }
    assert_eq!(completions, 8_191);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, 0, 0, 0)
    );
}

#[test]
fn actual_progression_admission_matches_independent_coordinate_sets_and_overlap_order() {
    let input = [0xa5, 0x5a];
    let orders = [
        ProgressionOrder::Lrcp,
        ProgressionOrder::Rlcp,
        ProgressionOrder::Rpcl,
        ProgressionOrder::Pcrl,
        ProgressionOrder::Cprl,
    ];
    let mut cases = 0;
    for components in 0..=3 {
        for depths in [&[0_u8][..], &[0, 2], &[2, 0, 1]] {
            let styles = raw_progression_styles(components, depths);
            for layers in 0..=3 {
                let (active, maximum) = reference_progression_shape(layers, &styles, 0).unwrap();
                let full = ProgressionChange {
                    resolution_start: 0,
                    resolution_end: maximum,
                    component_start: 0,
                    component_end: components,
                    layer_end: layers,
                    progression_order: ProgressionOrder::Lrcp,
                };
                let mut pool = [full; 12];
                pool[1].layer_end = 0;
                pool[2].layer_end = layers + 1;
                pool[3].component_start = components;
                pool[4].component_end = components + 1;
                pool[5].resolution_start = maximum;
                pool[6].resolution_end = maximum + 1;
                pool[7].layer_end = 1;
                pool[8].resolution_end = 1;
                pool[9].component_end = 1;
                pool[10].resolution_start = 1;
                pool[11] = raw_progression_windows()[2];
                for (index, record) in pool.iter_mut().enumerate() {
                    record.progression_order = orders[index % 5];
                }
                let mut sequences = vec![vec![]];
                for first in pool {
                    sequences.push(vec![first]);
                    for second in pool {
                        sequences.push(vec![first, second]);
                    }
                }
                assert_eq!(sequences.len(), 157);
                for records in sequences {
                    let cost = active as u64 * records.len() as u64;
                    let changes = ProgressionChanges::from_records(records.clone());
                    for cap in [0, cost.saturating_sub(1), cost, cost + 1] {
                        let limits = ResourceLimits::HARDENED
                            .with_maximum_work_units(cap)
                            .unwrap();
                        let mut parser = new_parser(&input, &limits).unwrap();
                        parser.position = usize::MAX;
                        parser.work_units = u64::MAX;
                        parser.packet_length_bytes = u64::MAX - 1;
                        parser.packet_lengths = u64::MAX - 2;
                        for offset in [0, usize::MAX] {
                            assert_eq!(
                                parser.validate_progression_changes(
                                    &changes, layers, &styles, offset
                                ),
                                reference_progression_admission(
                                    &records, layers, &styles, &limits, offset
                                )
                            );
                            assert_eq!(changes.records(), records);
                            assert_eq!(
                                (
                                    parser.position,
                                    parser.work_units,
                                    parser.packet_length_bytes,
                                    parser.packet_lengths
                                ),
                                (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2)
                            );
                            assert_eq!(parser.input, &input);
                            assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
                            assert!(core::ptr::eq(parser.limits, &limits));
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 60_288);
    let styles = raw_progression_styles(1, &[2]);
    let first = ProgressionChange {
        resolution_start: 0,
        resolution_end: 2,
        component_start: 0,
        component_end: 1,
        layer_end: 1,
        progression_order: ProgressionOrder::Lrcp,
    };
    let second = ProgressionChange {
        resolution_start: 1,
        resolution_end: 3,
        ..first
    };
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(6).unwrap();
    let parser = new_parser(&[], &limits).unwrap();
    let overlap = ProgressionChanges::from_records(vec![first, second]);
    assert_eq!(
        parser.validate_progression_changes(&overlap, 1, &styles, 17),
        Ok(())
    );
    let redundant = ProgressionChanges::from_records(vec![first, first]);
    assert_eq!(
        parser.validate_progression_changes(&redundant, 1, &styles, 17),
        Err(DecodeError::MalformedInput {
            offset: 17,
            kind: MalformedKind::InvalidProgressionOrderChange
        })
    );
}

fn reference_poc_component(
    bytes: &[u8],
    position: usize,
    width: usize,
    offset: usize,
) -> Result<u16, DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    if width == 1 {
        return bytes
            .get(position)
            .map(|byte| u16::from(*byte))
            .ok_or(malformed(MalformedKind::InvalidMarkerLength));
    }
    let end = position as u128 + 2;
    if end > usize::MAX as u128 {
        return Err(malformed(MalformedKind::ArithmeticOverflow));
    }
    let source = bytes
        .get(position..end as usize)
        .ok_or(malformed(MalformedKind::InvalidMarkerLength))?;
    Ok(u16::from_be_bytes([source[0], source[1]]))
}

fn reference_poc_payload(
    bytes: &[u8],
    components: u16,
    offset: usize,
) -> Result<Vec<ProgressionChange>, DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    let width = if components <= 256 { 1 } else { 2 };
    let chunks = bytes.chunks_exact(5 + 2 * width);
    if bytes.is_empty() || !chunks.remainder().is_empty() {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    let orders = [
        ProgressionOrder::Lrcp,
        ProgressionOrder::Rlcp,
        ProgressionOrder::Rpcl,
        ProgressionOrder::Pcrl,
        ProgressionOrder::Cprl,
    ];
    let mut records = Vec::new();
    for chunk in chunks {
        let progression_order = orders
            .get(usize::from(chunk[4 + 2 * width]))
            .copied()
            .ok_or(malformed(MalformedKind::InvalidProgressionOrderChange))?;
        let component_start = if width == 1 {
            u16::from(chunk[1])
        } else {
            u16::from_be_bytes([chunk[1], chunk[2]])
        };
        let component_end = if width == 1 {
            u16::from(chunk[5])
        } else {
            u16::from_be_bytes([chunk[6], chunk[7]])
        };
        records.push(ProgressionChange {
            resolution_start: chunk[0],
            component_start,
            layer_end: u16::from_be_bytes([chunk[1 + width], chunk[2 + width]]),
            resolution_end: chunk[3 + width],
            component_end: if components == 256 && component_end == 0 {
                256
            } else {
                component_end
            },
            progression_order,
        });
    }
    Ok(records)
}

fn raw_poc_payload(components: u16, records: &[[u16; 6]]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for [
        resolution_start,
        component_start,
        layer_end,
        resolution_end,
        component_end,
        order,
    ] in records
    {
        bytes.push(*resolution_start as u8);
        if components <= 256 {
            bytes.push(*component_start as u8);
        } else {
            bytes.extend(component_start.to_be_bytes());
        }
        bytes.extend(layer_end.to_be_bytes());
        bytes.push(*resolution_end as u8);
        if components <= 256 {
            bytes.push(*component_end as u8);
        } else {
            bytes.extend(component_end.to_be_bytes());
        }
        bytes.push(*order as u8);
    }
    bytes
}

fn assert_poc_payload_case(parser: &Parser<'_>, bytes: &[u8], components: u16, offset: usize) {
    assert_eq!(
        parser
            .parse_poc(
                Segment {
                    marker: 0x1234,
                    offset,
                    payload: bytes
                },
                components
            )
            .map(|changes| changes.records().to_vec()),
        reference_poc_payload(bytes, components, offset),
    );
}

#[test]
fn actual_poc_reads_preserve_width_fallback_endian_bytes_and_segment_error_offsets() {
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let mut frontiers = 0;
    for length in [0, 1, 2, 3, 8] {
        for pattern in [0, 1, 0x7f, 0x80, 255] {
            let bytes = vec![pattern; length];
            for position in [0, 1, 2, 7, 8, usize::MAX - 2, usize::MAX - 1, usize::MAX] {
                for width in [0, 1, 2, 3, 16, usize::MAX] {
                    for cursor in [0, 17, usize::MAX] {
                        parser.position = cursor;
                        for offset in [0, usize::MAX] {
                            let segment = Segment {
                                marker: 0x1234,
                                offset,
                                payload: &bytes,
                            };
                            assert_eq!(
                                parser.read_poc_component(segment, position, width),
                                reference_poc_component(&bytes, position, width, offset)
                            );
                            assert_eq!(
                                parser.read_poc_byte(segment, position),
                                bytes
                                    .get(position)
                                    .copied()
                                    .ok_or(DecodeError::MalformedInput {
                                        offset: offset as u64,
                                        kind: MalformedKind::InvalidMarkerLength
                                    })
                            );
                            frontiers += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(frontiers, 7_200);
    let mut words = 0;
    for word in 0..=u16::MAX {
        let [first, second] = word.to_be_bytes();
        let bytes = [0xa5, first, second, 0x5a];
        for width in [0, 1, 2, usize::MAX] {
            for offset in [0, usize::MAX] {
                let segment = Segment {
                    marker: 0x1234,
                    offset,
                    payload: &bytes,
                };
                assert_eq!(
                    parser.read_poc_component(segment, 1, width),
                    reference_poc_component(&bytes, 1, width, offset)
                );
                assert_eq!(parser.read_poc_byte(segment, 1), Ok(first));
                words += 1;
            }
        }
    }
    assert_eq!(words, 524_288);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2)
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));
}

#[test]
fn actual_poc_preserves_raw_records_width_thresholds_end256_and_error_precedence() {
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let mut counts = 0;
    for components in 0..=u16::MAX {
        let bytes = raw_poc_payload(components, &[[255, u16::MAX, 0, 0, 0, 4]]);
        for offset in [0, usize::MAX] {
            assert_poc_payload_case(&parser, &bytes, components, offset);
            counts += 1;
        }
    }
    assert_eq!(counts, 131_072);
    let mut words = 0;
    for word in 0..=u16::MAX {
        for components in [0, 1, 255, 256, 257, u16::MAX] {
            let bytes = raw_poc_payload(components, &[[0, word, word, 255, word, word % 5]]);
            for offset in [0, usize::MAX] {
                assert_poc_payload_case(&parser, &bytes, components, offset);
                words += 1;
            }
        }
    }
    assert_eq!(words, 786_432);
    let mut mutations = 0;
    for components in [0, 255, 256, 257, u16::MAX] {
        let source = raw_poc_payload(
            components,
            &[
                [1, 0, 1, 2, 1, 0],
                [255, 255, 0, 0, 0, 4],
                [0, u16::MAX, u16::MAX, 255, u16::MAX, 2],
            ],
        );
        for position in 0..source.len() {
            for value in 0..=u8::MAX {
                for variant in 0..3 {
                    let mut bytes = source.clone();
                    bytes[position] = value;
                    if variant == 0 {
                        bytes.pop();
                    } else if variant == 2 {
                        bytes.push(0);
                    }
                    for offset in [0, usize::MAX] {
                        assert_poc_payload_case(&parser, &bytes, components, offset);
                        mutations += 1;
                    }
                }
            }
        }
    }
    assert_eq!(mutations, 179_712);
    let mut lengths = 0;
    for length in 0..=29 {
        for pattern in [0, 255] {
            for components in [0, 1, 256, 257, u16::MAX] {
                for offset in [0, usize::MAX] {
                    assert_poc_payload_case(&parser, &vec![pattern; length], components, offset);
                    lengths += 1;
                }
            }
        }
    }
    assert_eq!(lengths, 600);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2)
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));
}

#[test]
fn actual_poc_reader_join_retains_raw_invalid_ranges_and_rejects_bad_order() {
    let limits = ResourceLimits::HARDENED;
    let first = raw_poc_payload(256, &[[255, 255, 0, 0, 0, 4]]);
    let second = raw_poc_payload(256, &[[0, 0, 1, 255, 1, 0], [1, 1, u16::MAX, 2, 0, 2]]);
    let third = raw_poc_payload(256, &[[0, 0, 1, 1, 1, 255]]);
    let mut input = segment(POC, &first);
    input.extend(segment(POC, &second));
    input.extend(segment(POC, &third));
    let mut parser = new_parser(&input, &limits).unwrap();
    let raw = parser.read_segment().unwrap();
    let changes = parser.parse_poc(raw, 256).unwrap();
    assert_eq!(
        changes.records(),
        reference_poc_payload(&first, 256, 0).unwrap()
    );
    assert_eq!(
        (
            changes.records()[0].resolution_start,
            changes.records()[0].resolution_end,
            changes.records()[0].layer_end,
            changes.records()[0].component_end
        ),
        (255, 0, 0, 256)
    );
    let raw = parser.read_segment().unwrap();
    assert_eq!(
        parser.parse_poc(raw, 256).unwrap().records(),
        reference_poc_payload(&second, 256, 11).unwrap()
    );
    let raw = parser.read_segment().unwrap();
    assert_eq!(
        parser.parse_poc(raw, 256),
        Err(DecodeError::MalformedInput {
            offset: 29,
            kind: MalformedKind::InvalidProgressionOrderChange,
        })
    );
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (40, 3, 0, 0)
    );
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
}

fn reference_kernel_coefficient(
    bytes: &[u8],
    cursor: usize,
    offset: usize,
    position: usize,
    width: usize,
    coefficient_type: u8,
) -> Result<KernelCoefficient, DecodeError> {
    if !(1..=16).contains(&width) {
        return Err(DecodeError::MalformedInput {
            offset: cursor as u64,
            kind: MalformedKind::InvalidTransform,
        });
    }
    let end = position as u128 + width as u128;
    if end > usize::MAX as u128 {
        return Err(DecodeError::MalformedInput {
            offset: cursor as u64,
            kind: MalformedKind::ArithmeticOverflow,
        });
    }
    let Some(source) = bytes.get(position..end as usize) else {
        return Err(DecodeError::MalformedInput {
            offset: offset as u64,
            kind: MalformedKind::InvalidMarkerLength,
        });
    };
    let mut value = source
        .iter()
        .fold(0_u128, |previous, byte| previous * 256 + u128::from(*byte));
    if coefficient_type <= 1 && source[0] >= 128 && width < 16 {
        value |= u128::MAX << (width * 8);
    }
    Ok(KernelCoefficient {
        bytes: value.to_be_bytes(),
        width: width as u8,
    })
}

fn reference_atk_byte(
    bytes: &[u8],
    position: &mut usize,
    offset: usize,
) -> Result<u8, DecodeError> {
    let byte = *bytes.get(*position).ok_or(DecodeError::MalformedInput {
        offset: offset as u64,
        kind: MalformedKind::InvalidMarkerLength,
    })?;
    *position += 1;
    Ok(byte)
}

fn reference_atk_step(
    bytes: &[u8],
    cursor: usize,
    offset: usize,
    start: usize,
    format: (usize, u8),
    flags: (bool, bool),
) -> Result<(KernelLiftingStep, usize), DecodeError> {
    let (width, coefficient_type) = format;
    let (reversible, whole_sample_filter) = flags;
    let mut position = start;
    let step_offset = if whole_sample_filter {
        0
    } else {
        i8::from_be_bytes([reference_atk_byte(bytes, &mut position, offset)?])
    };
    let exponent = if reversible {
        reference_atk_byte(bytes, &mut position, offset)?
    } else {
        0
    };
    let residue = if reversible {
        let value =
            reference_kernel_coefficient(bytes, cursor, offset, position, width, coefficient_type)?;
        position += width;
        Some(value)
    } else {
        None
    };
    let count = reference_atk_byte(bytes, &mut position, offset)?;
    if count == 0 {
        return Err(DecodeError::MalformedInput {
            offset: offset as u64,
            kind: MalformedKind::InvalidTransform,
        });
    }
    let mut coefficients = Vec::new();
    for _ in 0..count {
        coefficients.push(reference_kernel_coefficient(
            bytes,
            cursor,
            offset,
            position,
            width,
            coefficient_type,
        )?);
        position += width;
    }
    Ok((
        KernelLiftingStep {
            offset: step_offset,
            exponent,
            residue,
            coefficients,
        },
        position,
    ))
}

fn reference_atk_payload(
    bytes: &[u8],
    cursor: usize,
    offset: usize,
) -> Result<ArbitraryKernel, DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    if bytes.len() < 7 {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    let descriptor = u16::from_be_bytes([bytes[0], bytes[1]]);
    let index = (descriptor % 256) as u8;
    let coefficient_type = (descriptor / 256 % 8) as u8;
    if index < 2 || coefficient_type > 4 || descriptor >= 32768 {
        return Err(malformed(MalformedKind::InvalidTransform));
    }
    let width = 1_usize << coefficient_type;
    let whole_sample_filter = descriptor / 2048 % 2 == 1;
    let reversible = descriptor / 4096 % 2 == 1;
    let initial_odd = descriptor / 8192 % 2 == 1;
    let whole_sample_extension = descriptor / 16384 % 2 == 1;
    let mut position = 2;
    let scaling = if reversible {
        None
    } else {
        let value =
            reference_kernel_coefficient(bytes, cursor, offset, position, width, coefficient_type)?;
        position += width;
        Some(value)
    };
    let count = reference_atk_byte(bytes, &mut position, offset)?;
    let mut steps = Vec::new();
    for _ in 0..count {
        let (step, next) = reference_atk_step(
            bytes,
            cursor,
            offset,
            position,
            (width, coefficient_type),
            (reversible, whole_sample_filter),
        )?;
        position = next;
        steps.push(step);
    }
    if position != bytes.len() {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    Ok(ArbitraryKernel {
        index,
        reversible,
        descriptor,
        coefficient_type,
        whole_sample_filter,
        initial_odd,
        whole_sample_extension,
        scaling,
        steps,
    })
}

fn raw_atk_payload(descriptor: u16, counts: &[u8], pattern: u8) -> Vec<u8> {
    let coefficient_type = ((descriptor >> 8) & 7) as usize;
    let width = 1_usize << coefficient_type.min(4);
    let reversible = descriptor & 0x1000 != 0;
    let whole_sample_filter = descriptor & 0x0800 != 0;
    let mut bytes = descriptor.to_be_bytes().to_vec();
    if !reversible {
        bytes.extend((0..width).map(|index| pattern.wrapping_add(index as u8)));
    }
    bytes.push(u8::try_from(counts.len()).unwrap());
    for (step, count) in counts.iter().enumerate() {
        if !whole_sample_filter {
            bytes.push(pattern.wrapping_add(step as u8));
        }
        if reversible {
            bytes.push(pattern.wrapping_mul(3));
            bytes.extend((0..width).map(|index| pattern ^ index as u8));
        }
        bytes.push(*count);
        for coefficient in 0..*count {
            bytes.extend(
                (0..width)
                    .map(|index| pattern.wrapping_add(coefficient).wrapping_mul(17) ^ index as u8),
            );
        }
    }
    bytes
}

fn assert_atk_payload_case(parser: &Parser<'_>, bytes: &[u8], offset: usize) {
    assert_eq!(
        parser.decode_atk_payload(Segment {
            marker: 0x1234,
            offset,
            payload: bytes
        }),
        reference_atk_payload(bytes, parser.position, offset),
    );
}

#[test]
fn actual_atk_coefficients_preserve_all_raw_bytes_widths_signs_and_error_offsets() {
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&[], &limits).unwrap();
    let mut frontiers = 0;
    for width in (0..=17).chain(core::iter::once(usize::MAX)) {
        for coefficient_type in [0, 1, 2, 3, 4, 5, u8::MAX] {
            for position in [0, 1, 8, 16, 32, usize::MAX - 16, usize::MAX - 1, usize::MAX] {
                for length in [0, 1, 2, 16, 17, 32] {
                    for pattern in [0, 0x7f, 0x80, 255] {
                        let bytes = vec![pattern; length];
                        for cursor in [0, 17, usize::MAX] {
                            parser.position = cursor;
                            for offset in [0, usize::MAX] {
                                assert_eq!(
                                    parser.read_kernel_coefficient(
                                        Segment {
                                            marker: 0x1234,
                                            offset,
                                            payload: &bytes
                                        },
                                        position,
                                        width,
                                        coefficient_type
                                    ),
                                    reference_kernel_coefficient(
                                        &bytes,
                                        cursor,
                                        offset,
                                        position,
                                        width,
                                        coefficient_type
                                    ),
                                );
                                frontiers += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(frontiers, 153_216);
    let mut mutations = 0;
    for width in 1..=16 {
        for byte in 0..width {
            for value in 0..=u8::MAX {
                let mut bytes: Vec<u8> = (0..=width)
                    .map(|index| (index as u8).wrapping_mul(17).wrapping_add(0x80))
                    .collect();
                bytes[1 + byte] = value;
                for coefficient_type in [0, 1, 4, u8::MAX] {
                    for offset in [0, usize::MAX] {
                        assert_eq!(
                            parser.read_kernel_coefficient(
                                Segment {
                                    marker: 0x1234,
                                    offset,
                                    payload: &bytes
                                },
                                1,
                                width,
                                coefficient_type
                            ),
                            reference_kernel_coefficient(
                                &bytes,
                                usize::MAX,
                                offset,
                                1,
                                width,
                                coefficient_type
                            ),
                        );
                        mutations += 1;
                    }
                }
            }
        }
    }
    assert_eq!(mutations, 278_528);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, 0, 0, 0)
    );
    assert!(parser.input.is_empty());
    assert!(core::ptr::eq(parser.limits, &limits));
}

#[test]
fn actual_atk_preserves_all_descriptors_steps_counts_and_terminal_order() {
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let mut descriptors = 0;
    for descriptor in 0..=u16::MAX {
        for length in [0, 1, 6, 7, 8, 19, 32] {
            let mut bytes = descriptor.to_be_bytes().to_vec();
            bytes.resize(length, 0);
            for offset in [0, usize::MAX] {
                assert_atk_payload_case(&parser, &bytes, offset);
                descriptors += 1;
            }
        }
    }
    assert_eq!(descriptors, 917_504);
    let mut steps = 0;
    for width in [0, 1, 2, 3, 4, 8, 16, 17, usize::MAX] {
        for coefficient_type in [0, 1, 2, 4, u8::MAX] {
            for reversible in [false, true] {
                for whole_sample_filter in [false, true] {
                    for start in [0, 1, 8, usize::MAX] {
                        for length in [0, 1, 3, 7, 19, 65] {
                            for pattern in [0, 1, 0x80, 255] {
                                let bytes = vec![pattern; length];
                                for cursor in [0, usize::MAX] {
                                    parser.position = cursor;
                                    for offset in [0, usize::MAX] {
                                        assert_eq!(
                                            parser.decode_atk_step(
                                                Segment {
                                                    marker: 0x1234,
                                                    offset,
                                                    payload: &bytes
                                                },
                                                start,
                                                width,
                                                coefficient_type,
                                                reversible,
                                                whole_sample_filter
                                            ),
                                            reference_atk_step(
                                                &bytes,
                                                cursor,
                                                offset,
                                                start,
                                                (width, coefficient_type),
                                                (reversible, whole_sample_filter)
                                            ),
                                        );
                                        steps += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(steps, 69_120);
    let mut records = 0;
    for coefficient_type in 0_u16..=4 {
        for flags in 0_u16..16 {
            for index in [2, 255] {
                let descriptor = index + (coefficient_type << 8) + (flags << 11);
                for counts in [
                    vec![],
                    vec![0],
                    vec![1],
                    vec![2, 1],
                    vec![255],
                    vec![1; 255],
                ] {
                    let source = raw_atk_payload(descriptor, &counts, 0x80);
                    for variant in 0..3 {
                        let mut bytes = source.clone();
                        if variant == 0 {
                            bytes.pop();
                        } else if variant == 2 {
                            bytes.push(0);
                        }
                        for offset in [0, usize::MAX] {
                            assert_atk_payload_case(&parser, &bytes, offset);
                            records += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(records, 5_760);
    let maximum = raw_atk_payload(0x0402, &vec![255; 255], 0x80);
    assert_eq!(maximum.len(), 1_040_929);
    for offset in [0, usize::MAX] {
        assert_atk_payload_case(&parser, &maximum, offset);
    }
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2)
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));
}

fn assert_atk_owner_case(
    bytes: &[u8],
    mode: usize,
    limits: &ResourceLimits,
    budget: (u64, u64),
    offset: usize,
) {
    let index = bytes.get(1).copied().unwrap_or(0);
    let seed = ArbitraryKernel {
        index: 0,
        descriptor: u16::MAX,
        reversible: true,
        coefficient_type: u8::MAX,
        whole_sample_filter: false,
        initial_odd: true,
        whole_sample_extension: false,
        scaling: Some(KernelCoefficient {
            bytes: [0x80; 16],
            width: 0,
        }),
        steps: vec![KernelLiftingStep {
            offset: i8::MIN,
            exponent: u8::MAX,
            residue: Some(KernelCoefficient {
                bytes: [255; 16],
                width: u8::MAX,
            }),
            coefficients: vec![],
        }],
    };
    let mut extensions = raw_owned_tile_part_fixture(0).part2_extensions;
    extensions.arbitrary_kernels = if mode == 0 {
        vec![]
    } else {
        vec![seed.clone()]
    };
    if mode == 2 {
        let mut first = seed.clone();
        first.index = index;
        let mut later = first.clone();
        later.reversible = false;
        later.steps.clear();
        extensions.arbitrary_kernels.extend([first, seed, later]);
    }
    let (metadata, work) = budget;
    extensions.metadata_bytes = metadata;
    let mut expected = extensions.clone();
    let (mut result, next_work, next_metadata) =
        reference_extension_charge(bytes.len(), 17, work, metadata, limits);
    expected.metadata_bytes = next_metadata;
    if result.is_ok() {
        result = match reference_atk_payload(bytes, 17, offset) {
            Err(error) => Err(error),
            Ok(replacement) => {
                if let Some(existing) = expected
                    .arbitrary_kernels
                    .iter_mut()
                    .find(|entry| entry.index == replacement.index)
                {
                    *existing = replacement;
                } else {
                    expected.arbitrary_kernels.push(replacement);
                }
                Ok(())
            }
        };
    }
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, limits).unwrap();
    parser.position = 17;
    parser.work_units = work;
    parser.packet_length_bytes = u64::MAX;
    parser.packet_lengths = u64::MAX - 1;
    assert_eq!(
        parser.parse_atk(
            Segment {
                marker: 0x1234,
                offset,
                payload: bytes
            },
            &mut extensions
        ),
        result
    );
    assert_eq!(extensions, expected);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (17, next_work, u64::MAX, u64::MAX - 1)
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, limits));
}

#[test]
fn actual_atk_preserves_first_duplicates_all_owner_fields_and_ordered_budget_failures() {
    let base = ResourceLimits::HARDENED;
    let limits = [
        base,
        base.with_maximum_metadata_bytes(0).unwrap(),
        base.with_maximum_metadata_bytes(8).unwrap(),
        base.with_maximum_work_units(0).unwrap(),
        base.with_maximum_work_units(8).unwrap(),
        base.with_maximum_metadata_bytes(4)
            .unwrap()
            .with_maximum_work_units(0)
            .unwrap(),
    ];
    let first = raw_atk_payload(0x1802, &[2, 1], 0x80);
    let second = raw_atk_payload(0x0402, &[1], 255);
    let mut short = first.clone();
    short.pop();
    let mut long = first.clone();
    long.push(0);
    let payloads = [
        vec![],
        vec![0; 6],
        vec![0; 7],
        vec![5, 2, 0, 0, 0, 0, 0],
        raw_atk_payload(0x0202, &[], 0),
        first.clone(),
        second.clone(),
        raw_atk_payload(0x04ff, &[1], 0x80),
        raw_atk_payload(0x1802, &[0], 0),
        raw_atk_payload(0x1802, &[1, 0], 0),
        short,
        long,
    ];
    assert_eq!(payloads.len(), 12);
    let mut cases = 0;
    for limit in &limits {
        for bytes in &payloads {
            for mode in 0..3 {
                for budget in [
                    (0, 0),
                    (0, u64::MAX),
                    (u64::MAX, 0),
                    (16_777_215, 8),
                    (u64::MAX - 4, u64::MAX - 4),
                ] {
                    for offset in [0, usize::MAX] {
                        assert_atk_owner_case(bytes, mode, limit, budget, offset);
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 2_160);
    let mut input = segment(ATK, &first);
    input.extend(segment(ATK, &second));
    let mut parser = new_parser(&input, &base).unwrap();
    let mut extensions = Part2Extensions::default();
    let raw = parser.read_segment().unwrap();
    parser.parse_atk(raw, &mut extensions).unwrap();
    let raw = parser.read_segment().unwrap();
    parser.parse_atk(raw, &mut extensions).unwrap();
    assert_eq!(
        extensions.arbitrary_kernels,
        vec![reference_atk_payload(&second, input.len(), first.len() + 4).unwrap()]
    );
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            extensions.metadata_bytes
        ),
        (input.len(), input.len() as u64 + 2, input.len() as u64)
    );
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
}

fn reference_tlm_payload(
    bytes: &[u8],
    next_index: &mut u16,
    tile_count: u64,
    offset: usize,
    lengths: &mut Vec<TilePartLength>,
) -> Result<(), DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    if bytes.len() < 2 {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    if u16::from(bytes[0]) != *next_index {
        return Err(malformed(MalformedKind::InvalidMarkerOrder));
    }
    *next_index += 1;
    let style = bytes[1];
    let tile_bytes = usize::from(style / 16 % 4);
    let length_bytes = if matches!(style / 64, 0 | 2) { 2 } else { 4 };
    let reserved = style % 16;
    if style >= 128 || reserved != 0 || tile_bytes == 3 {
        return Err(malformed(MalformedKind::InvalidTilePart));
    }
    let chunks = bytes[2..].chunks_exact(tile_bytes + length_bytes);
    if !chunks.remainder().is_empty() {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    for chunk in chunks {
        let tile_index = match tile_bytes {
            0 => None,
            1 => Some(u16::from(chunk[0])),
            _ => Some(u16::from_be_bytes([chunk[0], chunk[1]])),
        };
        if tile_index.is_some_and(|value| u64::from(value) >= tile_count) {
            return Err(malformed(MalformedKind::InvalidTilePart));
        }
        let length = if length_bytes == 2 {
            u32::from(u16::from_be_bytes(chunk[tile_bytes..].try_into().unwrap()))
        } else {
            u32::from_be_bytes(chunk[tile_bytes..].try_into().unwrap())
        };
        if length < 14 {
            return Err(malformed(MalformedKind::InvalidTilePart));
        }
        lengths.push(TilePartLength { tile_index, length });
    }
    Ok(())
}

fn raw_tlm_payload(index: u8, style: u8, records: &[(u16, u32)]) -> Vec<u8> {
    let tile_bytes = usize::from(style / 16 % 4);
    let length_bytes = if matches!(style / 64, 0 | 2) { 2 } else { 4 };
    let mut bytes = vec![index, style];
    for (tile, length) in records {
        bytes.extend(&u32::from(*tile).to_be_bytes()[4 - tile_bytes..]);
        bytes.extend(&length.to_be_bytes()[4 - length_bytes..]);
    }
    bytes
}

fn assert_tlm_owner_case(
    bytes: &[u8],
    next_index: u16,
    tile_count: u64,
    limits: &ResourceLimits,
    budget: (u64, u64),
    offset: usize,
) {
    let (metadata, work) = budget;
    let mut extensions = raw_owned_tile_part_fixture(0).part2_extensions;
    extensions.tile_part_lengths = vec![
        TilePartLength {
            tile_index: Some(u16::MAX),
            length: 0,
        },
        TilePartLength {
            tile_index: None,
            length: u32::MAX,
        },
    ];
    extensions.metadata_bytes = metadata;
    let mut expected = extensions.clone();
    let mut expected_index = next_index;
    let (mut result, next_work, next_metadata) =
        reference_extension_charge(bytes.len(), 17, work, metadata, limits);
    expected.metadata_bytes = next_metadata;
    if result.is_ok() {
        result = reference_tlm_payload(
            bytes,
            &mut expected_index,
            tile_count,
            offset,
            &mut expected.tile_part_lengths,
        );
    }
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, limits).unwrap();
    parser.position = 17;
    parser.work_units = work;
    parser.packet_length_bytes = u64::MAX;
    parser.packet_lengths = u64::MAX - 1;
    let mut actual_index = next_index;
    assert_eq!(
        parser.parse_tlm(
            Segment {
                marker: 0x1234,
                offset,
                payload: bytes
            },
            &mut actual_index,
            tile_count,
            &mut extensions
        ),
        result,
    );
    assert_eq!(actual_index, expected_index);
    assert_eq!(extensions, expected);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (17, next_work, u64::MAX, u64::MAX - 1)
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, limits));
}

#[test]
fn actual_tlm_preserves_every_header_style_index_and_external_counter() {
    let limits = ResourceLimits::HARDENED;
    let mut headers = 0;
    for index in 0..=u8::MAX {
        for style in 0..=u8::MAX {
            for next in [0, u16::from(index), u16::from(index) + 1, 256, u16::MAX] {
                assert_tlm_owner_case(&[index, style], next, 0, &limits, (0, 0), usize::MAX);
                headers += 1;
            }
        }
    }
    assert_eq!(headers, 327_680);
    let mut counters = 0;
    for next in 0..=u16::MAX {
        for index in [0, u8::MAX] {
            assert_tlm_owner_case(&[index, 0], next, u64::MAX, &limits, (0, 0), usize::MAX);
            counters += 1;
        }
    }
    assert_eq!(counters, 131_072);
}

#[test]
fn actual_tlm_preserves_endian_words_valid_prefixes_and_record_alignment() {
    let limits = ResourceLimits::HARDENED;
    let styles = [0, 0x10, 0x20, 0x40, 0x50, 0x60];
    let mut words = 0;
    for word in 0..=u16::MAX {
        for style in styles {
            let length = if style < 0x40 {
                u32::from(word)
            } else {
                (u32::from(word) << 16) + u32::from(word.wrapping_mul(31337))
            };
            let source = raw_tlm_payload(0, style, &[(0, 14), (word, length), (1, 15)]);
            let tile = if style / 16 % 4 == 1 {
                u64::from(word as u8)
            } else {
                u64::from(word)
            };
            for count in [tile, tile + 1] {
                assert_tlm_owner_case(&source, 0, count, &limits, (0, 0), usize::MAX);
                words += 1;
            }
        }
    }
    assert_eq!(words, 786_432);
    let mut frontiers = 0;
    for style in styles {
        for tile_count in [0, 1, 255, 256, 257, 65535, 65536, u64::MAX] {
            for length in [0, 1, 13, 14, 15, 65535, 65536, u32::MAX] {
                for bad_position in 0..3 {
                    let mut records = [(0, 14); 3];
                    records[bad_position] = (u16::MAX, length);
                    let source = raw_tlm_payload(255, style, &records);
                    for variant in 0..3 {
                        let mut bytes = source.clone();
                        if variant == 0 {
                            bytes.pop();
                        } else if variant == 2 {
                            bytes.push(0);
                        }
                        for offset in [0, usize::MAX] {
                            assert_tlm_owner_case(&bytes, 255, tile_count, &limits, (0, 0), offset);
                            frontiers += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(frontiers, 6_912);
}

#[test]
fn actual_tlm_preserves_three_owner_frames_partial_charges_and_real_reader() {
    let base = ResourceLimits::HARDENED;
    let limits = [
        base,
        base.with_maximum_metadata_bytes(0).unwrap(),
        base.with_maximum_metadata_bytes(8).unwrap(),
        base.with_maximum_work_units(0).unwrap(),
        base.with_maximum_work_units(8).unwrap(),
        base.with_maximum_metadata_bytes(4)
            .unwrap()
            .with_maximum_work_units(0)
            .unwrap(),
    ];
    let mut short = raw_tlm_payload(0, 0x20, &[(0, 14)]);
    short.pop();
    let mut long = raw_tlm_payload(0, 0x20, &[(0, 14)]);
    long.push(0);
    let payloads = [
        vec![],
        vec![0],
        vec![0, 0],
        vec![255, 0],
        vec![255, 0x80],
        vec![1, 0x30],
        raw_tlm_payload(0, 0, &[(0, 0)]),
        raw_tlm_payload(0, 0x10, &[(1, 14)]),
        raw_tlm_payload(1, 0x20, &[(0, 14), (1, 15), (u16::MAX, 13)]),
        raw_tlm_payload(0, 0x40, &[(0, u32::MAX)]),
        short,
        long,
    ];
    assert_eq!(payloads.len(), 12);
    let mut cases = 0;
    for limit in &limits {
        for bytes in &payloads {
            for next in [0, 1, 255, 256, u16::MAX] {
                for tile_count in [0, 1, 2, 65536, u64::MAX] {
                    for budget in [
                        (0, 0),
                        (0, u64::MAX),
                        (u64::MAX, 0),
                        (16_777_215, 8),
                        (u64::MAX - 4, u64::MAX - 4),
                    ] {
                        for offset in [0, usize::MAX] {
                            assert_tlm_owner_case(bytes, next, tile_count, limit, budget, offset);
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 18_000);
    let mut input = segment(TLM, &raw_tlm_payload(0, 0, &[(0, 14), (0, 65535)]));
    input.extend(segment(TLM, &raw_tlm_payload(1, 0, &[(0, 13)])));
    let mut parser = new_parser(&input, &base).unwrap();
    let mut extensions = Part2Extensions::default();
    let mut next = 0;
    let raw = parser.read_segment().unwrap();
    parser
        .parse_tlm(raw, &mut next, 0, &mut extensions)
        .unwrap();
    let raw = parser.read_segment().unwrap();
    assert_eq!(
        parser.parse_tlm(raw, &mut next, 0, &mut extensions),
        Err(DecodeError::MalformedInput {
            offset: 10,
            kind: MalformedKind::InvalidTilePart
        }),
    );
    assert_eq!(
        extensions.tile_part_lengths,
        vec![
            TilePartLength {
                tile_index: None,
                length: 14
            },
            TilePartLength {
                tile_index: None,
                length: 65535
            },
        ]
    );
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            extensions.metadata_bytes,
            next
        ),
        (18, 20, 18, 2)
    );
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
}

fn reference_nlt_gamma(bytes: &[u8], offset: usize) -> Result<[u32; 5], DecodeError> {
    if bytes.len() != 19 {
        return Err(DecodeError::MalformedInput {
            offset: offset as u64,
            kind: MalformedKind::InvalidMarkerLength,
        });
    }
    let parameters = core::array::from_fn(|index| {
        let position = 4 + 3 * index;
        u32::from_be_bytes([0, bytes[position], bytes[position + 1], bytes[position + 2]])
    });
    if [0, 1, 3].iter().any(|index| parameters[*index] == 0) {
        return Err(DecodeError::MalformedInput {
            offset: offset as u64,
            kind: MalformedKind::InvalidTransform,
        });
    }
    Ok(parameters)
}

fn reference_nlt_payload(
    bytes: &[u8],
    components: u16,
    offset: usize,
) -> Result<NonlinearPointTransform, DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    if bytes.len() < 4 {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    let selector = u16::from_be_bytes([bytes[0], bytes[1]]);
    let component = if selector == u16::MAX {
        None
    } else if selector < components {
        Some(selector)
    } else {
        return Err(malformed(MalformedKind::InvalidTransform));
    };
    let precision = bytes[2] % 128 + 1;
    let kind = bytes[3];
    if precision > 38 || kind > 4 {
        return Err(malformed(MalformedKind::InvalidTransform));
    }
    if matches!(kind, 0 | 3) && bytes.len() != 4 {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    let mut result = NonlinearPointTransform {
        component,
        precision,
        signed: bytes[2] / 128 == 1,
        transform_type: kind,
        parameters: bytes[4..].to_vec(),
        d_min: None,
        d_max: None,
        point_bits: None,
        points: vec![],
        gamma_parameters: None,
    };
    if kind == 1 {
        result.gamma_parameters = Some(reference_nlt_gamma(bytes, offset)?);
    }
    if matches!(kind, 2 | 4) {
        if bytes.len() < 15 {
            return Err(malformed(MalformedKind::InvalidMarkerLength));
        }
        let stored = u16::from_be_bytes([bytes[4], bytes[5]]);
        if !(1..=8191).contains(&stored) {
            return Err(malformed(MalformedKind::InvalidTransform));
        }
        let minimum = u32::from_be_bytes(bytes[6..10].try_into().unwrap());
        let maximum = u32::from_be_bytes(bytes[10..14].try_into().unwrap());
        let bits = bytes[14];
        if minimum >= maximum || !(1..=32).contains(&bits) {
            return Err(malformed(MalformedKind::InvalidTransform));
        }
        let width = match bits {
            1..=8 => 1,
            9..=16 => 2,
            _ => 4,
        };
        if bytes.len() != 15 + (usize::from(stored) + 1) * width {
            return Err(malformed(MalformedKind::InvalidMarkerLength));
        }
        for chunk in bytes[15..].chunks_exact(width) {
            let value = chunk
                .iter()
                .fold(0_u64, |previous, byte| previous * 256 + u64::from(*byte));
            if value > (1_u64 << bits) - 1 {
                return Err(malformed(MalformedKind::InvalidTransform));
            }
            result.points.push(u32::try_from(value).unwrap());
        }
        result.d_min = Some(minimum);
        result.d_max = Some(maximum);
        result.point_bits = Some(bits);
    }
    Ok(result)
}

fn raw_nlt_gamma_payload(parameters: [u32; 5]) -> Vec<u8> {
    let mut bytes = vec![255, 255, 0xa4, 1];
    for value in parameters {
        bytes.extend(&value.to_be_bytes()[1..]);
    }
    bytes
}

fn raw_nlt_points_payload(
    kind: u8,
    bits: u8,
    stored: u16,
    domain: (u32, u32),
    values: &[u32],
) -> Vec<u8> {
    let mut bytes = vec![255, 255, 0xa4, kind];
    bytes.extend(stored.to_be_bytes());
    bytes.extend(domain.0.to_be_bytes());
    bytes.extend(domain.1.to_be_bytes());
    bytes.push(bits);
    let width = match bits {
        0..=8 => 1,
        9..=16 => 2,
        _ => 4,
    };
    for value in values {
        bytes.extend(&value.to_be_bytes()[4 - width..]);
    }
    bytes
}

fn assert_nlt_payload_case(parser: &Parser<'_>, bytes: &[u8], components: u16, offset: usize) {
    assert_eq!(
        parser.decode_nlt_payload(
            Segment {
                marker: 0x1234,
                offset,
                payload: bytes
            },
            components
        ),
        reference_nlt_payload(bytes, components, offset),
        "bytes={bytes:?}, components={components}, offset={offset}",
    );
}

#[test]
fn actual_nlt_preserves_all_component_selectors_precision_and_type_bytes() {
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let mut selectors = 0;
    for selector in 0..=u16::MAX {
        let [first, second] = selector.to_be_bytes();
        for components in [0, 1, 257, u16::MAX] {
            for offset in [0, usize::MAX] {
                assert_nlt_payload_case(&parser, &[first, second, 37, 3], components, offset);
                selectors += 1;
            }
        }
    }
    assert_eq!(selectors, 524_288);
    let mut headers = 0;
    for (selector, components) in [(0_u16, 0), (0, 1), (1, 1), (u16::MAX, 0)] {
        for packed in 0..=u8::MAX {
            for kind in 0..=u8::MAX {
                for length in [4, 19] {
                    let mut bytes = vec![0; length];
                    bytes[..2].copy_from_slice(&selector.to_be_bytes());
                    bytes[2] = packed;
                    bytes[3] = kind;
                    assert_nlt_payload_case(&parser, &bytes, components, usize::MAX);
                    headers += 1;
                }
            }
        }
    }
    assert_eq!(headers, 524_288);
    for length in 0..=24 {
        for pattern in [0, 255] {
            assert_nlt_payload_case(&parser, &vec![pattern; length], u16::MAX, usize::MAX);
        }
    }
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2)
    );
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.limits, &limits));
}

#[test]
fn actual_nlt_preserves_gamma_words_point_widths_caps_and_tail_bytes() {
    let limits = ResourceLimits::HARDENED;
    let mut parser = new_parser(&[], &limits).unwrap();
    parser.position = usize::MAX;
    let mut gamma = 0;
    for seed in [[1, 1, 0, 1, 0], [0x00ff_ffff; 5]] {
        for parameter in 0..5 {
            for byte in 0..3 {
                for value in 0..=u8::MAX {
                    let mut bytes = raw_nlt_gamma_payload(seed);
                    bytes[4 + 3 * parameter + byte] = value;
                    for offset in [0, usize::MAX] {
                        assert_eq!(
                            parser.decode_nlt_gamma(Segment {
                                marker: 0x1234,
                                offset,
                                payload: &bytes
                            }),
                            reference_nlt_gamma(&bytes, offset)
                        );
                        assert_nlt_payload_case(&parser, &bytes, 0, offset);
                        gamma += 1;
                    }
                }
            }
        }
    }
    assert_eq!(gamma, 15_360);
    let source = raw_nlt_gamma_payload([1, 1, 0, 1, 0]);
    let mut gamma_lengths = 0;
    for length in 0..=24 {
        let mut bytes = source.clone();
        bytes.resize(length, 0);
        for offset in [0, usize::MAX] {
            assert_eq!(
                parser.decode_nlt_gamma(Segment {
                    marker: 0x1234,
                    offset,
                    payload: &bytes
                }),
                reference_nlt_gamma(&bytes, offset),
            );
            gamma_lengths += 1;
        }
    }
    assert_eq!(gamma_lengths, 50);
    let mut frontiers = 0;
    for bits in 0..=u8::MAX {
        for stored in [0, 1, 2, 3, 31, 8191, 8192, u16::MAX] {
            for domain in [
                (0, 0),
                (0, 1),
                (0, u32::MAX),
                (1, 0),
                (u32::MAX, 0),
                (u32::MAX - 1, u32::MAX),
            ] {
                for kind in [2, 4] {
                    let source = raw_nlt_points_payload(kind, bits, stored, domain, &[0, u32::MAX]);
                    for variant in 0..3 {
                        let mut bytes = source.clone();
                        if variant == 0 {
                            bytes.pop();
                        } else if variant == 2 {
                            bytes.push(0);
                        }
                        for offset in [0, usize::MAX] {
                            assert_nlt_payload_case(&parser, &bytes, 0, offset);
                            frontiers += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(frontiers, 147_456);
    let mut admitted = 0;
    for bits in 1..=32 {
        let maximum = ((1_u64 << bits) - 1) as u32;
        for stored in [1_u16, 2, 7] {
            for kind in [2, 4] {
                for pattern in 0..4 {
                    let values: Vec<u32> = (0..=stored)
                        .map(|index| match pattern {
                            0 => 0,
                            1 => maximum,
                            2 => u32::from(index).min(maximum),
                            _ => {
                                if index % 2 == 0 {
                                    0
                                } else {
                                    maximum
                                }
                            }
                        })
                        .collect();
                    let bytes = raw_nlt_points_payload(kind, bits, stored, (0, u32::MAX), &values);
                    assert_nlt_payload_case(&parser, &bytes, 0, usize::MAX);
                    admitted += 1;
                }
            }
        }
    }
    assert_eq!(admitted, 768);
    let mut large = 0;
    for bits in [1, 8, 9, 16, 17, 31, 32] {
        let maximum = ((1_u64 << bits) - 1) as u32;
        for kind in [2, 4] {
            for pattern in 0..3 {
                let values: Vec<u32> = (0..8192)
                    .map(|index| {
                        if pattern == 0 {
                            0
                        } else if pattern == 1 || index % 2 != 0 {
                            maximum
                        } else {
                            0
                        }
                    })
                    .collect();
                let bytes = raw_nlt_points_payload(kind, bits, 8191, (0, u32::MAX), &values);
                assert_nlt_payload_case(&parser, &bytes, 0, usize::MAX);
                large += 1;
            }
        }
    }
    assert_eq!(large, 42);
    let mut rejected = 0;
    for bits in [1, 7, 9, 15, 17, 24, 25, 31] {
        for bad in 0..4 {
            let mut values = vec![0; 4];
            values[bad] = 1_u32 << bits;
            for kind in [2, 4] {
                let source = raw_nlt_points_payload(kind, bits, 3, (0, 1), &values);
                for variant in 0..3 {
                    let mut bytes = source.clone();
                    if variant == 0 {
                        bytes.pop();
                    } else if variant == 2 {
                        bytes.push(0);
                    }
                    for offset in [0, usize::MAX] {
                        assert_nlt_payload_case(&parser, &bytes, 0, offset);
                        rejected += 1;
                    }
                }
            }
        }
    }
    assert_eq!(rejected, 384);
    for bits in 0..=u8::MAX {
        let expected = if (1..=31).contains(&bits) {
            Ok(((1_u64 << bits) - 1) as u32)
        } else {
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::ArithmeticOverflow,
            })
        };
        assert_eq!(maximum_u32_for_bits(bits), expected);
    }
    let mut tails = 0;
    for byte in 0..=u8::MAX {
        for length in 0..=12 {
            let bytes = vec![byte; length];
            for start in [0, 1, 2, length, length + 1, usize::MAX] {
                for offset in [0, usize::MAX] {
                    let expected = match bytes.get(start..) {
                        Some(tail) => Ok(tail.to_vec()),
                        None => Err(DecodeError::MalformedInput {
                            offset: offset as u64,
                            kind: MalformedKind::InvalidMarkerLength,
                        }),
                    };
                    assert_eq!(
                        parser.copy_segment_tail(
                            Segment {
                                marker: 0x1234,
                                offset,
                                payload: &bytes
                            },
                            start
                        ),
                        expected
                    );
                    tails += 1;
                }
            }
        }
    }
    assert_eq!(tails, 39_936);
    assert_eq!(parser.position, usize::MAX);
}

fn assert_nlt_owner_case(
    bytes: &[u8],
    components: u16,
    mode: usize,
    limits: &ResourceLimits,
    budget: (u64, u64),
    offset: usize,
) {
    let selector = if bytes.len() >= 2 {
        u16::from_be_bytes([bytes[0], bytes[1]])
    } else {
        u16::MAX
    };
    let component = (selector != u16::MAX).then_some(selector);
    let seed = NonlinearPointTransform {
        component: Some(u16::MAX),
        precision: u8::MAX,
        signed: true,
        transform_type: u8::MAX,
        parameters: vec![255, 17],
        d_min: Some(u32::MAX),
        d_max: None,
        point_bits: Some(0),
        points: vec![u32::MAX, 0, 17],
        gamma_parameters: Some([0, 1, u32::MAX, 0, 17]),
    };
    let mut extensions = raw_owned_tile_part_fixture(0).part2_extensions;
    extensions.nonlinear_transforms = if mode == 0 {
        vec![]
    } else {
        vec![seed.clone()]
    };
    if mode == 2 {
        let mut first = seed.clone();
        first.component = component;
        let mut later = first.clone();
        later.precision = 0;
        later.parameters.clear();
        extensions.nonlinear_transforms.extend([first, seed, later]);
    }
    let (metadata, work) = budget;
    extensions.metadata_bytes = metadata;
    let mut expected = extensions.clone();
    let (mut result, next_work, next_metadata) =
        reference_extension_charge(bytes.len(), 17, work, metadata, limits);
    expected.metadata_bytes = next_metadata;
    if result.is_ok() {
        result = match reference_nlt_payload(bytes, components, offset) {
            Err(error) => Err(error),
            Ok(replacement) => {
                if let Some(existing) = expected
                    .nonlinear_transforms
                    .iter_mut()
                    .find(|entry| entry.component == replacement.component)
                {
                    *existing = replacement;
                } else {
                    expected.nonlinear_transforms.push(replacement);
                }
                Ok(())
            }
        };
    }
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, limits).unwrap();
    parser.position = 17;
    parser.work_units = work;
    parser.packet_length_bytes = u64::MAX;
    parser.packet_lengths = u64::MAX - 1;
    assert_eq!(
        parser.parse_nlt(
            Segment {
                marker: 0x1234,
                offset,
                payload: bytes
            },
            components,
            &mut extensions
        ),
        result
    );
    assert_eq!(extensions, expected);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (17, next_work, u64::MAX, u64::MAX - 1)
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, limits));
}

#[test]
fn actual_nlt_preserves_first_duplicate_all_owner_fields_and_ordered_budget_failures() {
    let base = ResourceLimits::HARDENED;
    let limits = [
        base,
        base.with_maximum_metadata_bytes(0).unwrap(),
        base.with_maximum_metadata_bytes(8).unwrap(),
        base.with_maximum_work_units(0).unwrap(),
        base.with_maximum_work_units(8).unwrap(),
        base.with_maximum_metadata_bytes(4)
            .unwrap()
            .with_maximum_work_units(0)
            .unwrap(),
    ];
    let gamma = raw_nlt_gamma_payload([1, 1, 0, 1, 0]);
    let mut bad_gamma = gamma.clone();
    bad_gamma[4..7].fill(0);
    let mut long_gamma = gamma.clone();
    long_gamma.push(0);
    let points = raw_nlt_points_payload(2, 7, 1, (0, 1), &[0, 127]);
    let bad_points = raw_nlt_points_payload(4, 7, 1, (0, 1), &[128, 0]);
    let mut short_points = points.clone();
    short_points.pop();
    let payloads = [
        vec![],
        vec![255, 255, 0],
        vec![255, 255, 0, 0],
        vec![0, 0, 0xa4, 3],
        vec![0, 1, 0xa6, 5],
        gamma.clone(),
        bad_gamma,
        long_gamma,
        points,
        bad_points,
        short_points,
        vec![255, 255, 255, 0],
    ];
    assert_eq!(payloads.len(), 12);
    let mut cases = 0;
    for limit in &limits {
        for bytes in &payloads {
            for components in [0, 1, 257, u16::MAX] {
                for mode in 0..3 {
                    for budget in [
                        (0, 0),
                        (0, u64::MAX),
                        (u64::MAX, 0),
                        (16_777_215, 8),
                        (u64::MAX - 4, u64::MAX - 4),
                    ] {
                        for offset in [0, usize::MAX] {
                            assert_nlt_owner_case(bytes, components, mode, limit, budget, offset);
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 8_640);
    let mut input = segment(NLT, &[255, 255, 0xa4, 3]);
    input.extend(segment(NLT, &gamma));
    let mut parser = new_parser(&input, &base).unwrap();
    let mut extensions = Part2Extensions::default();
    let raw = parser.read_segment().unwrap();
    parser.parse_nlt(raw, 0, &mut extensions).unwrap();
    let raw = parser.read_segment().unwrap();
    parser.parse_nlt(raw, 0, &mut extensions).unwrap();
    assert_eq!(
        extensions.nonlinear_transforms,
        vec![reference_nlt_payload(&gamma, 0, 8).unwrap()]
    );
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            extensions.metadata_bytes
        ),
        (31, 33, 31)
    );
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
}

fn reference_marker_words(
    bytes: &[u8],
    start: usize,
    offset: usize,
) -> Result<Vec<u16>, DecodeError> {
    let Some(tail) = bytes.get(start..) else {
        return Err(DecodeError::MalformedInput {
            offset: offset as u64,
            kind: MalformedKind::InvalidMarkerLength,
        });
    };
    let chunks = tail.chunks_exact(2);
    if !chunks.remainder().is_empty() {
        return Err(DecodeError::MalformedInput {
            offset: offset as u64,
            kind: MalformedKind::InvalidMarkerLength,
        });
    }
    Ok(chunks
        .map(|word| u16::from_be_bytes([word[0], word[1]]))
        .collect())
}

fn reference_cap_payload(bytes: &[u8], offset: usize) -> Result<(u32, Vec<u16>), DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    let Some(header) = bytes.get(..4) else {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    };
    let mask = u32::from_be_bytes([header[0], header[1], header[2], header[3]]);
    if mask == 0 {
        return Err(malformed(MalformedKind::InvalidProfile));
    }
    if bytes.len() != 4 + 2 * mask.count_ones() as usize {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    Ok((mask, reference_marker_words(bytes, 4, offset)?))
}

fn reference_profile_payload(bytes: &[u8], offset: usize) -> Result<Vec<u16>, DecodeError> {
    if bytes.len() < 2 {
        return Err(DecodeError::MalformedInput {
            offset: offset as u64,
            kind: MalformedKind::InvalidMarkerLength,
        });
    }
    let words = reference_marker_words(bytes, 0, offset)?;
    if words.last() == Some(&0) {
        return Err(DecodeError::MalformedInput {
            offset: offset as u64,
            kind: MalformedKind::InvalidProfile,
        });
    }
    Ok(words)
}

fn assert_profile_payload_case(parser: &Parser<'_>, bytes: &[u8], offset: usize) {
    let segment = Segment {
        marker: 0x1234,
        offset,
        payload: bytes,
    };
    assert_eq!(
        parser
            .parse_cap(segment)
            .map(|value| (value.p_cap(), value.c_capabilities().to_vec())),
        reference_cap_payload(bytes, offset),
    );
    assert_eq!(
        parser
            .parse_profile_number(segment)
            .map(|value| value.words().to_vec()),
        reference_profile_payload(bytes, offset),
    );
}

#[test]
fn actual_marker_word_reader_preserves_all_endian_pairs_and_odd_tail_offsets() {
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let mut cases = 0;
    for word in 0..=u16::MAX {
        let [first, second] = word.to_be_bytes();
        let bytes = [7, first, second, second, first, 255];
        for start in 0..=bytes.len() {
            for offset in [0, usize::MAX] {
                assert_eq!(
                    parser.read_marker_words(
                        Segment {
                            marker: 0x1234,
                            offset,
                            payload: &bytes
                        },
                        start
                    ),
                    reference_marker_words(&bytes, start, offset),
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 917_504);
    let mut frontiers = 0;
    for bytes in [vec![], vec![1], vec![1, 2, 3, 4]] {
        for start in [0, bytes.len(), bytes.len() + 1, usize::MAX] {
            for offset in [0, usize::MAX] {
                assert_eq!(
                    parser.read_marker_words(
                        Segment {
                            marker: 0x1234,
                            offset,
                            payload: &bytes
                        },
                        start
                    ),
                    reference_marker_words(&bytes, start, offset),
                );
                frontiers += 1;
            }
        }
    }
    assert_eq!(frontiers, 24);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2),
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));
}

#[test]
fn actual_profile_numbers_preserve_word_order_and_last_zero_error_precedence() {
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let mut cases = 0;
    for word in 0..=u16::MAX {
        let [first, second] = word.to_be_bytes();
        let payloads: &[&[u8]] = &[
            &[first, second],
            &[0, 0, first, second],
            &[first, second, 0, 0],
            &[first, second, 255],
        ];
        for bytes in payloads {
            for offset in [0, usize::MAX] {
                assert_profile_payload_case(&parser, bytes, offset);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 524_288);
    let mut frontiers = 0;
    for length in 0..=72 {
        for pattern in [0, 1, 0x55, 0xaa, 255] {
            for offset in [0, usize::MAX] {
                assert_profile_payload_case(&parser, &vec![pattern; length], offset);
                frontiers += 1;
            }
        }
    }
    assert_eq!(frontiers, 730);
    for words in [vec![], vec![0], vec![0, 1, 0], vec![u16::MAX, 0]] {
        let raw = ProfileNumber {
            words: words.clone(),
        };
        assert_eq!(raw.words(), words);
    }
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2),
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));
}

#[test]
fn actual_cap_preserves_mask_halves_bit_counts_length_order_and_reader_join() {
    let limits = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.position = usize::MAX;
    parser.work_units = u64::MAX;
    parser.packet_length_bytes = u64::MAX - 1;
    parser.packet_lengths = u64::MAX - 2;
    let mut cases = 0;
    for half in 0..=u16::MAX {
        for mask in [u32::from(half), u32::from(half) << 16] {
            assert_eq!(u32::from(count_set_bits(mask)), mask.count_ones());
            let mut source = mask.to_be_bytes().to_vec();
            for index in 0..mask.count_ones() {
                let word = half.wrapping_add(index as u16).wrapping_mul(31337);
                source.extend(word.to_be_bytes());
            }
            for variant in 0..3 {
                let mut bytes = source.clone();
                if variant == 0 {
                    bytes.pop();
                } else if variant == 2 {
                    bytes.push(255);
                }
                for offset in [0, usize::MAX] {
                    assert_profile_payload_case(&parser, &bytes, offset);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 786_432);
    let mut frontiers = 0;
    for mask in [
        0_u32,
        1,
        u32::MAX,
        0x5555_5555,
        0xaaaa_aaaa,
        PART_15_CAPABILITY_FLAG,
    ]
    .into_iter()
    .chain((0..=32).map(|bits| {
        if bits == 0 {
            0
        } else {
            u32::MAX >> (32 - bits)
        }
    })) {
        assert_eq!(u32::from(count_set_bits(mask)), mask.count_ones());
        for count in 0..=33 {
            let mut bytes = mask.to_be_bytes().to_vec();
            bytes.extend((0..count).flat_map(|index| (index as u16).to_be_bytes()));
            for offset in [0, usize::MAX] {
                assert_profile_payload_case(&parser, &bytes, offset);
                frontiers += 1;
            }
        }
    }
    assert_eq!(frontiers, 2_652);
    let raw = ExtendedCapabilities {
        p_cap: 0,
        c_capabilities: vec![0, u16::MAX, 17],
    };
    assert_eq!(raw.p_cap(), 0);
    assert_eq!(raw.c_capabilities(), &[0, u16::MAX, 17]);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (usize::MAX, u64::MAX, u64::MAX - 1, u64::MAX - 2),
    );
    assert_eq!(parser.input, &input);
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert!(core::ptr::eq(parser.limits, &limits));

    let cap = [0, 2, 0, 0, 0, 8];
    let mut stream = segment(CAP, &cap);
    stream.extend(segment(PRF, &[0, 0, 0x12, 0x34]));
    stream.extend(segment(CPF, &[0, 0]));
    let limits = ResourceLimits::HARDENED;
    let mut reader = new_parser(&stream, &limits).unwrap();
    let raw = reader.read_segment().unwrap();
    let capabilities = reader.parse_cap(raw).unwrap();
    assert_eq!(capabilities.p_cap(), PART_15_CAPABILITY_FLAG);
    assert_eq!(capabilities.c_capabilities(), &[8]);
    assert_eq!(capabilities.part15_value(), Some(8));
    let raw = reader.read_segment().unwrap();
    assert_eq!(
        reader.parse_profile_number(raw).unwrap().words(),
        &[0, 0x1234]
    );
    let raw = reader.read_segment().unwrap();
    assert_eq!(
        reader.parse_profile_number(raw),
        Err(DecodeError::MalformedInput {
            offset: 18,
            kind: MalformedKind::InvalidProfile
        }),
    );
    assert_eq!((reader.position, reader.work_units), (stream.len(), 3));
    assert!(core::ptr::eq(reader.input.as_ptr(), stream.as_ptr()));
}

fn reference_cbd_payload(
    bytes: &[u8],
    components: u16,
    offset: usize,
    depths: &mut Vec<ComponentBitDepth>,
) -> Result<(), DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    let Some(header) = bytes.get(..2) else {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    };
    let descriptor = u16::from_be_bytes([header[0], header[1]]);
    let repeated = descriptor / 32768 == 1;
    let count = descriptor % 32768;
    let expected = if repeated { 3 } else { 2 + usize::from(count) };
    if count != components || bytes.len() != expected {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    depths.clear();
    for packed in &bytes[2..] {
        let precision = packed % 128 + 1;
        if precision > 38 {
            return Err(malformed(MalformedKind::InvalidTransform));
        }
        depths.push(ComponentBitDepth {
            precision,
            signed: packed / 128 == 1,
        });
    }
    if repeated {
        depths.resize(usize::from(components).max(1), depths[0]);
    }
    Ok(())
}

fn assert_cbd_owner_case(
    bytes: &[u8],
    components: u16,
    limits: &ResourceLimits,
    budget: (u64, u64),
    offset: usize,
) {
    let (metadata, work) = budget;
    let mut extensions = raw_owned_tile_part_fixture(0).part2_extensions;
    extensions.component_bit_depths.push(ComponentBitDepth {
        precision: u8::MAX,
        signed: true,
    });
    extensions.metadata_bytes = metadata;
    let mut expected = extensions.clone();
    let (mut result, next_work, next_metadata) =
        reference_extension_charge(bytes.len(), 17, work, metadata, limits);
    expected.metadata_bytes = next_metadata;
    if result.is_ok() {
        result = reference_cbd_payload(
            bytes,
            components,
            offset,
            &mut expected.component_bit_depths,
        );
    }
    let input = [0xa5, 0x5a];
    let mut parser = new_parser(&input, limits).unwrap();
    parser.position = 17;
    parser.work_units = work;
    parser.packet_length_bytes = u64::MAX;
    parser.packet_lengths = u64::MAX - 1;
    assert_eq!(
        parser.parse_cbd(
            Segment {
                marker: 0x1234,
                offset,
                payload: bytes,
            },
            components,
            &mut extensions,
        ),
        result,
        "bytes={bytes:?}, components={components}, budget={budget:?}, offset={offset}"
    );
    assert_eq!(extensions, expected);
    assert_eq!(
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths
        ),
        (17, next_work, u64::MAX, u64::MAX - 1)
    );
    assert!(core::ptr::eq(parser.limits, limits));
    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
    assert_eq!(parser.input, &input);
}

#[test]
fn actual_cbd_preserves_all_raw_descriptors_and_partial_depth_prefixes() {
    let limits = ResourceLimits::HARDENED;
    let mut descriptors = 0;
    for descriptor in 0..=u16::MAX {
        for components in [0, 1, 3, u16::MAX] {
            for length in [2, 3, 5] {
                let mut bytes = vec![0xa4; length];
                bytes[..2].copy_from_slice(&descriptor.to_be_bytes());
                assert_cbd_owner_case(&bytes, components, &limits, (0, 0), usize::MAX);
                descriptors += 1;
            }
        }
    }
    assert_eq!(descriptors, 786_432);
    let mut prefixes = 0;
    for count in 1_u16..=8 {
        for position in 0..usize::from(count) {
            for packed in 0..=u8::MAX {
                for mutation in 0..3 {
                    let mut bytes = count.to_be_bytes().to_vec();
                    bytes.resize(usize::from(count) + 2, 0xa4);
                    bytes[position + 2] = packed;
                    if mutation == 1 && position > 0 {
                        bytes[2] = 0x7f;
                    } else if mutation == 2 && position + 1 < usize::from(count) {
                        bytes[usize::from(count) + 1] = 0x7f;
                    }
                    assert_cbd_owner_case(&bytes, count, &limits, (0, 0), 9);
                    prefixes += 1;
                }
            }
        }
    }
    assert_eq!(prefixes, 27_648);
    let mut repeated = 0;
    for count in [0_u16, 1, 2, 3, 31, 32767] {
        for packed in 0..=u8::MAX {
            let [first, second] = (count + 32768).to_be_bytes();
            for offset in [0, usize::MAX] {
                assert_cbd_owner_case(&[first, second, packed], count, &limits, (0, 0), offset);
                repeated += 1;
            }
        }
    }
    assert_eq!(repeated, 3_072);
}

#[test]
fn actual_cbd_preserves_budget_header_and_reader_order_with_all_owner_fields() {
    let base = ResourceLimits::HARDENED;
    let limits = [
        base,
        base.with_maximum_metadata_bytes(0).unwrap(),
        base.with_maximum_metadata_bytes(6).unwrap(),
        base.with_maximum_metadata_bytes(8).unwrap(),
        base.with_maximum_work_units(0).unwrap(),
        base.with_maximum_work_units(8).unwrap(),
        base.with_maximum_metadata_bytes(6)
            .unwrap()
            .with_maximum_work_units(0)
            .unwrap(),
    ];
    let payloads: &[&[u8]] = &[
        &[],
        &[0],
        &[0, 0],
        &[0x80, 0, 0],
        &[0, 3, 0xa4, 0, 37],
        &[0, 3, 0xa4, 38, 0],
        &[0, 3, 38, 0xa4, 0],
        &[0x80, 3, 0xa4],
        &[0x80, 3, 0xa6],
        &[0, 1, 127, 0],
        &[255, 255],
    ];
    let mut frontiers = 0;
    for limit in &limits {
        for bytes in payloads {
            for components in [0, 1, 3, u16::MAX] {
                for metadata in [0, 1, 7, 16_777_215, 16_777_216, u64::MAX - 4, u64::MAX] {
                    for work in [0, 1, 8, u64::MAX - 4, u64::MAX] {
                        for offset in [0, usize::MAX] {
                            assert_cbd_owner_case(
                                bytes,
                                components,
                                limit,
                                (metadata, work),
                                offset,
                            );
                            frontiers += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(frontiers, 21_560);
    let input = [255, 120, 0, 5, 0x80, 3, 0xa4, 255, 254, 0, 2];
    let mut parser = new_parser(&input, &base).unwrap();
    let segment = parser.read_segment().unwrap();
    let mut extensions = Part2Extensions::default();
    parser.parse_cbd(segment, 3, &mut extensions).unwrap();
    assert_eq!(
        extensions.component_bit_depths,
        vec![
            ComponentBitDepth {
                precision: 37,
                signed: true
            };
            3
        ]
    );
    assert_eq!(
        (
            extensions.metadata_bytes,
            parser.work_units,
            parser.position
        ),
        (7, 8, 7)
    );
    let segment = parser.read_segment().unwrap();
    assert_eq!(
        parser.parse_cbd(segment, 3, &mut extensions),
        Err(DecodeError::MalformedInput {
            offset: 7,
            kind: MalformedKind::InvalidMarkerLength,
        })
    );
    assert_eq!(extensions.component_bit_depths.len(), 3);
    assert_eq!(
        (
            extensions.metadata_bytes,
            parser.work_units,
            parser.position
        ),
        (11, 13, 11)
    );
}

fn reference_extension_charge(
    length: usize,
    cursor: usize,
    work: u64,
    metadata: u64,
    limits: &ResourceLimits,
) -> (Result<(), DecodeError>, u64, u64) {
    let overflow = || DecodeError::MalformedInput {
        offset: cursor as u64,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let amount = length as u128 + 4;
    if amount > u128::from(u64::MAX) {
        return (Err(overflow()), work, metadata);
    }
    let total = u128::from(metadata) + amount;
    if total > u128::from(u64::MAX) {
        return (Err(overflow()), work, metadata);
    }
    let total = total as u64;
    if total > limits.maximum_metadata_bytes() {
        return (
            Err(DecodeError::LimitExceeded {
                resource: Resource::MetadataBytes,
                limit: limits.maximum_metadata_bytes(),
                actual: total,
            }),
            work,
            total,
        );
    }
    let charged = u128::from(work) + amount;
    if charged > u128::from(u64::MAX) {
        return (Err(overflow()), work, total);
    }
    let charged = charged as u64;
    let result = if charged > limits.maximum_work_units() {
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: charged,
        })
    } else {
        Ok(())
    };
    (result, charged, total)
}

#[test]
fn actual_crg_preserves_all_owner_fields_partial_budget_commits_and_registration_bytes() {
    let base = ResourceLimits::HARDENED;
    let limits = [
        base,
        base.with_maximum_metadata_bytes(0).unwrap(),
        base.with_maximum_metadata_bytes(4).unwrap(),
        base.with_maximum_metadata_bytes(8).unwrap(),
        base.with_maximum_work_units(0).unwrap(),
        base.with_maximum_work_units(8).unwrap(),
        base.with_maximum_metadata_bytes(4)
            .unwrap()
            .with_maximum_work_units(0)
            .unwrap(),
    ];
    let mut matrix = 0;
    for limit in &limits {
        for components in [0_u16, 1, 2, 3, 63, 64, 65, 255, 256, 257, u16::MAX] {
            let source: Vec<u8> = (0..usize::from(components))
                .flat_map(|index| {
                    let word = u16::try_from(index).unwrap();
                    let [h0, h1] = word.to_be_bytes();
                    let [v0, v1] = word.wrapping_mul(31337).wrapping_add(17).to_be_bytes();
                    [h0, h1, v0, v1]
                })
                .collect();
            for variant in 0..3 {
                let mut bytes = source.clone();
                if variant == 1 {
                    bytes.pop();
                } else if variant == 2 {
                    bytes.push(0);
                }
                for duplicate in [false, true] {
                    for metadata in [0, 1, 7, 16_777_215, 16_777_216, u64::MAX - 4, u64::MAX] {
                        for work in [0, 1, 8, u64::MAX - 4, u64::MAX] {
                            for offset in [0, usize::MAX] {
                                let mut extensions =
                                    raw_owned_tile_part_fixture(0).part2_extensions;
                                if !duplicate {
                                    extensions.component_registrations.clear();
                                }
                                assert_eq!(
                                    !extensions.component_registrations.is_empty(),
                                    duplicate
                                );
                                extensions.metadata_bytes = metadata;
                                let before = extensions.clone();
                                let (charged_result, next_work, next_metadata) =
                                    reference_extension_charge(
                                        bytes.len(),
                                        17,
                                        work,
                                        metadata,
                                        limit,
                                    );
                                let mut expected_charge = before.clone();
                                expected_charge.metadata_bytes = next_metadata;
                                let mut charge_parser = new_parser(&[], limit).unwrap();
                                charge_parser.position = 17;
                                charge_parser.work_units = work;
                                charge_parser.packet_length_bytes = u64::MAX;
                                charge_parser.packet_lengths = u64::MAX - 1;
                                let mut charge_extensions = before.clone();
                                assert_eq!(
                                    charge_parser.charge_extension_metadata(
                                        Segment {
                                            marker: 0x1234,
                                            offset,
                                            payload: &bytes
                                        },
                                        &mut charge_extensions
                                    ),
                                    charged_result,
                                );
                                assert_eq!(charge_extensions, expected_charge);
                                assert_eq!(
                                    (
                                        charge_parser.position,
                                        charge_parser.work_units,
                                        charge_parser.packet_length_bytes,
                                        charge_parser.packet_lengths
                                    ),
                                    (17, next_work, u64::MAX, u64::MAX - 1)
                                );
                                let mut expected = expected_charge;
                                let result = if charged_result.is_err() {
                                    charged_result
                                } else if bytes.len() != 4 * usize::from(components) {
                                    Err(DecodeError::MalformedInput {
                                        offset: offset as u64,
                                        kind: MalformedKind::InvalidMarkerLength,
                                    })
                                } else if duplicate {
                                    Err(DecodeError::MalformedInput {
                                        offset: offset as u64,
                                        kind: MalformedKind::InvalidMarkerOrder,
                                    })
                                } else {
                                    expected.component_registrations = bytes
                                        .chunks_exact(4)
                                        .map(|part| ComponentRegistration {
                                            horizontal: u16::from_be_bytes([part[0], part[1]]),
                                            vertical: u16::from_be_bytes([part[2], part[3]]),
                                        })
                                        .collect();
                                    Ok(())
                                };
                                let mut parser = new_parser(&[], limit).unwrap();
                                parser.position = 17;
                                parser.work_units = work;
                                parser.packet_length_bytes = u64::MAX;
                                parser.packet_lengths = u64::MAX - 1;
                                assert_eq!(
                                    parser.parse_crg(
                                        Segment {
                                            marker: 0x1234,
                                            offset,
                                            payload: &bytes
                                        },
                                        components,
                                        &mut extensions
                                    ),
                                    result
                                );
                                assert_eq!(extensions, expected);
                                assert_eq!(
                                    (
                                        parser.position,
                                        parser.work_units,
                                        parser.packet_length_bytes,
                                        parser.packet_lengths
                                    ),
                                    (17, next_work, u64::MAX, u64::MAX - 1)
                                );
                                assert!(core::ptr::eq(parser.limits, limit));
                                assert!(parser.input.is_empty());
                                matrix += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(matrix, 32_340);
    let mut words = 0;
    for horizontal in 0..=u16::MAX {
        let vertical = horizontal.wrapping_mul(31337).wrapping_add(17);
        let [h0, h1] = horizontal.to_be_bytes();
        let [v0, v1] = vertical.to_be_bytes();
        let bytes = [h0, h1, v0, v1];
        for offset in [0, usize::MAX] {
            let mut parser = new_parser(&[], &base).unwrap();
            let mut extensions = Part2Extensions::default();
            parser
                .parse_crg(
                    Segment {
                        marker: 0x1234,
                        offset,
                        payload: &bytes,
                    },
                    1,
                    &mut extensions,
                )
                .unwrap();
            assert_eq!(
                extensions.component_registrations,
                vec![ComponentRegistration {
                    horizontal,
                    vertical
                }]
            );
            assert_eq!((extensions.metadata_bytes, parser.work_units), (8, 8));
            words += 1;
        }
    }
    assert_eq!(words, 131_072);
    let input = [255, 99, 0, 10, 0, 1, 128, 2, 255, 254, 0, 0];
    let mut parser = new_parser(&input, &base).unwrap();
    let segment = parser.read_segment().unwrap();
    let mut extensions = Part2Extensions::default();
    parser.parse_crg(segment, 2, &mut extensions).unwrap();
    assert_eq!(
        extensions.component_registrations,
        vec![
            ComponentRegistration {
                horizontal: 1,
                vertical: 0x8002
            },
            ComponentRegistration {
                horizontal: u16::MAX - 1,
                vertical: 0
            },
        ]
    );
    assert_eq!(
        (
            extensions.metadata_bytes,
            parser.work_units,
            parser.position
        ),
        (12, 13, input.len())
    );
    let mut empty_parser = new_parser(&[], &base).unwrap();
    let mut empty = Part2Extensions::default();
    for _ in 0..2 {
        empty_parser
            .parse_crg(
                Segment {
                    marker: 0x1234,
                    offset: usize::MAX,
                    payload: &[],
                },
                0,
                &mut empty,
            )
            .unwrap();
    }
    assert!(empty.component_registrations.is_empty());
    assert_eq!((empty.metadata_bytes, empty_parser.work_units), (8, 8));
}

fn reference_quantization_subbands(coding: CodingStyle) -> usize {
    1 + coding
        .decomposition_directions
        .iter()
        .take(usize::from(coding.decomposition_levels))
        .map(|direction| match direction {
            DecompositionDirection::None => 0,
            DecompositionDirection::Horizontal | DecompositionDirection::Vertical => 1,
            DecompositionDirection::TwoDimensional => 3,
        })
        .sum::<usize>()
}

fn reference_raw_quantization(
    bytes: &[u8],
    offset: usize,
    coding: CodingStyle,
) -> Result<Quantization, DecodeError> {
    let malformed = |kind| DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    };
    let header = *bytes
        .first()
        .ok_or_else(|| malformed(MalformedKind::InvalidMarkerLength))?;
    let style = match header % 32 {
        0 => QuantizationStyle::None,
        1 => QuantizationStyle::ScalarDerived,
        2 => QuantizationStyle::ScalarExpounded,
        _ => return Err(malformed(MalformedKind::InvalidQuantization)),
    };
    let bands = reference_quantization_subbands(coding);
    let expected = match style {
        QuantizationStyle::None => bands,
        QuantizationStyle::ScalarDerived => 2,
        QuantizationStyle::ScalarExpounded => 2 * bands,
    };
    if bytes.len() - 1 != expected {
        return Err(malformed(MalformedKind::InvalidMarkerLength));
    }
    if matches!(style, QuantizationStyle::None) && bytes[1..].iter().any(|byte| byte % 8 != 0) {
        return Err(malformed(MalformedKind::InvalidQuantization));
    }
    let count = if matches!(style, QuantizationStyle::ScalarDerived) {
        1
    } else {
        bands
    };
    let mut steps = [QuantizationStep {
        exponent: 0,
        mantissa: 0,
    }; 97];
    if count > steps.len() {
        return Err(malformed(MalformedKind::InvalidQuantization));
    }
    for (index, step) in steps[..count].iter_mut().enumerate() {
        *step = if matches!(style, QuantizationStyle::None) {
            QuantizationStep {
                exponent: bytes[1 + index] / 8,
                mantissa: 0,
            }
        } else {
            let word = u16::from_be_bytes([bytes[1 + 2 * index], bytes[2 + 2 * index]]);
            QuantizationStep {
                exponent: (word / 2048) as u8,
                mantissa: word % 2048,
            }
        };
    }
    Ok(Quantization {
        style,
        guard_bits: header / 32,
        step_count: u16::try_from(count).unwrap(),
        steps,
    })
}

fn raw_quantization_payload(header: u8, coding: CodingStyle) -> Vec<u8> {
    let count = reference_quantization_subbands(coding);
    let mut bytes = vec![header];
    match header % 32 {
        0 => bytes.extend((0..count).map(|index| u8::try_from(index % 32).unwrap() * 8)),
        1 | 2 => {
            let total = if header % 32 == 1 { 1 } else { count };
            for index in 0..total {
                bytes.extend(
                    u16::try_from(index)
                        .unwrap()
                        .wrapping_mul(2089)
                        .wrapping_add(0x8123)
                        .to_be_bytes(),
                );
            }
        }
        _ => {}
    }
    bytes
}

#[test]
fn actual_raw_quantization_derives_all_steps_defaults_and_ordered_errors() {
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let mut seed = reference_raw_coding_style(&[0, 0, 0, 1, 0, 0, 0, 0, 0, 1], 0, &limits).unwrap();
    seed.layers = 0;
    seed.code_block_width = 0;
    seed.code_block_height = u16::MAX;
    seed.decomposition_structure = Some(127);
    seed.transform = WaveletTransform::Arbitrary(255);
    let mut words = 0;
    for style in [1, 2] {
        for word in 0..=u16::MAX {
            let [high, low] = word.to_be_bytes();
            for guard in [0, 7] {
                let bytes = [(guard << 5) | style, high, low];
                for offset in [0, usize::MAX] {
                    let expected = reference_raw_quantization(&bytes, offset, seed);
                    assert_eq!(parser.parse_qcd_payload(offset, &bytes, seed), expected);
                    assert_eq!(
                        parser.parse_qcd(
                            Segment {
                                marker: 0x1234,
                                offset,
                                payload: &bytes
                            },
                            seed
                        ),
                        expected
                    );
                    words += 1;
                }
            }
        }
    }
    assert_eq!(words, 524_288);
    let mut headers = 0;
    for levels in 0..=u8::MAX {
        for pattern in 0..5 {
            let mut coding = seed;
            coding.decomposition_levels = levels;
            coding.decomposition_directions = core::array::from_fn(|index| match pattern {
                0 => DecompositionDirection::None,
                1 => DecompositionDirection::TwoDimensional,
                2 => DecompositionDirection::Horizontal,
                3 => DecompositionDirection::Vertical,
                _ => match index % 4 {
                    0 => DecompositionDirection::None,
                    1 => DecompositionDirection::Horizontal,
                    2 => DecompositionDirection::Vertical,
                    _ => DecompositionDirection::TwoDimensional,
                },
            });
            for header in 0..=u8::MAX {
                let source = raw_quantization_payload(header, coding);
                for variant in 0..3 {
                    let mut bytes = source.clone();
                    if variant == 1 {
                        bytes.pop();
                    } else if variant == 2 {
                        bytes.push(0);
                    }
                    for offset in [0, usize::MAX] {
                        let expected = reference_raw_quantization(&bytes, offset, coding);
                        assert_eq!(parser.parse_qcd_payload(offset, &bytes, coding), expected);
                        assert_eq!(
                            parser.parse_qcd(
                                Segment {
                                    marker: 0x1234,
                                    offset,
                                    payload: &bytes
                                },
                                coding
                            ),
                            expected
                        );
                        headers += 1;
                    }
                }
            }
        }
    }
    assert_eq!(headers, 1_966_080);
    let mut low_bits = 0;
    for levels in [0, 1, 31, 32, 255] {
        let mut coding = seed;
        coding.decomposition_levels = levels;
        coding.decomposition_directions = [DecompositionDirection::TwoDimensional; 32];
        let count = reference_quantization_subbands(coding);
        for index in 0..count {
            for byte in 0..=u8::MAX {
                let mut bytes = vec![0; count + 1];
                bytes[0] = 0xe0;
                bytes[index + 1] = byte;
                for offset in [0, usize::MAX] {
                    assert_eq!(
                        parser.parse_qcd_payload(offset, &bytes, coding),
                        reference_raw_quantization(&bytes, offset, coding)
                    );
                    low_bits += 1;
                }
            }
        }
    }
    assert_eq!(low_bits, 150_016);
    assert_eq!(words + headers + low_bits, 2_640_384);
}

#[test]
fn actual_component_quantization_binds_prefix_bytes_defaults_and_reader() {
    fn reference(
        bytes: &[u8],
        offset: usize,
        components: u16,
        coding: CodingStyle,
    ) -> Result<(u16, Quantization), DecodeError> {
        let malformed = |kind| DecodeError::MalformedInput {
            offset: offset as u64,
            kind,
        };
        let width = if components < 257 { 1 } else { 2 };
        if bytes.len() < width {
            return Err(malformed(MalformedKind::InvalidMarkerLength));
        }
        let component = if width == 1 {
            u16::from(bytes[0])
        } else {
            u16::from_be_bytes([bytes[0], bytes[1]])
        };
        if component >= components {
            return Err(malformed(MalformedKind::InvalidQuantization));
        }
        reference_raw_quantization(&bytes[width..], offset, coding).map(|value| (component, value))
    }
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let seed = reference_raw_coding_style(&[0, 0, 0, 1, 0, 0, 0, 0, 0, 1], 0, &limits).unwrap();
    let mut cases = 0;
    for pattern in 0..4 {
        let mut coding = seed;
        coding.decomposition_levels = if pattern == 0 { 0 } else { 255 };
        coding.decomposition_directions = core::array::from_fn(|index| match pattern {
            0 | 1 => DecompositionDirection::TwoDimensional,
            2 => DecompositionDirection::None,
            _ => {
                if index % 2 == 0 {
                    DecompositionDirection::Horizontal
                } else {
                    DecompositionDirection::Vertical
                }
            }
        });
        for components in [0, 1, 256, 257, u16::MAX] {
            let width = if components < 257 { 1 } else { 2 };
            for component in [0_u16, 1, 255, 256, 65534, 65535] {
                let prefix = if width == 1 {
                    vec![(component % 256) as u8]
                } else {
                    component.to_be_bytes().to_vec()
                };
                for header in 0..=u8::MAX {
                    let quantization = raw_quantization_payload(header, coding);
                    for variant in 0..3 {
                        let mut bytes = prefix.clone();
                        if variant == 0 {
                            bytes.extend(&quantization);
                        } else if variant == 1 {
                            bytes.truncate(width - 1);
                        }
                        for offset in [0, usize::MAX] {
                            assert_eq!(
                                parser.parse_qcc(
                                    Segment {
                                        marker: 0x1234,
                                        offset,
                                        payload: &bytes
                                    },
                                    components,
                                    coding
                                ),
                                reference(&bytes, offset, components, coding),
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 184_320);
    let payload = [0, 1, 0xe1, 0xff, 0xff];
    let mut input = vec![255, 93];
    input.extend(u16::try_from(payload.len() + 2).unwrap().to_be_bytes());
    input.extend(payload);
    let mut reader = new_parser(&input, &limits).unwrap();
    let segment = reader.read_segment().unwrap();
    let actual = reader.parse_qcc(segment, 257, seed).unwrap();
    assert_eq!(Ok(actual), reference(&payload, 0, 257, seed));
    assert_eq!(actual.0, 1);
    assert_eq!(actual.1.guard_bits, 7);
    assert_eq!(actual.1.step_count, 1);
    assert_eq!(
        actual.1.steps[0],
        QuantizationStep {
            exponent: 31,
            mantissa: 2047
        }
    );
    assert!(
        actual.1.steps[1..]
            .iter()
            .all(|value| value.exponent == 0 && value.mantissa == 0)
    );
    assert_eq!(reader.position, input.len());
    assert_eq!(reader.work_units, 1);
}

#[test]
fn actual_component_index_preserves_width_threshold_error_kind_and_marker_independence() {
    let limits = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limits).unwrap();
    let mut cases = 0;
    for components in [0, 1, 256, 257, u16::MAX] {
        let width = if components < 257 { 1 } else { 2 };
        for word in 0..=u16::MAX {
            let [high, low] = word.to_be_bytes();
            let bytes = [high, low, 0xa5];
            let component = if width == 1 { u16::from(high) } else { word };
            for length in 0..=bytes.len() {
                for kind in [
                    MalformedKind::InvalidCodingStyle,
                    MalformedKind::InvalidQuantization,
                ] {
                    for offset in [0, usize::MAX] {
                        let expected = if length < width {
                            Err(DecodeError::MalformedInput {
                                offset: offset as u64,
                                kind: MalformedKind::InvalidMarkerLength,
                            })
                        } else if component >= components {
                            Err(DecodeError::MalformedInput {
                                offset: offset as u64,
                                kind,
                            })
                        } else {
                            Ok((component, width))
                        };
                        let segment = Segment {
                            marker: if high % 2 == 0 { 0xff53 } else { 0x1234 },
                            offset,
                            payload: &bytes[..length],
                        };
                        assert_eq!(
                            parser.parse_component_index(segment, components, kind),
                            expected
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 5_242_880);
}

#[test]
fn actual_raw_component_styles_preserve_source_defaults_selectors_and_first_errors() {
    fn reference(
        bytes: &[u8],
        offset: usize,
        components: u16,
        default: CodingStyle,
        limits: &ResourceLimits,
    ) -> Result<(u16, CodingStyle), DecodeError> {
        let malformed = |kind| DecodeError::MalformedInput {
            offset: offset as u64,
            kind,
        };
        let width = if components < 257 { 1 } else { 2 };
        if bytes.len() < width {
            return Err(malformed(MalformedKind::InvalidMarkerLength));
        }
        let component = if width == 1 {
            u16::from(bytes[0])
        } else {
            u16::from_be_bytes([bytes[0], bytes[1]])
        };
        if component >= components {
            return Err(malformed(MalformedKind::InvalidCodingStyle));
        }
        if bytes.len() < width + 6 {
            return Err(malformed(MalformedKind::InvalidMarkerLength));
        }
        let scoc = bytes[width];
        if scoc > 1 {
            return Err(malformed(MalformedKind::InvalidCodingStyle));
        }
        let parameters = &bytes[width + 1..];
        let structure = if parameters[0] >= 128 {
            let index = parameters[0] - 128;
            if index == 0 {
                return Err(malformed(MalformedKind::InvalidCodingStyle));
            }
            Some(index)
        } else {
            None
        };
        if parameters.len() > 38 {
            return Err(malformed(MalformedKind::InvalidMarkerLength));
        }
        let mut cod = vec![
            scoc + 2 * u8::from(default.sop_markers) + 4 * u8::from(default.eph_markers),
            match default.progression_order {
                ProgressionOrder::Lrcp => 0,
                ProgressionOrder::Rlcp => 1,
                ProgressionOrder::Rpcl => 2,
                ProgressionOrder::Pcrl => 3,
                ProgressionOrder::Cprl => 4,
            },
        ];
        cod.extend(default.layers.to_be_bytes());
        cod.push(u8::from(default.multiple_component_transform));
        cod.extend(parameters);
        if structure.is_some() {
            cod[5] = default.decomposition_levels;
        }
        let mut style = reference_raw_coding_style(&cod, offset, limits)?;
        style.decomposition_structure = structure;
        Ok((component, style))
    }

    let base = ResourceLimits::HARDENED;
    let limits = [
        base,
        base.with_coding_style_limits_for_test(0, 0),
        base.with_coding_style_limits_for_test(u16::MAX, u8::MAX),
    ];
    let seed = reference_raw_coding_style(&[6, 0, 0, 1, 0, 2, 0, 0, 0, 1], 0, &base).unwrap();
    let orders = [
        ProgressionOrder::Lrcp,
        ProgressionOrder::Rlcp,
        ProgressionOrder::Rpcl,
        ProgressionOrder::Pcrl,
        ProgressionOrder::Cprl,
    ];
    let mut defaults = Vec::new();
    for (index, order) in orders.into_iter().enumerate() {
        let mut default = seed;
        default.progression_order = order;
        default.layers = [0, 1, 256, u16::MAX, 2][index];
        default.multiple_component_transform = index % 2 == 1;
        default.sop_markers = index % 2 == 1;
        default.eph_markers = index / 2 % 2 == 1;
        default.decomposition_levels = [0, 1, 32, 255, 2][index];
        default.decomposition_structure = Some(127);
        default.code_block_width = 0;
        default.code_block_height = 0;
        default.code_block_style = 255;
        default.transform = WaveletTransform::Arbitrary(255);
        default.precincts_defined = true;
        default.precinct_exponents = [(0, 0); 33];
        defaults.push(default);
    }
    defaults.push(seed);
    let mut cases = 0;
    let mut successes = 0;
    for default in &defaults {
        for components in [0, 1, 256, 257, u16::MAX] {
            let width = if components < 257 { 1 } else { 2 };
            for variant in 0..3 {
                let mut source = vec![0; width];
                source.push(u8::from(variant == 2));
                source.extend([if variant == 1 { 0x81 } else { 0 }, 0, 0, 0, 1]);
                if variant == 2 {
                    source.push(0x21);
                }
                for position in 0..9 {
                    for byte in 0..=u8::MAX {
                        let mut bytes = source.clone();
                        bytes.resize(bytes.len().max(position + 1), 0);
                        bytes[position] = byte;
                        for limit in &limits {
                            let parser = new_parser(&[], limit).unwrap();
                            for offset in [0, usize::MAX] {
                                let expected =
                                    reference(&bytes, offset, components, *default, limit);
                                let actual = parser.parse_coc(
                                    Segment {
                                        marker: 0x1234,
                                        offset,
                                        payload: &bytes,
                                    },
                                    components,
                                    *default,
                                );
                                assert_eq!(actual, expected);
                                successes += usize::from(actual.is_ok());
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 1_244_160);
    assert!(successes > 1_000);
    let mut frontiers = 0;
    for default in &defaults {
        for components in [0, 1, 256, 257, u16::MAX] {
            let width = if components < 257 { 1 } else { 2 };
            for length in 0..=45 {
                for scoc in [0, 1, 2, 255] {
                    for selector in [0, 128, 129, 255] {
                        let mut bytes = vec![0; length];
                        if let Some(value) = bytes.get_mut(width) {
                            *value = scoc;
                        }
                        if let Some(value) = bytes.get_mut(width + 1) {
                            *value = selector;
                        }
                        for limit in &limits {
                            let parser = new_parser(&[], limit).unwrap();
                            for offset in [0, usize::MAX] {
                                assert_eq!(
                                    parser.parse_coc(
                                        Segment {
                                            marker: 0xff53,
                                            offset,
                                            payload: &bytes
                                        },
                                        components,
                                        *default,
                                    ),
                                    reference(&bytes, offset, components, *default, limit),
                                );
                                frontiers += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(frontiers, 132_480);
    let payload = [0, 0, 1, 0x81, 0, 0, 0, 1, 0x11, 0x22, 0x33];
    let mut input = vec![255, 83];
    input.extend(u16::try_from(payload.len() + 2).unwrap().to_be_bytes());
    input.extend(payload);
    let mut parser = new_parser(&input, &base).unwrap();
    let segment = parser.read_segment().unwrap();
    let actual = parser.parse_coc(segment, 257, seed).unwrap();
    assert_eq!(Ok(actual), reference(&payload, 0, 257, seed, &base));
    assert_eq!(actual.1.decomposition_structure, Some(1));
    assert_eq!(actual.1.decomposition_levels, 2);
    assert_eq!(actual.1.precinct_exponents[..3], [(1, 1), (2, 2), (3, 3)]);
    assert_eq!(parser.position, input.len());
    assert_eq!(parser.work_units, 1);
}

fn reference_raw_coding_style(
    bytes: &[u8],
    offset: usize,
    limits: &ResourceLimits,
) -> Result<CodingStyle, DecodeError> {
    fn malformed(offset: usize, kind: MalformedKind) -> DecodeError {
        DecodeError::MalformedInput {
            offset: offset as u64,
            kind,
        }
    }
    if bytes.len() < 10 {
        return Err(malformed(offset, MalformedKind::InvalidMarkerLength));
    }
    let flags = bytes[0];
    if flags >= 8 {
        return Err(malformed(offset, MalformedKind::InvalidCodingStyle));
    }
    let order = [
        ProgressionOrder::Lrcp,
        ProgressionOrder::Rlcp,
        ProgressionOrder::Rpcl,
        ProgressionOrder::Pcrl,
        ProgressionOrder::Cprl,
    ]
    .get(usize::from(bytes[1]))
    .copied()
    .ok_or_else(|| malformed(offset, MalformedKind::InvalidCodingStyle))?;
    let layers = u16::from_be_bytes([bytes[2], bytes[3]]);
    if layers > limits.maximum_layers() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Layers,
            limit: u64::from(limits.maximum_layers()),
            actual: u64::from(layers),
        });
    }
    if layers == 0 || bytes[4] > 1 {
        return Err(malformed(offset, MalformedKind::InvalidCodingStyle));
    }
    let resolutions = u16::from(bytes[5]) + 1;
    if resolutions > u16::from(u8::MAX) {
        return Err(malformed(offset, MalformedKind::ArithmeticOverflow));
    }
    if resolutions > u16::from(limits.maximum_resolutions_per_component()) {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Resolutions,
            limit: u64::from(limits.maximum_resolutions_per_component()),
            actual: u64::from(resolutions),
        });
    }
    if bytes[6] > 8 || bytes[7] > 8 {
        return Err(malformed(offset, MalformedKind::InvalidCodingStyle));
    }
    let width = 2_u32.pow(u32::from(bytes[6]) + 2);
    let height = 2_u32.pow(u32::from(bytes[7]) + 2);
    let style_valid = match bytes[8] / 64 {
        0 => true,
        1 => (bytes[8] % 64) & 0x37 == 0,
        2 => false,
        _ => (bytes[8] % 64) & 5 == 0,
    };
    if u64::from(width) * u64::from(height) > 4096 || !style_valid {
        return Err(malformed(offset, MalformedKind::InvalidCodingStyle));
    }
    let defined = flags % 2 == 1;
    if bytes.len() != 10 + if defined { usize::from(resolutions) } else { 0 } {
        return Err(malformed(offset, MalformedKind::InvalidMarkerLength));
    }
    let mut precincts = [(15, 15); 33];
    if defined {
        for (index, byte) in bytes[10..].iter().enumerate() {
            let slot = precincts
                .get_mut(index)
                .ok_or_else(|| malformed(offset, MalformedKind::InvalidCodingStyle))?;
            *slot = (byte % 16, byte / 16);
        }
    }
    Ok(CodingStyle {
        progression_order: order,
        layers,
        multiple_component_transform: bytes[4] == 1,
        decomposition_levels: bytes[5],
        decomposition_structure: None,
        decomposition_directions: [DecompositionDirection::TwoDimensional; 32],
        code_block_width: u16::try_from(width).unwrap(),
        code_block_height: u16::try_from(height).unwrap(),
        code_block_style: bytes[8],
        transform: match bytes[9] {
            0 => WaveletTransform::Irreversible9x7,
            1 => WaveletTransform::Reversible5x3,
            index => WaveletTransform::Arbitrary(index),
        },
        precincts_defined: defined,
        sop_markers: flags / 2 % 2 == 1,
        eph_markers: flags / 4 % 2 == 1,
        precinct_exponents: precincts,
    })
}

#[test]
fn actual_raw_cod_derives_full_style_defaults_precincts_and_ordered_admission() {
    fn malformed(offset: usize, kind: MalformedKind) -> DecodeError {
        DecodeError::MalformedInput {
            offset: offset as u64,
            kind,
        }
    }
    fn payload(header: [u8; 10], variant: usize) -> Vec<u8> {
        let mut bytes = header.to_vec();
        if header[0] % 2 == 1 {
            bytes.extend(
                (0..usize::from(header[5]) + 1).map(|index| (index as u8).wrapping_mul(17)),
            );
        }
        if variant == 1 {
            bytes.truncate(9);
        } else if variant == 2 {
            bytes.push(0);
        }
        bytes
    }
    let base = ResourceLimits::HARDENED;
    let limits = [
        base,
        base.with_coding_style_limits_for_test(0, 33),
        base.with_coding_style_limits_for_test(1, 33),
        base.with_coding_style_limits_for_test(u16::MAX, 0),
        base.with_coding_style_limits_for_test(u16::MAX, 1),
        base.with_coding_style_limits_for_test(u16::MAX, 33),
        base.with_coding_style_limits_for_test(u16::MAX, u8::MAX),
    ];
    let mut cases = 0;
    let mut successes = 0;
    for flags in [0, 1, 7] {
        for index in 0..10 {
            for byte in 0..=u8::MAX {
                let mut header = [flags, 0, 0, 1, 0, 0, 0, 0, 0, 1];
                header[index] = byte;
                for variant in 0..3 {
                    let bytes = payload(header, variant);
                    for limit in &limits {
                        let parser = new_parser(&[], limit).unwrap();
                        for offset in [0, 17, usize::MAX] {
                            let expected = reference_raw_coding_style(&bytes, offset, limit);
                            assert_eq!(parser.parse_cod_payload(offset, &bytes), expected);
                            assert_eq!(
                                parser.parse_cod(Segment {
                                    marker: 0x1234,
                                    offset,
                                    payload: &bytes
                                }),
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
    assert_eq!(cases, 483_840);
    assert!(successes > 1_000);
    let parser = new_parser(&[], &base).unwrap();
    for width in 0..10 {
        for height in 0..10 {
            let bytes = [0, 0, 0, 1, 0, 0, width, height, 0, 1];
            assert_eq!(
                parser.parse_cod_payload(31, &bytes),
                reference_raw_coding_style(&bytes, 31, &base)
            );
        }
    }
    let bytes = payload([7, 4, 0, 2, 1, 2, 4, 4, 0xc0, 255], 0);
    let mut input = vec![255, 82];
    input.extend(u16::try_from(bytes.len() + 2).unwrap().to_be_bytes());
    input.extend(&bytes);
    let mut parser = new_parser(&input, &base).unwrap();
    let segment = parser.read_segment().unwrap();
    let actual = parser.parse_cod(segment).unwrap();
    assert_eq!(
        actual,
        reference_raw_coding_style(&bytes, 0, &base).unwrap()
    );
    assert!(matches!(actual.transform, WaveletTransform::Arbitrary(255)));
    assert!(
        actual.precinct_exponents[3..]
            .iter()
            .all(|entry| *entry == (15, 15))
    );
    assert_eq!(parser.work_units, 1);
    assert_eq!(parser.position, input.len());
    let raw = base.with_coding_style_limits_for_test(u16::MAX, u8::MAX);
    let parser = new_parser(&[], &raw).unwrap();
    let no_precincts = payload([0, 0, 255, 255, 0, 254, 0, 0, 0, 255], 0);
    assert_eq!(
        parser
            .parse_cod_payload(0, &no_precincts)
            .unwrap()
            .decomposition_levels,
        254
    );
    let explicit = payload([1, 0, 0, 1, 0, 254, 0, 0, 0, 255], 0);
    assert_eq!(
        parser.parse_cod_payload(0, &explicit),
        Err(malformed(0, MalformedKind::InvalidCodingStyle))
    );
    let overflow = payload([0, 0, 0, 1, 0, 255, 0, 0, 0, 1], 0);
    assert_eq!(
        parser.parse_cod_payload(0, &overflow),
        Err(malformed(0, MalformedKind::ArithmeticOverflow))
    );
}

#[test]
fn actual_raw_siz_derives_every_image_field_uniform_policy_unused_slot_and_first_limit_error() {
    fn malformed(offset: usize, kind: MalformedKind) -> DecodeError {
        DecodeError::MalformedInput {
            offset: offset as u64,
            kind,
        }
    }
    fn payload(geometry: [u32; 8], components: &[[u8; 3]], r_siz: u16) -> Vec<u8> {
        let mut bytes = r_siz.to_be_bytes().to_vec();
        for coordinate in geometry {
            bytes.extend(coordinate.to_be_bytes());
        }
        bytes.extend(u16::try_from(components.len()).unwrap().to_be_bytes());
        for component in components {
            bytes.extend(component);
        }
        bytes
    }
    fn reference(
        bytes: &[u8],
        offset: usize,
        limits: &ResourceLimits,
    ) -> Result<(ImageSize, u16), DecodeError> {
        if bytes.len() < 36 {
            return Err(malformed(offset, MalformedKind::InvalidMarkerLength));
        }
        let mut words = bytes[2..34]
            .chunks_exact(4)
            .map(|word| u32::from_be_bytes(word.try_into().unwrap()));
        let xsiz = words.next().unwrap();
        let ysiz = words.next().unwrap();
        let xosiz = words.next().unwrap();
        let yosiz = words.next().unwrap();
        let xtsiz = words.next().unwrap();
        let ytsiz = words.next().unwrap();
        let xtosiz = words.next().unwrap();
        let ytosiz = words.next().unwrap();
        let count = u16::from_be_bytes([bytes[34], bytes[35]]);
        let first_x = u64::from(xtosiz) + u64::from(xtsiz);
        let first_y = u64::from(ytosiz) + u64::from(ytsiz);
        let component_bytes = u128::from(count) * 3;
        if first_x > u64::from(u32::MAX)
            || first_y > u64::from(u32::MAX)
            || component_bytes > usize::MAX as u128
            || component_bytes + 36 > usize::MAX as u128
        {
            return Err(malformed(offset, MalformedKind::ArithmeticOverflow));
        }
        if bytes.len() as u128 != 36 + component_bytes
            || xsiz <= xosiz
            || ysiz <= yosiz
            || xtsiz == 0
            || ytsiz == 0
            || xtosiz > xosiz
            || ytosiz > yosiz
            || first_x <= u64::from(xosiz)
            || first_y <= u64::from(yosiz)
            || count == 0
        {
            return Err(malformed(offset, MalformedKind::InvalidImageGeometry));
        }
        if count > limits.maximum_components() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::Components,
                limit: u64::from(limits.maximum_components()),
                actual: u64::from(count),
            });
        }
        let mut infos = [ComponentInfo::default(); MAX_COMPONENTS];
        let mut first = None;
        let mut uniform = true;
        for (index, entry) in bytes[36..].chunks_exact(3).enumerate() {
            let precision = u16::from(entry[0] % 128) + 1;
            let signed = entry[0] >= 128;
            if precision > 38 || entry[1] == 0 || entry[2] == 0 || index >= infos.len() {
                return Err(malformed(offset, MalformedKind::InvalidImageGeometry));
            }
            let precision = u8::try_from(precision).unwrap();
            infos[index] = ComponentInfo {
                precision,
                signed,
                x_subsampling: entry[1],
                y_subsampling: entry[2],
                x_registration: 0,
                y_registration: 0,
            };
            match first {
                None => first = Some((precision, signed)),
                Some(expected) if expected != (precision, signed) => uniform = false,
                _ => {}
            }
        }
        let width = xsiz - xosiz;
        let height = ysiz - yosiz;
        if width > limits.maximum_width() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::Width,
                limit: u64::from(limits.maximum_width()),
                actual: u64::from(width),
            });
        }
        if height > limits.maximum_height() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::Height,
                limit: u64::from(limits.maximum_height()),
                actual: u64::from(height),
            });
        }
        let pixels = u128::from(width) * u128::from(height);
        if pixels > u128::from(u64::MAX) {
            return Err(malformed(offset, MalformedKind::ArithmeticOverflow));
        }
        if pixels > u128::from(limits.maximum_pixels()) {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::Pixels,
                limit: limits.maximum_pixels(),
                actual: pixels as u64,
            });
        }
        let across = u64::from(xsiz - xtosiz).div_ceil(u64::from(xtsiz));
        let down = u64::from(ysiz - ytosiz).div_ceil(u64::from(ytsiz));
        let tiles = u128::from(across) * u128::from(down);
        if tiles > u128::from(u64::MAX) {
            return Err(malformed(offset, MalformedKind::ArithmeticOverflow));
        }
        if tiles > u128::from(limits.maximum_tiles()) {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::Tiles,
                limit: u64::from(limits.maximum_tiles()),
                actual: tiles as u64,
            });
        }
        let first = first.unwrap();
        Ok((
            ImageSize {
                width,
                height,
                x_origin: xosiz,
                y_origin: yosiz,
                components: count,
                uniform_bit_depth: if uniform { Some(first.0) } else { None },
                uniform_signed: if uniform { Some(first.1) } else { None },
                tile_width: xtsiz,
                tile_height: ytsiz,
                tile_x_origin: xtosiz,
                tile_y_origin: ytosiz,
                tiles_across: u32::try_from(across).unwrap(),
                tiles_down: u32::try_from(down).unwrap(),
                component_info: infos,
            },
            u16::from_be_bytes([bytes[0], bytes[1]]),
        ))
    }
    let geometries = [
        [17, 11, 3, 1, 8, 6, 0, 0],
        [u32::MAX, u32::MAX, 0, 0, u32::MAX, u32::MAX, 0, 0],
        [0; 8],
        [3, 11, 3, 1, 8, 6, 0, 0],
        [17, 1, 3, 1, 8, 6, 0, 0],
        [17, 11, 3, 1, 0, 6, 0, 0],
        [17, 11, 3, 1, 8, 0, 0, 0],
        [17, 11, 3, 1, 8, 6, 4, 0],
        [17, 11, 3, 1, 8, 6, 0, 2],
        [17, 11, 3, 1, 2, 6, 0, 0],
        [17, 11, 3, 1, 8, 1, 0, 0],
        [17, 11, 3, 1, 1, 6, u32::MAX, 0],
        [17, 11, 3, 1, 8, 1, 0, u32::MAX],
        [1_000, 1_000, 0, 0, 1, 1, 0, 0],
        [1, 1, 0, 0, 1, 1, 0, 0],
        [17, 11, 3, 1, 8, 6, 3, 1],
    ];
    let components = [
        vec![],
        vec![[7, 1, 1]],
        vec![[0x87, 2, 3]],
        vec![[7, 1, 1], [8, 3, 2]],
        vec![[7, 1, 1], [0x87, 1, 1]],
        vec![[37, 255, 255]],
        vec![[38, 1, 1]],
        vec![[255, 1, 1]],
        vec![[7, 0, 1]],
        vec![[7, 1, 0]],
        vec![[7, 1, 1], [8, 1, 1], [7, 1, 1]],
        vec![[7, 1, 1]; MAX_COMPONENTS],
        vec![[7, 1, 1]; MAX_COMPONENTS + 1],
    ];
    let base = ResourceLimits::HARDENED;
    let limits = [
        base,
        base.with_geometry_limits_for_test(
            1,
            base.maximum_width(),
            base.maximum_height(),
            base.maximum_pixels(),
            base.maximum_tiles(),
        ),
        base.with_geometry_limits_for_test(
            base.maximum_components(),
            8,
            base.maximum_height(),
            base.maximum_pixels(),
            base.maximum_tiles(),
        ),
        base.with_geometry_limits_for_test(
            base.maximum_components(),
            base.maximum_width(),
            4,
            base.maximum_pixels(),
            base.maximum_tiles(),
        ),
        base.with_geometry_limits_for_test(
            base.maximum_components(),
            base.maximum_width(),
            base.maximum_height(),
            16,
            base.maximum_tiles(),
        ),
        base.with_geometry_limits_for_test(
            base.maximum_components(),
            base.maximum_width(),
            base.maximum_height(),
            base.maximum_pixels(),
            2,
        ),
        base.with_geometry_limits_for_test(u16::MAX, 8, 4, 16, 2),
    ];
    let mut cases = 0;
    let mut successes = 0;
    for geometry in geometries {
        for entries in &components {
            for r_siz in [0, 1, 0x4000, u16::MAX] {
                for variant in 0..4 {
                    let mut bytes = payload(geometry, entries, r_siz);
                    match variant {
                        0 => {}
                        1 => bytes.truncate(35),
                        2 => bytes.push(0),
                        _ => bytes[34..36].copy_from_slice(&u16::MAX.to_be_bytes()),
                    }
                    for limit in &limits {
                        let parser = new_parser(&[], limit).unwrap();
                        for offset in [0, 17, usize::MAX] {
                            let expected = reference(&bytes, offset, limit);
                            assert_eq!(
                                parser.parse_siz(Segment {
                                    marker: 0x1234,
                                    offset,
                                    payload: &bytes
                                }),
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
    assert_eq!(cases, 69_888);
    assert!(successes > 100);
    let mut descriptor_cases = 0;
    let limit = ResourceLimits::HARDENED;
    let parser = new_parser(&[], &limit).unwrap();
    for ssiz in 0..=u8::MAX {
        for x in [0, 1, u8::MAX] {
            for y in [0, 1, u8::MAX] {
                let bytes = payload(geometries[0], &[[ssiz, x, y]], u16::MAX);
                assert_eq!(
                    parser.parse_siz(Segment {
                        marker: SIZ,
                        offset: 19,
                        payload: &bytes
                    }),
                    reference(&bytes, 19, &limit)
                );
                descriptor_cases += 1;
            }
        }
    }
    assert_eq!(descriptor_cases, 2_304);
    let mut words = 0;
    for base in [
        [0; 4],
        [u8::MAX; 4],
        [0x12, 0x34, 0x56, 0x78],
        [0x80, 0, 0, 1],
    ] {
        for index in 0..4 {
            for byte in 0..=u8::MAX {
                let mut bytes = base;
                bytes[index] = byte;
                assert_eq!(read_u32(bytes), u32::from_be_bytes(bytes));
                words += 1;
            }
        }
    }
    assert_eq!(words, 4_096);
    for value in [0, 1, 2, u32::MAX - 1, u32::MAX] {
        for divisor in [0, 1, 2, 3, u32::MAX] {
            let expected = if divisor == 0 {
                Err(malformed(0, MalformedKind::InvalidImageGeometry))
            } else {
                Ok(u32::try_from(u64::from(value).div_ceil(u64::from(divisor))).unwrap())
            };
            assert_eq!(ceil_div(value, divisor), expected);
        }
    }
    let bytes = payload(geometries[0], &components[4], 0x4000);
    let mut input = vec![255, 81];
    input.extend(u16::try_from(bytes.len() + 2).unwrap().to_be_bytes());
    input.extend(&bytes);
    let mut parser = new_parser(&input, &limit).unwrap();
    let segment = parser.read_segment().unwrap();
    let actual = parser.parse_siz(segment).unwrap();
    assert_eq!(actual, reference(&bytes, 0, &limit).unwrap());
    assert_eq!(actual.0.uniform_bit_depth, None);
    assert_eq!(actual.0.uniform_signed, None);
    assert!(
        actual.0.component_info[2..]
            .iter()
            .all(|info| *info == ComponentInfo::default())
    );
    assert_eq!(parser.work_units, 1);
    assert_eq!(parser.position, input.len());
}

#[test]
fn actual_raw_reader_derives_marker_payload_cursor_work_and_partial_error_state() {
    type Counters = (usize, u64, u64, u64);
    type SegmentObservation = (u16, usize, Vec<u8>);

    fn malformed(position: usize, kind: MalformedKind) -> DecodeError {
        DecodeError::MalformedInput {
            offset: position as u64,
            kind,
        }
    }
    fn counters(parser: &Parser<'_>) -> Counters {
        (
            parser.position,
            parser.work_units,
            parser.packet_length_bytes,
            parser.packet_lengths,
        )
    }
    fn raw<'a>(
        input: &'a [u8],
        limits: &'a ResourceLimits,
        position: usize,
        work: u64,
    ) -> Parser<'a> {
        Parser {
            input,
            limits,
            position,
            work_units: work,
            packet_length_bytes: u64::MAX,
            packet_lengths: 17,
        }
    }
    fn frame(parser: &Parser<'_>, input: &[u8], limits: &ResourceLimits, expected: Counters) {
        assert_eq!(counters(parser), expected);
        assert_eq!(parser.input, input);
        assert!(core::ptr::eq(parser.limits, limits));
    }
    fn peek(input: &[u8], position: usize) -> Result<u16, DecodeError> {
        let tail = input
            .get(position..)
            .ok_or_else(|| malformed(position, MalformedKind::Truncated))?;
        let bytes = tail
            .get(..2)
            .ok_or_else(|| malformed(position, MalformedKind::Truncated))?;
        if bytes[0] != 255 || bytes[1] == 0 || bytes[1] == 255 {
            Err(malformed(position, MalformedKind::InvalidMarker))
        } else {
            Ok(u16::from_be_bytes([bytes[0], bytes[1]]))
        }
    }
    fn charge(
        position: usize,
        work: &mut u64,
        amount: u64,
        limits: &ResourceLimits,
    ) -> Result<(), DecodeError> {
        let next = u128::from(*work) + u128::from(amount);
        if next > u128::from(u64::MAX) {
            return Err(malformed(position, MalformedKind::ArithmeticOverflow));
        }
        *work = next as u64;
        if *work > limits.maximum_work_units() {
            Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: limits.maximum_work_units(),
                actual: *work,
            })
        } else {
            Ok(())
        }
    }
    fn standalone(
        input: &[u8],
        state: &mut Counters,
        expected: u16,
        limits: &ResourceLimits,
    ) -> Result<(), DecodeError> {
        if peek(input, state.0)? != expected {
            return Err(malformed(state.0, MalformedKind::InvalidMarkerOrder));
        }
        let next = state.0 as u128 + 2;
        if next > usize::MAX as u128 {
            return Err(malformed(state.0, MalformedKind::ArithmeticOverflow));
        }
        state.0 = next as usize;
        charge(state.0, &mut state.1, 1, limits)
    }
    fn segment(
        input: &[u8],
        state: &mut Counters,
        limits: &ResourceLimits,
    ) -> Result<SegmentObservation, DecodeError> {
        let start = state.0;
        let marker = peek(input, start)?;
        charge(start, &mut state.1, 1, limits)?;
        if [SOC, SOD, EOC, 0xff92].contains(&marker) && marker != SOT {
            return Err(malformed(start, MalformedKind::InvalidMarkerOrder));
        }
        let length_offset = start as u128 + 2;
        if length_offset > usize::MAX as u128 {
            return Err(malformed(start, MalformedKind::ArithmeticOverflow));
        }
        let length_offset = length_offset as usize;
        let word = input
            .get(length_offset..)
            .and_then(|tail| tail.get(..2))
            .ok_or_else(|| malformed(start, MalformedKind::Truncated))?;
        let length = u16::from_be_bytes([word[0], word[1]]);
        if length < 2 {
            return Err(malformed(start, MalformedKind::InvalidMarkerLength));
        }
        let end = length_offset as u128 + u128::from(length);
        if end > usize::MAX as u128 {
            return Err(malformed(start, MalformedKind::ArithmeticOverflow));
        }
        if end > input.len() as u128 {
            return Err(malformed(start, MalformedKind::Truncated));
        }
        let payload = input[length_offset + 2..end as usize].to_vec();
        state.0 = end as usize;
        Ok((marker, start, payload))
    }
    fn eoc(
        input: &[u8],
        state: &mut Counters,
        limits: &ResourceLimits,
    ) -> Result<usize, DecodeError> {
        let tail = input
            .get(state.0..)
            .ok_or_else(|| malformed(state.0, MalformedKind::Truncated))?;
        for word in tail.windows(2) {
            charge(state.0, &mut state.1, 1, limits)?;
            if word == [255, 217] {
                return Ok(state.0);
            }
            state.0 += 1;
        }
        Err(malformed(state.0, MalformedKind::Truncated))
    }

    let zero_work = ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap();
    let mut words = 0;
    for word in 0..=u16::MAX {
        let bytes = word.to_be_bytes();
        let parser = raw(&bytes, &zero_work, 0, u64::MAX);
        assert_eq!(parser.peek_marker(), peek(&bytes, 0));
        assert_eq!(read_u16(bytes), u16::from_be_bytes(bytes));
        assert_eq!(
            is_standalone_marker(word),
            [SOC, SOD, EOC, 0xff92].contains(&word)
        );
        frame(&parser, &bytes, &zero_work, (0, u64::MAX, u64::MAX, 17));
        words += 1;
    }
    assert_eq!(words, 65_536);
    let mut constructors = 0;
    for length in 0..=64 {
        let bytes = vec![0xa5; length];
        for maximum in [
            0,
            1,
            2,
            17,
            64,
            ResourceLimits::HARDENED.maximum_input_bytes(),
        ] {
            let limits = ResourceLimits::HARDENED
                .with_maximum_input_bytes(maximum)
                .unwrap();
            match new_parser(&bytes, &limits) {
                Ok(parser) => {
                    assert!(length as u64 <= maximum);
                    frame(&parser, &bytes, &limits, (0, 0, 0, 0));
                }
                Err(error) => assert_eq!(
                    error,
                    DecodeError::LimitExceeded {
                        resource: Resource::InputBytes,
                        limit: maximum,
                        actual: length as u64,
                    }
                ),
            }
            constructors += 1;
        }
    }
    assert_eq!(constructors, 390);
    let fixtures = [
        vec![],
        vec![0],
        vec![255],
        vec![255, 0],
        vec![255, 255],
        vec![0, 144],
        vec![255, 79],
        vec![255, 217],
        vec![255, 144, 0, 2],
        vec![255, 81, 0, 1],
        vec![255, 81, 0, 0],
        vec![255, 81, 0, 5, 170, 187],
        vec![255, 81, 0, 4, 170, 187],
        vec![255, 0, 255, 217],
        vec![17, 255, 217, 255, 217],
        vec![255, 81, 255, 255],
    ];
    let limits = [
        ResourceLimits::HARDENED,
        zero_work,
        ResourceLimits::HARDENED.with_maximum_work_units(1).unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(2).unwrap(),
    ];
    let mut state_cases = 0;
    for input in fixtures {
        for position in (0..=input.len() + 2).chain(core::iter::once(usize::MAX)) {
            for work in [0, 1, u64::MAX - 1, u64::MAX] {
                for limit in &limits {
                    let initial = (position, work, u64::MAX, 17);
                    let parser = raw(&input, limit, position, work);
                    assert_eq!(parser.peek_marker(), peek(&input, position));
                    for kind in [
                        MalformedKind::Truncated,
                        MalformedKind::InvalidMarker,
                        MalformedKind::ArithmeticOverflow,
                    ] {
                        assert_eq!(parser.malformed_here(kind), malformed(position, kind));
                    }
                    assert_eq!(parser.offset(position), position as u64);
                    for amount in [0, 1, 2, u64::MAX] {
                        let mut actual = raw(&input, limit, position, work);
                        let mut expected = initial;
                        assert_eq!(
                            actual.charge_work(amount),
                            charge(position, &mut expected.1, amount, limit)
                        );
                        frame(&actual, &input, limit, expected);
                    }
                    for marker in [SOC, SIZ, EOC, 0x1234] {
                        let mut actual = raw(&input, limit, position, work);
                        let mut expected = initial;
                        assert_eq!(
                            actual.expect_standalone(marker),
                            standalone(&input, &mut expected, marker, limit)
                        );
                        frame(&actual, &input, limit, expected);
                    }
                    let mut actual = raw(&input, limit, position, work);
                    let mut expected = initial;
                    let read = actual
                        .read_segment()
                        .map(|segment| (segment.marker, segment.offset, segment.payload.to_vec()));
                    assert_eq!(read, segment(&input, &mut expected, limit));
                    frame(&actual, &input, limit, expected);
                    let mut actual = raw(&input, limit, position, work);
                    let mut expected = initial;
                    assert_eq!(actual.find_eoc(), eoc(&input, &mut expected, limit));
                    frame(&actual, &input, limit, expected);
                    state_cases += 1;
                }
            }
        }
    }
    assert_eq!(state_cases, 1_808);
}

fn reference_tile_data_window(
    input: &[u8],
    limits: &ResourceLimits,
    state: &mut PacketAdmissionState,
    data_start: usize,
    start: usize,
    length: u32,
) -> Result<(usize, Vec<u8>), DecodeError> {
    let end = if length == 0 {
        loop {
            let Some(word) = input.get(state.position..).and_then(|tail| tail.get(..2)) else {
                return Err(input_error_literal(
                    state.position,
                    MalformedKind::Truncated,
                ));
            };
            let charged = u128::from(state.work) + 1;
            if charged > u128::from(u64::MAX) {
                return Err(input_error_literal(
                    state.position,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
            state.work = charged as u64;
            if state.work > limits.maximum_work_units() {
                return Err(DecodeError::LimitExceeded {
                    resource: Resource::WorkUnits,
                    limit: limits.maximum_work_units(),
                    actual: state.work,
                });
            }
            if word == [255, 217] {
                break state.position;
            }
            state.position += 1;
        }
    } else {
        if u128::from(length) > usize::MAX as u128 {
            return Err(input_error_literal(
                state.position,
                MalformedKind::InvalidTilePart,
            ));
        }
        let wide = start as u128 + u128::from(length);
        if wide > usize::MAX as u128 {
            return Err(input_error_literal(
                state.position,
                MalformedKind::ArithmeticOverflow,
            ));
        }
        let end = wide as usize;
        if end < state.position || end > input.len() {
            return Err(input_error_literal(start, MalformedKind::InvalidTilePart));
        }
        end
    };
    if data_start > end || end > input.len() {
        return Err(input_error_literal(
            state.position,
            MalformedKind::InvalidTilePart,
        ));
    }
    Ok((end, input[data_start..end].to_vec()))
}

#[test]
fn actual_raw_tile_data_window_matches_independent_full_state_reference() {
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(1).unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(2).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
    ];
    let fixtures: &[&[u8]] = &[
        &[],
        &[255],
        &[0],
        &[255, 217],
        &[0, 255, 217],
        &[255, 0, 255, 217],
        &[255, 217, 0, 255, 217],
        &[1, 2, 3],
    ];
    let mut cases = 0;
    let (mut successes, mut slice_errors, mut scans, mut overflows) = (0, 0, 0, 0);
    for &input in fixtures {
        for limit in &limits {
            for position in [0, 1, input.len(), input.len() + 1, usize::MAX] {
                for work in [0, 1, u64::MAX - 1, u64::MAX] {
                    for (header_bytes, packet_count) in [(0, 0), (u64::MAX, 17)] {
                        for data_start in [0, 1, input.len(), input.len() + 1, usize::MAX] {
                            for start in [0, 1, input.len(), usize::MAX - 1, usize::MAX] {
                                for length in [0, 1, 2, input.len() as u32, u32::MAX] {
                                    let initial = PacketAdmissionState {
                                        position,
                                        work,
                                        header_bytes,
                                        packet_count,
                                    };
                                    let mut expected = initial;
                                    let reference = reference_tile_data_window(
                                        input,
                                        limit,
                                        &mut expected,
                                        data_start,
                                        start,
                                        length,
                                    );
                                    let mut parser = Parser {
                                        input,
                                        limits: limit,
                                        position,
                                        work_units: work,
                                        packet_length_bytes: header_bytes,
                                        packet_lengths: packet_count,
                                    };
                                    let actual = parser.tile_data_window(data_start, start, length);
                                    assert_eq!(
                                        actual.map(|(end, data)| (end, data.to_vec())),
                                        reference,
                                        "position={position} start={start} length={length} data_start={data_start}"
                                    );
                                    assert_packet_admission_state(&parser, expected, input, limit);
                                    if let Ok((end, data)) = actual {
                                        assert!(core::ptr::eq(
                                            data.as_ptr(),
                                            input[data_start..end].as_ptr()
                                        ));
                                        successes += 1;
                                    } else if actual
                                        == Err(input_error_literal(
                                            expected.position,
                                            MalformedKind::InvalidTilePart,
                                        ))
                                        && (length == 0
                                            || (start as u128 + u128::from(length)
                                                <= input.len() as u128
                                                && start as u128 + u128::from(length)
                                                    >= position as u128))
                                    {
                                        slice_errors += 1;
                                    }
                                    if expected.position != initial.position {
                                        scans += 1;
                                    }
                                    if matches!(
                                        actual,
                                        Err(DecodeError::MalformedInput {
                                            kind: MalformedKind::ArithmeticOverflow,
                                            ..
                                        })
                                    ) {
                                        overflows += 1;
                                    }
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 200_000);
    assert_eq!(
        (successes, slice_errors, scans, overflows),
        (7_720, 8_030, 2_100, 54_250)
    );
    eprintln!(
        "tile window: cases={cases} success={successes} slice_errors={slice_errors} scans={scans} overflows={overflows}"
    );
}

#[test]
fn actual_tile_data_window_reader_joins_preserve_metadata_failure_cursor_order() {
    let limits = ResourceLimits::HARDENED;
    let mut joins = 0;
    for zero_length in [false, true] {
        for bad_lengths in [false, true] {
            let mut input = vec![0x42, 0x43];
            input.extend(segment(PLT, &[0, if bad_lengths { 2 } else { 3 }]));
            input.extend(segment(PPT, &[0, 0xab]));
            input.extend(SOD.to_be_bytes());
            let data_start = input.len();
            input.extend([0x12, 0x34]);
            let end = input.len();
            input.extend(EOC.to_be_bytes());
            let mut parser = new_parser(&input, &limits).unwrap();
            parser.position = 2;
            let style = parser
                .parse_cod(Segment {
                    marker: COD,
                    offset: 0,
                    payload: &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1],
                })
                .unwrap();
            let quantization = Quantization::reversible_default(style);
            let result = parser.read_tile_part(
                TilePart {
                    start: 1,
                    length: if zero_length { 0 } else { (end - 1) as u32 },
                    tile_index: 17,
                    tile_part_index: 23,
                    tile_part_count: 29,
                },
                (style, quantization),
                ComponentCodingStyles::uniform(1, style).unwrap(),
                ComponentQuantizations::uniform(1, quantization).unwrap(),
                RoiShifts::none(),
                ProgressionChanges::none(),
                MctParameters {
                    arrays: Vec::new(),
                    records: Vec::new(),
                    order: Vec::new(),
                },
                Part2Extensions::default(),
                1,
                PacketLengths::none(),
                PackedPacketHeaders::none(),
            );
            if bad_lengths {
                assert_eq!(
                    result.err(),
                    Some(input_error_literal(1, MalformedKind::InvalidPacketLength))
                );
            } else {
                let (payload, _, _) = result.unwrap();
                assert_eq!(
                    (
                        payload.tile_index,
                        payload.tile_part_index,
                        payload.tile_part_count
                    ),
                    (17, 23, 29)
                );
                assert_eq!(payload.data, [0x12, 0x34]);
                assert!(core::ptr::eq(
                    payload.data.as_ptr(),
                    input[data_start..end].as_ptr()
                ));
                assert_eq!(payload.packet_lengths.packet_count(), 1);
                assert_eq!(payload.packet_lengths.encoded_bytes(), 1);
                assert_eq!(
                    payload.packed_packet_headers.reassemble(&limits).unwrap(),
                    [0xab]
                );
            }
            assert_packet_admission_state(
                &parser,
                PacketAdmissionState {
                    position: if zero_length || !bad_lengths {
                        end
                    } else {
                        data_start
                    },
                    work: if zero_length { 8 } else { 5 },
                    header_bytes: 2,
                    packet_count: 1,
                },
                &input,
                &limits,
            );
            joins += 1;
        }
    }
    assert_eq!(joins, 4);

    // Both metadata finalizers can fail after a successful raw window.
    for length in [0, 4] {
        let input = [0x12, 0x34, 255, 217];
        let mut parser = new_parser(&input, &limits).unwrap();
        let (_, data) = parser.tile_data_window(0, 0, length).unwrap();
        let expected = PacketAdmissionState {
            position: if length == 0 { 2 } else { 0 },
            work: if length == 0 { 3 } else { 0 },
            header_bytes: 0,
            packet_count: 0,
        };
        assert_eq!(
            parser.finish_packet_lengths(
                usize::MAX,
                0,
                PacketLengths::none(),
                true,
                0,
                0,
                0,
                data.len(),
                0,
                19,
            ),
            Err(input_error_literal(19, MalformedKind::InvalidTilePart))
        );
        assert_packet_admission_state(&parser, expected, &input, &limits);
        assert_eq!(
            parser.finish_packed_packet_headers(
                usize::MAX,
                0,
                PackedPacketHeaders::none(),
                1,
                0,
                23,
            ),
            Err(input_error_literal(23, MalformedKind::InvalidTilePart))
        );
        assert_packet_admission_state(&parser, expected, &input, &limits);
    }
    eprintln!("tile window joins: reader=4 raw_finalizer_failures=4");
}

#[test]
fn progression_change_component_indexes_follow_csiz_width() {
    let limits = ResourceLimits::default();
    let parser = new_parser(&[], &limits).unwrap();
    let payload = [0, 1, 0, 0, 1, 1, 1, 1, 0];
    let changes = parser
        .parse_poc(
            Segment {
                marker: POC,
                offset: 0,
                payload: &payload,
            },
            300,
        )
        .unwrap();
    assert_eq!(changes.records()[0].component_start, 256);
    assert_eq!(changes.records()[0].component_end, 257);

    let one_byte_endpoint = [0, 255, 0, 1, 1, 0, 0];
    let changes = parser
        .parse_poc(
            Segment {
                marker: POC,
                offset: 0,
                payload: &one_byte_endpoint,
            },
            256,
        )
        .unwrap();
    assert_eq!(changes.records()[0].component_start, 255);
    assert_eq!(changes.records()[0].component_end, 256);
}

#[test]
fn parses_retains_and_iterates_plm_and_plt_packet_lengths() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let tile_data = vec![0; 129];
    let limits = ResourceLimits::default();

    let plm_bytes = codestream_with_headers(
        1,
        &[cod.clone(), qcd.clone(), plm(0, &[&[1, 128]])],
        &[],
        &tile_data,
    );
    let plm_layout = parse_layout(&plm_bytes, &limits).unwrap();
    let plm_lengths = plm_layout.tile_parts[0].packet_lengths;
    assert!(plm_lengths.is_present());
    assert_eq!(plm_lengths.packet_count(), 2);
    assert_eq!(plm_lengths.encoded_bytes(), 3);
    let mut plm_iter = plm_lengths.iter();
    assert_eq!(plm_iter.next_length().unwrap(), Some(1));
    assert_eq!(plm_iter.next_length().unwrap(), Some(128));
    assert_eq!(plm_iter.next_length().unwrap(), None);

    let plt_bytes =
        codestream_with_headers(1, &[cod, qcd], &[plt(0, &[1]), plt(1, &[128])], &tile_data);
    let plt_layout = parse_layout(&plt_bytes, &limits).unwrap();
    let plt_lengths = plt_layout.tile_parts[0].packet_lengths;
    assert!(plt_lengths.is_present());
    assert_eq!(plt_lengths.packet_count(), 2);
    assert_eq!(plt_lengths.encoded_bytes(), 3);
    let mut plt_iter = plt_lengths.iter();
    assert_eq!(plt_iter.next_length().unwrap(), Some(1));
    assert_eq!(plt_iter.next_length().unwrap(), Some(128));
    assert_eq!(plt_iter.next_length().unwrap(), None);

    let empty_plm = codestream_with_headers(
        1,
        &[
            segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]),
            segment(QCD, &[0, 0]),
            plm(0, &[&[]]),
        ],
        &[],
        &[],
    );
    let empty_layout = parse_layout(&empty_plm, &limits).unwrap();
    assert!(empty_layout.tile_parts[0].packet_lengths.is_present());
    assert_eq!(empty_layout.tile_parts[0].packet_lengths.packet_count(), 0);

    let empty_plt = codestream_with_headers(
        1,
        &[
            segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]),
            segment(QCD, &[0, 0]),
        ],
        &[segment(PLT, &[0])],
        &[],
    );
    let empty_layout = parse_layout(&empty_plt, &limits).unwrap();
    assert!(empty_layout.tile_parts[0].packet_lengths.is_present());
    assert_eq!(empty_layout.tile_parts[0].packet_lengths.packet_count(), 0);
}

#[test]
fn validates_packet_length_scope_indexes_coding_and_payload_sum() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let limits = ResourceLimits::default();

    let duplicate_plt = codestream_with_headers(
        1,
        &[cod.clone(), qcd.clone()],
        &[plt(0, &[1]), plt(0, &[1])],
        &[0, 0],
    );
    assert!(matches!(
        parse_layout(&duplicate_plt, &limits),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));
    let duplicate_plm = codestream_with_headers(
        1,
        &[cod.clone(), qcd.clone(), plm(0, &[&[1]]), plm(0, &[&[1]])],
        &[],
        &[0],
    );
    assert!(matches!(
        parse_layout(&duplicate_plm, &limits),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));

    let incomplete = codestream_with_headers(
        1,
        &[cod.clone(), qcd.clone()],
        &[segment(PLT, &[0, 0x81])],
        &[0],
    );
    assert!(matches!(
        parse_layout(&incomplete, &limits),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidPacketLength,
            ..
        })
    ));

    let overflow = codestream_with_headers(
        1,
        &[cod.clone(), qcd.clone()],
        &[segment(PLT, &[0, 0x81, 0x80, 0x80, 0x80, 0x80, 0])],
        &[0],
    );
    assert!(matches!(
        parse_layout(&overflow, &limits),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidPacketLength,
            ..
        })
    ));
    let truncated_plm_group = codestream_with_headers(
        1,
        &[cod.clone(), qcd.clone(), segment(PLM, &[0, 0, 0, 0, 2, 1])],
        &[],
        &[0],
    );
    assert!(matches!(
        parse_layout(&truncated_plm_group, &limits),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerLength,
            ..
        })
    ));

    let wrong_sum = codestream_with_headers(1, &[cod.clone(), qcd.clone()], &[plt(0, &[2])], &[0]);
    assert!(matches!(
        parse_layout(&wrong_sum, &limits),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidPacketLength,
            ..
        })
    ));

    let plt_in_main =
        codestream_with_headers(1, &[cod.clone(), qcd.clone(), plt(0, &[1])], &[], &[0]);
    assert!(matches!(
        parse_layout(&plt_in_main, &limits),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));
    let plm_in_tile =
        codestream_with_headers(1, &[cod.clone(), qcd.clone()], &[plm(0, &[&[1]])], &[0]);
    assert!(matches!(
        parse_layout(&plm_in_tile, &limits),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));
    let both_scopes =
        codestream_with_headers(1, &[cod, qcd, plm(0, &[&[1]])], &[plt(0, &[1])], &[0]);
    assert!(matches!(
        parse_layout(&both_scopes, &limits),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));
}

#[test]
fn accounts_packet_length_bytes_packets_and_plm_tile_groups() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let bytes = codestream_with_headers(
        1,
        &[cod.clone(), qcd.clone(), plm(0, &[&[1, 1]])],
        &[],
        &[0, 0],
    );
    let byte_limits = ResourceLimits::default()
        .with_maximum_packet_header_bytes(1)
        .unwrap();
    assert!(matches!(
        parse_layout(&bytes, &byte_limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::PacketHeaderBytes,
            ..
        })
    ));
    let packet_limits = ResourceLimits::default().with_maximum_packets(1).unwrap();
    assert!(matches!(
        parse_layout(&bytes, &packet_limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            ..
        })
    ));

    let extra_group = codestream_with_headers(1, &[cod, qcd, plm(0, &[&[1], &[1]])], &[], &[0]);
    assert!(matches!(
        parse_layout(&extra_group, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidPacketLength,
            ..
        })
    ));
}

#[test]
fn parses_last_zero_length_tile_part() {
    let bytes = codestream(&[0xff, 0x00, 3], true);
    let info = parse(&bytes, &ResourceLimits::default()).unwrap();
    assert_eq!(info.tile_parts, 1);
    let limits = ResourceLimits::default();
    assert_eq!(
        parse_layout(&bytes, &limits).unwrap().tile_parts[0].data,
        [0xff, 0x00, 3]
    );
}

#[test]
fn retains_main_and_tile_maxshift_overrides_per_component() {
    let limits = ResourceLimits::default();
    let mut main = codestream(&[0], true);
    let sot = main
        .windows(2)
        .position(|bytes| bytes == SOT.to_be_bytes())
        .unwrap();
    main.splice(sot..sot, segment(RGN, &[0, 0, 5]));
    let layout = parse_layout(&main, &limits).unwrap();
    assert_eq!(layout.info.roi_shifts.shift(0).unwrap(), 5);
    assert_eq!(layout.tile_parts[0].roi_shifts.shift(0).unwrap(), 5);

    let mut tile = codestream(&[0], true);
    let sot = tile
        .windows(2)
        .position(|bytes| bytes == SOT.to_be_bytes())
        .unwrap();
    tile.splice(sot..sot, segment(RGN, &[0, 0, 3]));
    let sod = tile
        .windows(2)
        .position(|bytes| bytes == SOD.to_be_bytes())
        .unwrap();
    tile.splice(sod..sod, segment(RGN, &[0, 0, 6]));
    let layout = parse_layout(&tile, &limits).unwrap();
    assert_eq!(layout.info.roi_shifts.shift(0).unwrap(), 3);
    assert_eq!(layout.tile_parts[0].roi_shifts.shift(0).unwrap(), 6);
}

#[test]
fn retains_main_and_tile_component_style_and_quantization_overrides() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let main_coc = segment(COC, &[1, 0, 1, 1, 1, 1, 0]);
    let main_qcc = segment(QCC, &[1, 0, 8, 16, 24, 32]);
    let tile_cod = segment(COD, &[0, 0, 0, 1, 0, 2, 0, 0, 0, 1]);
    let tile_coc = segment(COC, &[1, 0, 2, 0, 0, 2, 1]);
    let tile_qcc_zero = segment(QCC, &[0, 0, 40, 48, 56, 64, 72, 80, 88]);
    let tile_qcc = segment(QCC, &[1, 0, 40, 48, 56, 64, 72, 80, 88]);
    let bytes = codestream_with_headers(
        2,
        &[cod, main_coc, qcd, main_qcc],
        &[tile_cod, tile_coc, tile_qcc_zero, tile_qcc],
        &[0, 0, 0, 0],
    );
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();

    let main_zero = layout.info.component_coding_styles.style(0).unwrap();
    let main_one = layout.info.component_coding_styles.style(1).unwrap();
    assert_eq!(main_zero.decomposition_levels, 0);
    assert_eq!(main_one.decomposition_levels, 1);
    assert_eq!(main_one.code_block_width, 8);
    assert_eq!(main_one.code_block_style, 1);
    assert_eq!(main_one.transform, WaveletTransform::Irreversible9x7);
    assert_eq!(
        layout
            .info
            .component_quantizations
            .quantization(0)
            .unwrap()
            .step_count,
        1
    );
    let main_one_quantization = layout.info.component_quantizations.quantization(1).unwrap();
    assert_eq!(main_one_quantization.step_count, 4);
    assert_eq!(main_one_quantization.step(3).unwrap().exponent, 4);

    let tile = &layout.tile_parts[0];
    let tile_one = tile.component_coding_styles.style(1).unwrap();
    assert_eq!(
        tile.component_coding_styles
            .style(0)
            .unwrap()
            .decomposition_levels,
        2
    );
    assert_eq!(tile_one.decomposition_levels, 2);
    assert_eq!(tile_one.code_block_width, 4);
    assert_eq!(tile_one.code_block_style, 2);
    assert_eq!(tile_one.transform, WaveletTransform::Reversible5x3);
    assert_eq!(
        tile.component_quantizations
            .quantization(0)
            .unwrap()
            .step_count,
        7
    );
    let tile_one_quantization = tile.component_quantizations.quantization(1).unwrap();
    assert_eq!(tile_one_quantization.step_count, 7);
    assert_eq!(tile_one_quantization.step(6).unwrap().exponent, 11);
}

#[test]
fn component_quantization_storage_scales_with_components_and_clones_independently() {
    assert!(core::mem::size_of::<ComponentQuantizations>() <= 64);
    let info = parse(&codestream(&[0], false), &ResourceLimits::default()).unwrap();
    let default = info.component_quantizations.quantization(0).unwrap();
    for count in [1_u16, 3, MAX_COMPONENTS as u16] {
        let mut table = ComponentQuantizations::uniform(count, default).unwrap();
        assert_eq!(table.quantizations.len(), usize::from(count));
        let snapshot = table.clone();
        let mut changed = default;
        changed.guard_bits += 1;
        table.set(count - 1, changed).unwrap();
        assert_eq!(
            snapshot.quantization(count - 1).unwrap().guard_bits,
            default.guard_bits
        );
        assert_eq!(
            table.quantization(count - 1).unwrap().guard_bits,
            changed.guard_bits
        );
        assert!(!table.equals(&snapshot));
        assert!(table.quantization(count).is_err());
        assert!(table.set(count, default).is_err());
    }
    assert!(ComponentQuantizations::uniform(0, default).is_err());
    assert!(ComponentQuantizations::uniform((MAX_COMPONENTS + 1) as u16, default).is_err());
}

#[test]
fn tile_default_quantization_precedes_main_qcc_and_tile_qcc_precedes_default() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let main_qcd = segment(QCD, &[0x40, 0x40]);
    let main_qcc = segment(QCC, &[1, 0x40, 0x48]);
    let tile_qcd = segment(QCD, &[0x40, 0x50]);
    let tile_qcc = segment(QCC, &[2, 0x40, 0x58]);
    let bytes = codestream_with_headers(
        3,
        &[cod, main_qcd, main_qcc],
        &[tile_qcd, tile_qcc],
        &[0, 0, 0],
    );
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let tile = &layout.tile_parts[0];

    assert_eq!(
        layout
            .info
            .component_quantizations
            .quantization(1)
            .unwrap()
            .step(0)
            .unwrap()
            .exponent,
        9
    );
    assert_eq!(tile.quantization.step(0).unwrap().exponent, 10);
    assert_eq!(
        tile.component_quantizations
            .quantization(0)
            .unwrap()
            .step(0)
            .unwrap()
            .exponent,
        10
    );
    assert_eq!(
        tile.component_quantizations
            .quantization(1)
            .unwrap()
            .step(0)
            .unwrap()
            .exponent,
        10
    );
    assert_eq!(
        tile.component_quantizations
            .quantization(2)
            .unwrap()
            .step(0)
            .unwrap()
            .exponent,
        11
    );
}

#[test]
fn validates_tile_default_quantization_duplicates_lengths_and_compatibility() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0x40, 0x40]);

    let duplicate = codestream_with_headers(
        1,
        &[cod.clone(), qcd.clone()],
        &[qcd.clone(), qcd.clone()],
        &[0],
    );
    assert!(matches!(
        parse_layout(&duplicate, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));

    let invalid_length = codestream_with_headers(
        1,
        &[cod.clone(), qcd.clone()],
        &[segment(QCD, &[0x40])],
        &[0],
    );
    assert!(matches!(
        parse_layout(&invalid_length, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerLength,
            ..
        })
    ));

    let incompatible = codestream_with_headers(
        2,
        &[cod, qcd],
        &[
            segment(QCD, &[0x40, 0x48]),
            segment(COC, &[1, 0, 1, 2, 2, 0, 1]),
        ],
        &[0],
    );
    assert!(matches!(
        parse_layout(&incompatible, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidQuantization,
            ..
        })
    ));
}

#[test]
fn retains_tile_default_quantization_across_tile_parts() {
    let mut bytes = SOC.to_be_bytes().to_vec();
    bytes.extend(siz());
    bytes.extend(segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]));
    bytes.extend(segment(QCD, &[0x40, 0x40]));
    let mut part = 0_u8;
    while part < 2 {
        let start = bytes.len();
        let mut sot = Vec::new();
        sot.extend_from_slice(&0_u16.to_be_bytes());
        sot.extend_from_slice(&0_u32.to_be_bytes());
        sot.extend_from_slice(&[part, 2]);
        bytes.extend(segment(SOT, &sot));
        if part == 0 {
            bytes.extend(segment(QCD, &[0x40, 0x58]));
        }
        bytes.extend_from_slice(&SOD.to_be_bytes());
        let length = u32::try_from(bytes.len() - start).unwrap();
        bytes[start + 6..start + 10].copy_from_slice(&length.to_be_bytes());
        part += 1;
    }
    bytes.extend_from_slice(&EOC.to_be_bytes());

    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(layout.tile_parts.len(), 2);
    assert_eq!(
        layout.tile_parts[0].quantization.step(0).unwrap().exponent,
        11
    );
    assert_eq!(
        layout.tile_parts[1].quantization.step(0).unwrap().exponent,
        11
    );
    assert_eq!(
        layout.tile_parts[1]
            .component_quantizations
            .quantization(0)
            .unwrap()
            .step(0)
            .unwrap()
            .exponent,
        11
    );
}

fn index_cache_layout_fixture() -> (Vec<u8>, [Vec<u8>; 2]) {
    let main = [
        baseline_headers()[0].clone(),
        segment(QCD, &[0x40, 0x40]),
        segment(COC, &[2, 0, 0, 3, 1, 0, 1]),
        segment(QCC, &[2, 0x40, 0x50]),
        segment(DFS, &[0, 1, 1, 0x40]),
        segment(NLT, &[0, 0, 7, 0]),
    ];
    let headers = [
        [
            vec![
                segment(COC, &[1, 0, 0, 1, 2, 0, 1]),
                segment(QCC, &[1, 0x40, 0x58]),
                segment(DFS, &[0, 1, 1, 0xc0]),
                segment(NLT, &[0, 0, 8, 0]),
            ],
            vec![
                segment(COD, &[0, 0, 0, 1, 0, 0, 3, 2, 0, 1]),
                segment(QCD, &[0x40, 0x48]),
            ],
            vec![],
            vec![segment(COC, &[2, 0, 0, 0, 1, 0, 1])],
        ],
        [
            vec![
                segment(COD, &[0, 0, 0, 1, 0, 0, 1, 3, 0, 1]),
                segment(QCD, &[0x40, 0x60]),
                segment(COC, &[2, 0, 0, 2, 0, 0, 1]),
            ],
            vec![
                segment(COC, &[1, 0, 0, 0, 2, 0, 1]),
                segment(QCC, &[1, 0x40, 0x50]),
                segment(NLT, &[0, 0, 9, 0]),
            ],
            vec![],
            vec![],
        ],
    ];
    let header_length = 2 + siz_with_components(3).len() + main.iter().map(Vec::len).sum::<usize>();
    let seed = codestream_with_headers(3, &main, &[], &[]);
    let mut interleaved = seed[..header_length].to_vec();
    // Split the existing SIZ into two 32x32 tiles.
    interleaved[24..28].copy_from_slice(&32_u32.to_be_bytes());
    let mut separate = [
        seed[..header_length].to_vec(),
        seed[..header_length].to_vec(),
    ];
    for (part, (first, second)) in headers[0].iter().zip(&headers[1]).enumerate() {
        for (tile, header) in [first, second].into_iter().enumerate() {
            let single = codestream_with_headers(3, &main, header, &[0]);
            let mut chunk = single[header_length..single.len() - 2].to_vec();
            chunk[10] = u8::try_from(part).unwrap();
            chunk[11] = 4;
            separate[tile].extend_from_slice(&chunk);
            chunk[4..6].copy_from_slice(&u16::try_from(tile).unwrap().to_be_bytes());
            interleaved.extend_from_slice(&chunk);
        }
    }
    interleaved.extend_from_slice(&EOC.to_be_bytes());
    for bytes in &mut separate {
        bytes.extend_from_slice(&EOC.to_be_bytes());
    }
    (interleaved, separate)
}

#[test]
fn index_cache_preserves_interleaved_latest_part_headers_and_unused_fields() {
    let (bytes, separate) = index_cache_layout_fixture();
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let references: [Vec<ComponentCodingStyles>; 2] = core::array::from_fn(|tile| {
        parse_layout(&separate[tile], &limits)
            .unwrap()
            .tile_parts
            .iter()
            .map(|part| part.component_coding_styles)
            .collect()
    });
    assert_eq!(layout.tile_parts.len(), 8);
    assert_eq!(layout.info.consumed_bytes, bytes.len() as u64);
    for (index, actual) in layout.tile_parts.iter().enumerate() {
        let tile = index % 2;
        let part = index / 2;
        assert_eq!(usize::from(actual.tile_index), tile);
        assert_eq!(usize::from(actual.tile_part_index), part);
        assert_eq!(actual.component_coding_styles, references[tile][part]);
    }
    for (tile, input) in separate.iter().enumerate() {
        let reference = parse_layout(input, &limits).unwrap();
        for (part, expected) in reference.tile_parts.iter().enumerate() {
            let mut expected = expected.clone();
            expected.tile_index = u16::try_from(tile).unwrap();
            assert_eq!(layout.tile_parts[2 * part + tile], expected);
        }
    }
    assert_ne!(references[0][0], references[0][1]);
    assert_eq!(references[0][1], references[0][2]);
    assert_eq!(references[1][1], references[1][3]);
}

#[test]
fn index_cache_preserves_late_tile_error_and_tile_part_limit_priority() {
    let (mut bytes, _) = index_cache_layout_fixture();
    let last = bytes
        .windows(2)
        .rposition(|marker| marker == SOT.to_be_bytes())
        .unwrap();
    bytes[last + 4..last + 6].copy_from_slice(&2_u16.to_be_bytes());
    assert_eq!(
        parse_layout(&bytes, &ResourceLimits::default()).unwrap_err(),
        DecodeError::MalformedInput {
            offset: last as u64,
            kind: MalformedKind::InvalidTilePart,
        }
    );
    let limits = ResourceLimits::default()
        .with_maximum_tile_parts(7)
        .unwrap();
    assert_eq!(
        parse_layout(&bytes, &limits).unwrap_err(),
        DecodeError::limit(Resource::TileParts, 7, 8)
    );
}

#[test]
fn validates_component_override_indexes_duplicates_and_lengths() {
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let coc = segment(COC, &[1, 0, 1, 1, 1, 0, 1]);

    let out_of_range = codestream_with_headers(
        2,
        &[
            cod.clone(),
            segment(COC, &[2, 0, 0, 2, 2, 0, 1]),
            qcd.clone(),
        ],
        &[],
        &[0, 0],
    );
    assert!(matches!(
        parse_layout(&out_of_range, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidCodingStyle,
            ..
        })
    ));

    let out_of_range_qcc = codestream_with_headers(
        2,
        &[cod.clone(), qcd.clone(), segment(QCC, &[2, 0, 0])],
        &[],
        &[0, 0],
    );
    assert!(matches!(
        parse_layout(&out_of_range_qcc, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidQuantization,
            ..
        })
    ));

    let duplicate = codestream_with_headers(
        2,
        &[cod.clone(), coc.clone(), coc.clone(), qcd.clone()],
        &[],
        &[0, 0, 0],
    );
    assert!(matches!(
        parse_layout(&duplicate, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));

    let duplicate_qcc = codestream_with_headers(
        2,
        &[
            cod.clone(),
            qcd.clone(),
            segment(QCC, &[1, 0, 0]),
            segment(QCC, &[1, 0, 0]),
        ],
        &[],
        &[0, 0],
    );
    assert!(matches!(
        parse_layout(&duplicate_qcc, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));

    let duplicate_tile_coc = codestream_with_headers(
        2,
        &[cod.clone(), qcd.clone()],
        &[coc.clone(), coc.clone()],
        &[0, 0, 0],
    );
    assert!(matches!(
        parse_layout(&duplicate_tile_coc, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));

    let short_coc = codestream_with_headers(
        2,
        &[cod.clone(), segment(COC, &[1, 0, 0]), qcd.clone()],
        &[],
        &[0, 0],
    );
    assert!(matches!(
        parse_layout(&short_coc, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerLength,
            ..
        })
    ));

    let short_qcc = codestream_with_headers(
        2,
        &[cod, coc, qcd, segment(QCC, &[1, 0, 8])],
        &[],
        &[0, 0, 0],
    );
    assert!(matches!(
        parse_layout(&short_qcc, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerLength,
            ..
        })
    ));
}

#[test]
fn validates_maxshift_component_style_shift_and_duplicates() {
    let limits = ResourceLimits::default();
    for payload in [[1, 0, 1], [0, 1, 1]] {
        let mut bytes = codestream(&[0], true);
        let sot = bytes
            .windows(2)
            .position(|value| value == SOT.to_be_bytes())
            .unwrap();
        bytes.splice(sot..sot, segment(RGN, &payload));
        assert!(matches!(
            parse_layout(&bytes, &limits),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::InvalidRegionOfInterest,
                ..
            })
        ));
    }

    let mut maximum = codestream(&[0], true);
    let sot = maximum
        .windows(2)
        .position(|value| value == SOT.to_be_bytes())
        .unwrap();
    maximum.splice(sot..sot, segment(RGN, &[0, 0, MAX_ROI_SHIFT]));
    let parsed = parse_layout(&maximum, &limits).unwrap();
    assert_eq!(parsed.info.roi_shifts.shift(0).unwrap(), u8::MAX);

    let mut duplicate = codestream(&[0], true);
    let sot = duplicate
        .windows(2)
        .position(|value| value == SOT.to_be_bytes())
        .unwrap();
    let mut markers = segment(RGN, &[0, 0, 2]);
    markers.extend(segment(RGN, &[0, 0, 2]));
    duplicate.splice(sot..sot, markers);
    assert!(matches!(
        parse_layout(&duplicate, &limits),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));
}

#[test]
fn parses_reassembles_and_validates_packed_packet_headers() {
    let limits = ResourceLimits::default();
    let cod = segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]);
    let qcd = segment(QCD, &[0, 0]);
    let ppm_bytes = codestream_with_headers(
        1,
        &[
            cod.clone(),
            qcd.clone(),
            ppm(0, &[0, 0]),
            ppm(1, &[0, 1, 0]),
        ],
        &[],
        &[],
    );
    let ppm_layout = parse_layout(&ppm_bytes, &limits).unwrap();
    let packed = ppm_layout.tile_parts[0].packed_packet_headers;
    assert!(packed.is_present());
    assert_eq!(packed.len(), 1);
    assert_eq!(packed.fragment_count(), 2);
    assert_eq!(packed.reassemble(&limits).unwrap(), [0]);

    let ppt_bytes = codestream_with_headers(
        1,
        &[cod.clone(), qcd.clone()],
        &[ppt(0, &[0xaa]), ppt(1, &[0xbb])],
        &[],
    );
    let ppt_layout = parse_layout(&ppt_bytes, &limits).unwrap();
    let packed = ppt_layout.tile_parts[0].packed_packet_headers;
    assert_eq!(packed.len(), 2);
    assert_eq!(packed.fragment_count(), 2);
    assert_eq!(packed.reassemble(&limits).unwrap(), [0xaa, 0xbb]);

    for invalid in [
        codestream_with_headers(
            1,
            &[cod.clone(), qcd.clone(), ppm(1, &[0, 0, 0, 1, 0])],
            &[],
            &[],
        ),
        codestream_with_headers(
            1,
            &[cod.clone(), qcd.clone(), ppm(0, &[0, 0, 0, 2, 0])],
            &[],
            &[],
        ),
        codestream_with_headers(
            1,
            &[cod.clone(), qcd.clone(), ppm(0, &[0, 0, 0, 1, 0])],
            &[ppt(0, &[0])],
            &[],
        ),
    ] {
        assert!(matches!(
            parse_layout(&invalid, &limits),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::InvalidMarkerOrder | MalformedKind::InvalidPackedPacketHeader,
                ..
            })
        ));
    }

    let ppm_in_tile = codestream_with_headers(1, &[cod.clone(), qcd.clone()], &[ppm(0, &[])], &[]);
    let ppt_in_main = codestream_with_headers(1, &[cod, qcd, ppt(0, &[])], &[], &[]);
    for invalid in [ppm_in_tile, ppt_in_main] {
        assert!(matches!(
            parse_layout(&invalid, &limits),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::InvalidMarkerOrder,
                ..
            })
        ));
    }

    let bounded = codestream_with_headers(
        1,
        &[
            segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]),
            segment(QCD, &[0, 0]),
        ],
        &[ppt(0, &[0, 0])],
        &[],
    );
    let tight = limits.with_maximum_packet_header_bytes(1).unwrap();
    assert_eq!(
        parse_layout(&bounded, &tight),
        Err(DecodeError::LimitExceeded {
            resource: Resource::PacketHeaderBytes,
            limit: 1,
            actual: 2,
        })
    );
}

#[test]
fn rejects_missing_siz_and_trailing_bytes() {
    let mut missing = SOC.to_be_bytes().to_vec();
    missing.extend(segment(SOT, &[0, 0, 0, 0, 0, 14, 0, 1]));
    assert!(matches!(
        parse(&missing, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidMarkerOrder,
            ..
        })
    ));

    let mut trailing = codestream(&[], false);
    trailing.push(0);
    assert!(matches!(
        parse(&trailing, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::TrailingData,
            ..
        })
    ));
}

#[test]
fn rejects_impossible_geometry() {
    let mut bytes = codestream(&[], false);
    let xsiz_offset = 2 + 4 + 2;
    bytes[xsiz_offset..xsiz_offset + 4].copy_from_slice(&0_u32.to_be_bytes());
    assert!(matches!(
        parse(&bytes, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidImageGeometry,
            ..
        })
    ));
}

#[test]
fn every_prefix_fails_without_panicking() {
    let bytes = codestream(&[1, 2, 3], false);
    for length in 0..bytes.len() {
        assert!(parse(&bytes[..length], &ResourceLimits::default()).is_err());
    }
}

#[test]
fn enforces_work_limit_for_zero_length_tile_part() {
    let bytes = codestream(&[0; 64], true);
    let limits = ResourceLimits::default()
        .with_maximum_work_units(8)
        .unwrap();
    assert!(matches!(
        parse(&bytes, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            ..
        })
    ));
}

#[test]
fn accepts_all_part_one_progression_orders() {
    let expected = [
        ProgressionOrder::Lrcp,
        ProgressionOrder::Rlcp,
        ProgressionOrder::Rpcl,
        ProgressionOrder::Pcrl,
        ProgressionOrder::Cprl,
    ];
    for (value, expected_order) in expected.into_iter().enumerate() {
        let cod = [0, u8::try_from(value).unwrap(), 0, 1, 0, 0, 2, 2, 0, 1];
        let bytes = codestream_with_styles(&[], false, &cod, &[0, 0]);
        let info = parse(&bytes, &ResourceLimits::default()).unwrap();
        assert_eq!(info.coding_style.progression_order, expected_order);
    }
}

#[test]
fn rejects_invalid_coding_and_quantization_styles() {
    let invalid_progression =
        codestream_with_styles(&[], false, &[0, 5, 0, 1, 0, 0, 2, 2, 0, 1], &[0, 0]);
    assert!(matches!(
        parse(&invalid_progression, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidCodingStyle,
            ..
        })
    ));

    let invalid_quantization =
        codestream_with_styles(&[], false, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1], &[3, 0]);
    assert!(matches!(
        parse(&invalid_quantization, &ResourceLimits::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidQuantization,
            ..
        })
    ));
}
