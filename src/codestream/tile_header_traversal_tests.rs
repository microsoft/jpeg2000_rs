use super::*;
use crate::codestream::tile_header_traversal::{
    TileHeaderAccumulator, new_tile_header_accumulator,
};

fn frame(parser: &Parser<'_>) -> (usize, usize, ResourceLimits, usize, u64, u64, u64) {
    (
        parser.input.as_ptr() as usize,
        parser.input.len(),
        *parser.limits,
        parser.position,
        parser.work_units,
        parser.packet_length_bytes,
        parser.packet_lengths,
    )
}

fn initial<'a>(start: usize) -> TileHeaderAccumulator<'a> {
    new_tile_header_accumulator(
        start,
        raw_resolution_style(0, 0),
        RoiShifts::none(),
        ProgressionChanges::none(),
        MctParameters {
            arrays: Vec::new(),
            records: Vec::new(),
            order: Vec::new(),
        },
        Part2Extensions::default(),
    )
}

#[test]
fn raw_roi_setter_preserves_every_physical_shift_and_error_frame() {
    let mut cases = 0;
    let mut check = |component: u16, shift: u8| {
        let before = core::array::from_fn(|index| (component as u8) ^ (index as u8));
        let mut actual = RoiShifts { shifts: before };
        let mut expected = before;
        let result = if usize::from(component) < MAX_COMPONENTS {
            expected[usize::from(component)] = shift;
            Ok(())
        } else {
            Err(input_error_literal(
                0,
                MalformedKind::InvalidRegionOfInterest,
            ))
        };
        assert_eq!(actual.set(component, shift), result);
        assert_eq!(actual.shifts, expected);
        cases += 1;
    };
    for component in 0..=u16::MAX {
        for shift in [0, 127, 255] {
            check(component, shift);
        }
    }
    for component in [0, 63, 64, u16::MAX] {
        for shift in 0..=u8::MAX {
            check(component, shift);
        }
    }
    assert_eq!(cases, 197_632);
}

#[test]
fn raw_tile_header_metadata_and_ppt_errors_retain_partial_owners_and_work() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(3)
        .unwrap();
    let input = super::segment(DFS, &[0, 1, 1, 0x40]);
    let mut parser = new_parser(&input, &limits).unwrap();
    let mut raw = initial(7);
    assert_eq!(
        parser.traverse_tile_header(
            &mut raw,
            1,
            0,
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 3,
            actual: 9,
        })
    );
    assert_eq!(parser.position, 8);
    assert_eq!(parser.work_units, 9);
    assert_eq!(raw.part2_extensions.metadata_bytes, 8);
    assert!(raw.part2_extensions.decomposition_structures.is_empty());
    assert!(raw.has_functional_header_marker);
    let limits = ResourceLimits::default();
    let mut input = super::segment(PPT, &[0, 1, 2]);
    input.extend(super::segment(PPT, &[2, 3]));
    let mut parser = new_parser(&input, &limits).unwrap();
    let mut raw = initial(7);
    assert_eq!(
        parser.traverse_tile_header(
            &mut raw,
            1,
            0,
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(input_error_literal(7, MalformedKind::InvalidMarkerOrder))
    );
    assert_eq!(parser.position, input.len());
    assert_eq!(raw.ppt_bytes, [1, 2]);
    assert_eq!((raw.next_ppt_index, raw.ppt_fragments), (1, 1));
    assert_eq!((raw.tile_header_start, raw.tile_header_end), (7, 7));
}

#[test]
fn raw_tile_header_read_initialization_and_nonfunctional_markers_preserve_inheritance() {
    let limits = ResourceLimits::default();
    let mut input = super::segment(COM, &[0, 0, 99]);
    input.extend(super::segment(PLT, &[0, 3]));
    let header_end = input.len();
    input.extend_from_slice(&SOD.to_be_bytes());
    input.extend_from_slice(&[9, 8, 7]);
    let mut parser = new_parser(&input, &limits).unwrap();
    let mut style = raw_resolution_style(u8::MAX, 0);
    style.layers = u16::MAX;
    let mut roi = RoiShifts::none();
    roi.shifts[63] = u8::MAX;
    let raw = parser
        .read_tile_header(
            style,
            roi,
            ProgressionChanges::none(),
            MctParameters {
                arrays: Vec::new(),
                records: Vec::new(),
                order: vec![99, 99],
            },
            Part2Extensions::default(),
            u16::MAX,
            u8::MAX,
            PacketLengths::none(),
            PackedPacketHeaders::none(),
        )
        .unwrap();
    assert_eq!(
        (raw.tile_header_start, raw.tile_header_end, parser.position),
        (0, header_end, header_end + 2)
    );
    assert_eq!(raw.tile_coding_style, style);
    assert_eq!(raw.tile_roi_shifts, roi);
    assert_eq!(raw.mct_parameters.order, [99, 99]);
    assert!(!raw.has_functional_header_marker && !raw.tile_cod_seen && !raw.tile_rgn_seen);
    assert!(!raw.poc_seen && !raw.tile_mco_seen);
    assert!(raw.roi_seen.iter().all(|seen| !*seen));
    assert!(
        raw.coc_segments.iter().all(Option::is_none)
            && raw.qcc_segments.iter().all(Option::is_none)
    );
    assert_eq!(
        (
            raw.next_plt_index,
            raw.plt_packet_count,
            raw.plt_encoded_bytes,
            raw.plt_payload_bytes
        ),
        (1, 1, 1, 3)
    );
    assert!(raw.plt_seen);
}

#[test]
fn raw_tile_header_poc_replaces_inherited_records_and_appends_in_wire_order() {
    let limits = ResourceLimits::default();
    let mut input = poc(&[[0, 0, 0, 1, 1, 1, 0], [0, 0, 0, 2, 1, 1, 4]]);
    input.extend_from_slice(&SOD.to_be_bytes());
    let mut parser = new_parser(&input, &limits).unwrap();
    let mut raw = initial(0);
    raw.progression_changes.records.push(ProgressionChange {
        resolution_start: 99,
        component_start: 99,
        layer_end: 99,
        resolution_end: 99,
        component_end: 99,
        progression_order: ProgressionOrder::Rlcp,
    });
    parser
        .traverse_tile_header(
            &mut raw,
            1,
            0,
            PacketLengths::none(),
            PackedPacketHeaders::none(),
        )
        .unwrap();
    assert_eq!(raw.progression_changes.records.len(), 2);
    assert_eq!(raw.progression_changes.records[0].layer_end, 1);
    assert_eq!(raw.progression_changes.records[1].layer_end, 2);
    assert_eq!(
        raw.progression_changes.records[0].progression_order,
        ProgressionOrder::Lrcp
    );
    assert_eq!(
        raw.progression_changes.records[1].progression_order,
        ProgressionOrder::Cprl
    );
}

fn segment(marker: u16, payload: &[u8]) -> Segment<'_> {
    Segment {
        marker,
        offset: 37,
        payload,
    }
}

#[test]
fn raw_tile_header_sod_stops_before_pending_and_inherited_finalizers() {
    let limits = ResourceLimits::default();
    let mut parser = Parser {
        input: &[0xff, 0x93, 11, 22],
        limits: &limits,
        position: 0,
        work_units: 9,
        packet_length_bytes: u64::MAX - 1,
        packet_lengths: u64::MAX - 2,
    };
    let mut raw = initial(usize::MAX);
    raw.tile_header_end = 99;
    raw.tile_coding_style.decomposition_levels = u8::MAX;
    raw.coc_segments[63] = Some(segment(COC, &[255, 255, 13]));
    raw.qcc_segments[2] = Some(segment(QCC, &[255]));
    raw.tile_roi_shifts.shifts[63] = 211;
    raw.roi_seen[63] = true;
    raw.tile_cod_seen = true;
    raw.tile_rgn_seen = true;
    raw.poc_seen = true;
    raw.tile_mco_seen = true;
    raw.has_functional_header_marker = true;
    raw.plt_seen = true;
    raw.next_plt_index = u16::MAX;
    raw.plt_packet_count = u64::MAX;
    raw.plt_encoded_bytes = u64::MAX - 1;
    raw.plt_payload_bytes = u64::MAX - 2;
    raw.next_ppt_index = u16::MAX;
    raw.ppt_fragments = u16::MAX;
    raw.ppt_bytes = vec![9, 8, 7];
    raw.completed_mct = vec![7, 7, 3];
    raw.completed_mcc = vec![9, 9];
    raw.mct_parameters.order = vec![99, 99];
    raw.part2_extensions.metadata_bytes = u64::MAX;
    raw.pending_mct = vec![MctFragment {
        descriptor: 99,
        next_index: u16::MAX,
        final_index: 0,
        offset: usize::MAX,
        data: vec![4, 3, 2],
    }];
    raw.tile_header_end = 0;
    let expected = format!("{raw:?}");
    for components in 0..=u16::MAX {
        parser.position = 0;
        parser.work_units = 9;
        raw.tile_header_end = usize::MAX;
        assert_eq!(
            parser.traverse_tile_header(
                &mut raw,
                components,
                u8::MAX,
                PacketLengths::none(),
                PackedPacketHeaders::none()
            ),
            Ok(())
        );
        assert_eq!(format!("{raw:?}"), expected);
        assert_eq!(
            frame(&parser),
            (
                parser.input.as_ptr() as usize,
                4,
                limits,
                2,
                10,
                u64::MAX - 1,
                u64::MAX - 2
            )
        );
    }
}

#[test]
fn raw_tile_header_all_marker_words_preserve_admission_and_boundary_priority() {
    let limits = ResourceLimits::default();
    let allowed = [
        COD, COC, PLT, QCD, QCC, RGN, POC, PPT, COM, DFS, ADS, MCT, MCC, NLT, MCO, CBD, ATK,
    ];
    let forbidden = [CAP, TLM, PRF, PLM, CPF, PPM, CRG];
    for marker in 0..=u16::MAX {
        if allowed.contains(&marker) || marker == SOD {
            continue;
        }
        let [high, low] = marker.to_be_bytes();
        let input = [high, low, 0, 2, 0xff, 0x93];
        let mut parser = new_parser(&input, &limits).unwrap();
        let mut raw = initial(usize::MAX);
        raw.tile_header_end = 99;
        raw.coc_segments[63] = Some(segment(COC, &[255, 7]));
        raw.ppt_bytes = vec![7, 9];
        raw.next_plt_index = u16::MAX;
        let before = format!("{raw:?}");
        let (kind, position, work) = if high != 0xff || matches!(low, 0 | 255) {
            (MalformedKind::InvalidMarker, 0, 0)
        } else if [SOC, SIZ, SOT, EOC].contains(&marker) {
            (MalformedKind::InvalidMarkerOrder, 0, 0)
        } else if marker == 0xff92 {
            (MalformedKind::InvalidMarkerOrder, 0, 1)
        } else if forbidden.contains(&marker) {
            (MalformedKind::InvalidMarkerOrder, 4, 1)
        } else {
            (MalformedKind::InvalidMarker, 4, 1)
        };
        assert_eq!(
            parser.traverse_tile_header(
                &mut raw,
                0,
                255,
                PacketLengths::none(),
                PackedPacketHeaders::none()
            ),
            Err(input_error_literal(0, kind)),
            "{marker:04x}"
        );
        assert_eq!(format!("{raw:?}"), before, "{marker:04x}");
        assert_eq!(
            (
                parser.position,
                parser.work_units,
                parser.packet_length_bytes,
                parser.packet_lengths
            ),
            (position, work, 0, 0),
            "{marker:04x}"
        );
    }
}

#[test]
fn raw_tile_header_read_error_frontiers_keep_complete_reader_and_raw_state() {
    let limits = ResourceLimits::default();
    for (input, position, work, expected_position, expected_work, offset, kind, end) in [
        (&[][..], 0, 7, 0, 7, 0, MalformedKind::Truncated, 99),
        (&[0xff][..], 0, 7, 0, 7, 0, MalformedKind::Truncated, 99),
        (
            &[0xff, 0x93][..],
            usize::MAX,
            7,
            usize::MAX,
            7,
            usize::MAX,
            MalformedKind::Truncated,
            99,
        ),
        (
            &[0xff, 0x93][..],
            0,
            u64::MAX,
            2,
            u64::MAX,
            2,
            MalformedKind::ArithmeticOverflow,
            99,
        ),
        (
            &[0xff, 0x64][..],
            0,
            u64::MAX,
            0,
            u64::MAX,
            0,
            MalformedKind::ArithmeticOverflow,
            99,
        ),
        (
            &[0xff, 0x64][..],
            0,
            7,
            0,
            8,
            0,
            MalformedKind::Truncated,
            99,
        ),
        (
            &[0xff, 0x64, 0, 1][..],
            0,
            7,
            0,
            8,
            0,
            MalformedKind::InvalidMarkerLength,
            99,
        ),
        (
            &[0xff, 0x64, 0, 9][..],
            0,
            7,
            0,
            8,
            0,
            MalformedKind::Truncated,
            99,
        ),
        (
            &[0xff, 0x52, 0, 2][..],
            0,
            7,
            4,
            8,
            0,
            MalformedKind::InvalidMarkerLength,
            99,
        ),
    ] {
        let mut parser = Parser {
            input,
            limits: &limits,
            position,
            work_units: work,
            packet_length_bytes: 101,
            packet_lengths: 103,
        };
        let mut raw = initial(17);
        raw.tile_header_end = 99;
        let mut expected = initial(17);
        expected.tile_header_end = end;
        if input == [0xff, 0x52, 0, 2] {
            expected.tile_cod_seen = true;
            expected.has_functional_header_marker = true;
        }
        let before_frame = frame(&parser);
        assert_eq!(
            parser.traverse_tile_header(
                &mut raw,
                1,
                0,
                PacketLengths::none(),
                PackedPacketHeaders::none()
            ),
            Err(input_error_literal(offset, kind))
        );
        assert_eq!(raw, expected);
        assert_eq!(
            frame(&parser),
            (
                before_frame.0,
                before_frame.1,
                limits,
                expected_position,
                expected_work,
                101,
                103
            )
        );
    }
}

#[test]
fn raw_tile_header_duplicate_parse_and_flag_order_is_not_transactional() {
    let limits = ResourceLimits::default();
    let mut parser = new_parser(&[], &limits).unwrap();
    for (marker, kind) in [
        (COD, MalformedKind::InvalidMarkerLength),
        (MCO, MalformedKind::InvalidTransform),
        (POC, MalformedKind::InvalidMarkerLength),
    ] {
        let mut raw = initial(0);
        raw.mct_parameters.order = vec![7, 7];
        let inherited = format!("{:?}", raw.mct_parameters);
        assert_eq!(
            parser.dispatch_tile_header_segment(
                &mut raw,
                segment(marker, &[]),
                1,
                0,
                PacketLengths::none(),
                PackedPacketHeaders::none()
            ),
            Err(input_error_literal(37, kind))
        );
        assert!(raw.has_functional_header_marker);
        assert!(match marker {
            COD => raw.tile_cod_seen,
            MCO => raw.tile_mco_seen,
            _ => raw.poc_seen,
        });
        assert_eq!(format!("{:?}", raw.mct_parameters), inherited);
        assert_eq!(
            parser.dispatch_tile_header_segment(
                &mut raw,
                segment(marker, &[]),
                1,
                0,
                PacketLengths::none(),
                PackedPacketHeaders::none()
            ),
            Err(input_error_literal(37, MalformedKind::InvalidMarkerOrder))
        );
    }
    let mut raw = initial(0);
    raw.qcd_segment = Some(segment(QCD, &[199]));
    assert_eq!(
        parser.dispatch_tile_header_segment(
            &mut raw,
            segment(QCD, &[]),
            1,
            0,
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(input_error_literal(37, MalformedKind::InvalidMarkerOrder))
    );
    assert_eq!(raw.qcd_segment.unwrap().payload, &[199]);
    raw.roi_seen[0] = true;
    assert_eq!(
        parser.dispatch_tile_header_segment(
            &mut raw,
            segment(RGN, &[]),
            1,
            0,
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(input_error_literal(37, MalformedKind::InvalidMarkerLength))
    );
    assert_eq!(
        parser.dispatch_tile_header_segment(
            &mut raw,
            segment(RGN, &[0, 0, 8]),
            1,
            0,
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(input_error_literal(37, MalformedKind::InvalidMarkerOrder))
    );
    assert!(!raw.tile_rgn_seen);
    raw.poc_seen = false;
    assert_eq!(
        parser.dispatch_tile_header_segment(
            &mut raw,
            segment(POC, &[]),
            1,
            1,
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(input_error_literal(37, MalformedKind::InvalidMarkerOrder))
    );
    assert!(!raw.poc_seen);
    for marker in [COC, QCC] {
        let mut raw = initial(0);
        raw.coc_segments[63] = Some(segment(COC, &[99]));
        raw.qcc_segments[63] = Some(segment(QCC, &[99]));
        assert_eq!(
            parser.dispatch_tile_header_segment(
                &mut raw,
                segment(marker, &[0, 1, 7]),
                257,
                0,
                PacketLengths::none(),
                PackedPacketHeaders::none()
            ),
            Ok(())
        );
        let slots = if marker == COC {
            &raw.coc_segments
        } else {
            &raw.qcc_segments
        };
        assert_eq!(slots[1].unwrap().payload, &[0, 1, 7]);
        assert_eq!(slots[63].unwrap().payload, &[99]);
        assert_eq!(
            parser.dispatch_tile_header_segment(
                &mut raw,
                segment(marker, &[0, 1, 8]),
                257,
                0,
                PacketLengths::none(),
                PackedPacketHeaders::none()
            ),
            Err(input_error_literal(37, MalformedKind::InvalidMarkerOrder))
        );
    }
}

#[test]
fn raw_tile_header_packet_conflicts_and_ordered_partial_counters_survive_errors() {
    let limits = ResourceLimits::default();
    let mut parser = new_parser(&[], &limits).unwrap();
    let main_lengths = PacketLengths {
        source: PacketLengthSource::Plm(&[1]),
        packet_count: 1,
        encoded_bytes: 1,
    };
    let main_headers = PackedPacketHeaders {
        source: PackedPacketHeaderSource::MarkerSegments {
            header: &[7],
            marker: PPM,
            logical_start: 0,
        },
        fragments: 1,
        length: 1,
    };
    for marker in [PLT, PPT] {
        let mut raw = initial(0);
        assert_eq!(
            parser.dispatch_tile_header_segment(
                &mut raw,
                segment(marker, &[]),
                1,
                0,
                main_lengths,
                main_headers
            ),
            Err(input_error_literal(
                37,
                if marker == PLT {
                    MalformedKind::InvalidMarkerLength
                } else {
                    MalformedKind::InvalidMarkerOrder
                }
            ))
        );
        assert_eq!(raw.has_functional_header_marker, marker == PPT);
        assert_eq!(
            (raw.next_plt_index, raw.next_ppt_index, raw.ppt_fragments),
            (0, 0, 0)
        );
    }
    let mut raw = initial(0);
    assert_eq!(
        parser.dispatch_tile_header_segment(
            &mut raw,
            segment(PLT, &[0, 0x80]),
            1,
            0,
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(input_error_literal(37, MalformedKind::InvalidPacketLength))
    );
    assert_eq!(raw.next_plt_index, 1);
    assert!(!raw.plt_seen && !raw.has_functional_header_marker);
    assert_eq!((parser.packet_length_bytes, parser.packet_lengths), (1, 0));
    for stage in 0..3 {
        let mut parser = new_parser(&[], &limits).unwrap();
        let mut raw = initial(0);
        raw.plt_packet_count = if stage == 0 { u64::MAX } else { 7 };
        raw.plt_encoded_bytes = if stage == 1 { u64::MAX } else { 11 };
        raw.plt_payload_bytes = if stage == 2 { u64::MAX } else { 13 };
        assert_eq!(
            parser.dispatch_tile_header_segment(
                &mut raw,
                segment(PLT, &[0, 3]),
                1,
                0,
                PacketLengths::none(),
                PackedPacketHeaders::none()
            ),
            Err(input_error_literal(37, MalformedKind::ArithmeticOverflow))
        );
        assert!(raw.plt_seen);
        assert_eq!(raw.next_plt_index, 1);
        assert_eq!(raw.plt_packet_count, if stage == 0 { u64::MAX } else { 8 });
        assert_eq!(
            raw.plt_encoded_bytes,
            if stage == 0 {
                11
            } else if stage == 1 {
                u64::MAX
            } else {
                12
            }
        );
        assert_eq!(
            raw.plt_payload_bytes,
            if stage == 2 { u64::MAX } else { 13 }
        );
        assert_eq!((parser.packet_length_bytes, parser.packet_lengths), (1, 1));
    }
    let mut raw = initial(0);
    raw.ppt_fragments = u16::MAX;
    raw.ppt_bytes = vec![7, 7, 9];
    assert_eq!(
        parser.dispatch_tile_header_segment(
            &mut raw,
            segment(PPT, &[0, 3]),
            1,
            0,
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(input_error_literal(37, MalformedKind::ArithmeticOverflow))
    );
    assert_eq!((raw.next_ppt_index, raw.ppt_fragments), (1, u16::MAX));
    assert_eq!(raw.ppt_bytes, [7, 7, 9]);
}

#[test]
fn actual_tile_header_traversal_joins_real_producers_and_existing_caller_finalizers() {
    let [cod, qcd] = baseline_headers();
    let [mct_first, mct_last] = mct_i16_segmented(1, 1, &[1, 1], 1);
    let headers = [
        qcd,
        cod,
        super::segment(COC, &[0, 0, 0, 2, 2, 0, 1]),
        super::segment(QCC, &[0, 0, 0]),
        super::segment(RGN, &[0, 0, 9]),
        super::segment(PLT, &[0, 3]),
        super::segment(PPT, &[0, 7, 9]),
        poc(&[[0, 0, 0, 1, 1, 1, 0]]),
        super::segment(DFS, &[0, 1, 1, 0x40]),
        super::segment(ADS, &[2, 1, 0x40, 1, 0]),
        super::segment(NLT, &[0xff, 0xff, 7, 0]),
        super::segment(ATK, &[0x4a, 2, 0x3f, 0x80, 0, 0, 0]),
        mct_first,
        mct_last,
        mcc(9, 1, true, 1, 0),
        mco(&[9]),
        super::segment(COM, &[0, 0, 7, 9]),
    ];
    let stream = codestream_with_headers(1, &baseline_headers(), &headers, &[3, 4, 5]);
    let limits = ResourceLimits::default();
    let mut parser = new_parser(&stream, &limits).unwrap();
    parser.parse_layout_prologue().unwrap();
    let mut count = 1;
    while parser
        .read_main_header_segment(&mut count)
        .unwrap()
        .is_some()
    {}
    let tile_part = parser.read_sot(1).unwrap();
    let header_start = parser.position;
    let mut inherited = MctParameters {
        arrays: Vec::new(),
        records: Vec::new(),
        order: vec![99, 99],
    };
    let first = &mct_i16(1, 1, &[7])[4..];
    inherited
        .arrays
        .push(parser.parse_mct(segment(MCT, first)).unwrap());
    inherited
        .arrays
        .push(parser.parse_mct(segment(MCT, first)).unwrap());
    let old_mcc = mcc(9, 1, false, 1, 0);
    inherited
        .records
        .push(parser.parse_mcc(segment(MCC, &old_mcc[4..]), 1).unwrap());
    inherited
        .records
        .push(parser.parse_mcc(segment(MCC, &old_mcc[4..]), 1).unwrap());
    let mut raw = new_tile_header_accumulator(
        header_start,
        raw_resolution_style(0, 0),
        RoiShifts::none(),
        ProgressionChanges {
            records: vec![ProgressionChange {
                resolution_start: 99,
                component_start: 99,
                layer_end: 99,
                resolution_end: 99,
                component_end: 99,
                progression_order: ProgressionOrder::Lrcp,
            }],
        },
        inherited,
        Part2Extensions::default(),
    );
    parser
        .traverse_tile_header(
            &mut raw,
            1,
            0,
            PacketLengths::none(),
            PackedPacketHeaders::none(),
        )
        .unwrap();
    let end = header_start + headers.iter().map(Vec::len).sum::<usize>();
    assert_eq!(
        (raw.tile_header_start, raw.tile_header_end, parser.position),
        (header_start, end, end + 2)
    );
    assert_eq!(&stream[parser.position..parser.position + 3], &[3, 4, 5]);
    assert!(raw.tile_cod_seen && raw.tile_rgn_seen && raw.poc_seen && raw.tile_mco_seen);
    assert!(raw.has_functional_header_marker && raw.plt_seen);
    assert_eq!(
        raw.coc_segments[0].unwrap().payload.as_ptr(),
        stream[header_start + headers[0].len() + headers[1].len() + 4..].as_ptr()
    );
    assert_eq!(raw.qcc_segments[0].unwrap().payload, &[0, 0, 0]);
    assert!(raw.coc_segments[1..].iter().all(Option::is_none));
    assert_eq!(raw.tile_roi_shifts.shifts[0], 9);
    assert_eq!(
        (
            raw.next_plt_index,
            raw.plt_packet_count,
            raw.plt_encoded_bytes,
            raw.plt_payload_bytes
        ),
        (1, 1, 1, 3)
    );
    assert_eq!((raw.next_ppt_index, raw.ppt_fragments), (1, 1));
    assert_eq!(raw.ppt_bytes, [7, 9]);
    assert_eq!(raw.progression_changes.records.len(), 1);
    assert_eq!(raw.progression_changes.records[0].component_start, 0);
    assert!(raw.pending_mct.is_empty() && raw.pending_mcc.is_empty());
    assert_eq!(raw.completed_mct, [1]);
    assert_eq!(raw.completed_mcc, [9]);
    assert_eq!(raw.mct_parameters.arrays.len(), 2);
    assert_ne!(raw.mct_parameters.arrays[0], raw.mct_parameters.arrays[1]);
    assert_eq!(raw.mct_parameters.records.len(), 2);
    assert_ne!(raw.mct_parameters.records[0], raw.mct_parameters.records[1]);
    assert_eq!(raw.mct_parameters.order, [9]);
    assert_eq!(raw.part2_extensions.decomposition_structures.len(), 1);
    assert_eq!(raw.part2_extensions.arbitrary_decompositions.len(), 1);
    assert_eq!(raw.part2_extensions.nonlinear_transforms.len(), 1);
    assert_eq!(raw.part2_extensions.arbitrary_kernels.len(), 1);
    for zero_length in [false, true] {
        let tile_headers: Vec<_> = headers
            .iter()
            .filter(|bytes| ![PLT, PPT].contains(&u16::from_be_bytes([bytes[0], bytes[1]])))
            .cloned()
            .collect();
        let mut stream = codestream_with_headers(1, &baseline_headers(), &tile_headers, &[3, 4, 5]);
        if zero_length {
            let start = stream
                .windows(2)
                .position(|b| b == SOT.to_be_bytes())
                .unwrap();
            stream[start + 6..start + 10].fill(0);
        }
        let layout = parse_layout(&stream, &limits).unwrap();
        let payload = &layout.tile_parts[0];
        assert_eq!(payload.data, &[3, 4, 5]);
        assert_eq!(payload.roi_shifts.shifts[0], 9);
        assert_eq!(payload.progression_changes.records.len(), 1);
        assert_eq!(payload.part2_extensions.arbitrary_kernels.len(), 1);
        assert!(payload.multiple_component_transform.is_some());
        assert!(payload.has_functional_header_marker && payload.has_roi_marker);
        assert_eq!(tile_part.tile_index, payload.tile_index);
    }
}
