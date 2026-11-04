use super::*;

fn defaults() -> (CodingStyle, Quantization) {
    let mut style = raw_resolution_style(0, 7);
    style.decomposition_structure = None;
    style.layers = 2;
    style.transform = WaveletTransform::Reversible5x3;
    (style, Quantization::reversible_default(style))
}

fn tile(length: u32) -> TilePart {
    TilePart {
        start: 0,
        length,
        tile_index: u16::MAX,
        tile_part_index: 0,
        tile_part_count: u8::MAX,
    }
}

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

fn read<'a>(
    parser: &mut Parser<'a>,
    tile: TilePart,
    components: u16,
    progression: ProgressionChanges,
    mct: MctParameters,
    lengths: PacketLengths<'a>,
    headers: PackedPacketHeaders<'a>,
) -> Result<(TilePartPayload<'a>, MctParameters, Part2Extensions), DecodeError> {
    let defaults = defaults();
    parser.read_tile_part(
        tile,
        defaults,
        ComponentCodingStyles {
            components,
            styles: [defaults.0; 64],
        },
        ComponentQuantizations {
            components,
            quantizations: vec![defaults.1; 64],
        },
        RoiShifts::none(),
        progression,
        mct,
        Part2Extensions::default(),
        components,
        lengths,
        headers,
    )
}

fn empty_mct() -> MctParameters {
    MctParameters {
        arrays: Vec::new(),
        records: Vec::new(),
        order: Vec::new(),
    }
}

#[test]
fn actual_tile_part_raw_counts_full_physical_tails_metadata_and_returned_tuple() {
    let limits = ResourceLimits::default();
    let input = [0xff, 0x93, 5, 7, 0xff, 0xd9, 11];
    let mut style = raw_resolution_style(u8::MAX, 7);
    style.layers = u16::MAX;
    let quantization = raw_subband_quantization(QuantizationStyle::ScalarDerived, u16::MAX, 7);
    let inherited_styles = ComponentCodingStyles {
        components: 0,
        styles: core::array::from_fn(|index| raw_resolution_style(index as u8, index)),
    };
    let inherited_quantizations = ComponentQuantizations {
        components: u16::MAX,
        quantizations: vec![
            quantization,
            raw_subband_quantization(QuantizationStyle::None, 0, 3),
        ],
    };
    let roi = RoiShifts {
        shifts: core::array::from_fn(|index| (index * 3) as u8),
    };
    let mut extensions = Part2Extensions::default();
    extensions
        .decomposition_structures
        .push(DecompositionStructure {
            index: 255,
            directions: vec![
                DecompositionDirection::Horizontal,
                DecompositionDirection::Vertical,
            ],
        });
    extensions.component_bit_depths = vec![
        ComponentBitDepth {
            precision: 255,
            signed: true,
        },
        ComponentBitDepth {
            precision: 0,
            signed: false,
        },
    ];
    extensions.metadata_bytes = u64::MAX;
    let lengths = PacketLengths {
        source: PacketLengthSource::None,
        packet_count: u64::MAX,
        encoded_bytes: u64::MAX - 1,
    };
    let headers = PackedPacketHeaders {
        source: PackedPacketHeaderSource::None,
        length: usize::MAX,
        fragments: u16::MAX,
    };
    for zero in [false, true] {
        let mut parser = new_parser(&input, &limits).unwrap();
        parser.work_units = 41;
        parser.packet_length_bytes = 43;
        parser.packet_lengths = 47;
        let (payload, parameters, returned_extensions) = parser
            .read_tile_part(
                tile(if zero { 0 } else { 4 }),
                (style, quantization),
                inherited_styles,
                inherited_quantizations.clone(),
                roi,
                ProgressionChanges::none(),
                empty_mct(),
                extensions.clone(),
                0,
                lengths,
                headers,
            )
            .unwrap();
        assert_eq!(
            payload,
            TilePartPayload {
                tile_index: u16::MAX,
                tile_part_index: 0,
                tile_part_count: u8::MAX,
                coding_style: style,
                quantization,
                component_coding_styles: inherited_styles,
                component_quantizations: inherited_quantizations.clone(),
                roi_shifts: roi,
                progression_changes: ProgressionChanges::none(),
                multiple_component_transform: None,
                part2_extensions: extensions.clone(),
                packet_lengths: lengths,
                packed_packet_headers: headers,
                has_functional_header_marker: false,
                has_roi_marker: false,
                data: &input[2..4],
            }
        );
        assert_eq!(parameters, empty_mct());
        assert_eq!(returned_extensions, extensions);
        assert_eq!(
            frame(&parser),
            (
                input.as_ptr() as usize,
                input.len(),
                limits,
                4,
                if zero { 45 } else { 42 },
                43,
                47
            )
        );
        assert_eq!(payload.data.as_ptr(), input[2..].as_ptr());
    }
}

#[test]
fn actual_tile_part_pending_fragments_precede_component_configuration_and_late_qcd() {
    let limits = ResourceLimits::default();
    let first_mct = mct_i16_segmented(1, 1, &[1], 1)[0].clone();
    let mut first_mcc = mcc(9, 1, true, 1, 0);
    first_mcc[8] = 1;
    for fragment in [first_mct, first_mcc] {
        let mut input = fragment;
        input.extend(super::segment(QCD, &[]));
        input.extend_from_slice(&SOD.to_be_bytes());
        let mut parser = new_parser(&input, &limits).unwrap();
        let style = raw_resolution_style(0, 0);
        let result = parser.read_tile_part(
            tile(u32::MAX),
            (style, defaults().1),
            ComponentCodingStyles {
                components: 1,
                styles: [style; 64],
            },
            ComponentQuantizations {
                components: 0,
                quantizations: Vec::new(),
            },
            RoiShifts::none(),
            ProgressionChanges::none(),
            empty_mct(),
            Part2Extensions::default(),
            1,
            PacketLengths::none(),
            PackedPacketHeaders::none(),
        );
        assert_eq!(
            result,
            Err(input_error_literal(
                input.len(),
                MalformedKind::MissingRequiredStructure
            ))
        );
        assert_eq!(parser.position, input.len());
    }
}

#[test]
fn actual_tile_part_component_then_qcd_then_poc_then_mct_error_precedence() {
    let limits = ResourceLimits::default();
    let input = [super::segment(QCD, &[]), SOD.to_be_bytes().to_vec()].concat();
    let mut style = defaults().0;
    style.decomposition_structure = Some(99);
    let mut parser = new_parser(&input, &limits).unwrap();
    let result = parser.read_tile_part(
        tile(u32::MAX),
        defaults(),
        ComponentCodingStyles {
            components: 1,
            styles: [style; 64],
        },
        ComponentQuantizations::uniform(1, defaults().1).unwrap(),
        RoiShifts::none(),
        ProgressionChanges::none(),
        MctParameters {
            order: vec![99],
            ..empty_mct()
        },
        Part2Extensions::default(),
        1,
        PacketLengths::none(),
        PackedPacketHeaders::none(),
    );
    assert_eq!(
        result,
        Err(input_error_literal(
            0,
            MalformedKind::MissingRequiredStructure
        ))
    );
    let mut parser = new_parser(&input, &limits).unwrap();
    assert_eq!(
        read(
            &mut parser,
            tile(u32::MAX),
            1,
            ProgressionChanges::none(),
            MctParameters {
                order: vec![99],
                ..empty_mct()
            },
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(input_error_literal(0, MalformedKind::InvalidMarkerLength))
    );
    let input = SOD.to_be_bytes();
    let mut parser = new_parser(&input, &limits).unwrap();
    let mut part = tile(u32::MAX);
    part.start = 37;
    let invalid_poc = ProgressionChanges {
        records: vec![ProgressionChange {
            resolution_start: 99,
            component_start: 0,
            layer_end: 1,
            resolution_end: 100,
            component_end: 1,
            progression_order: ProgressionOrder::Lrcp,
        }],
    };
    assert_eq!(
        read(
            &mut parser,
            part,
            1,
            invalid_poc,
            MctParameters {
                order: vec![99],
                ..empty_mct()
            },
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(input_error_literal(
            37,
            MalformedKind::InvalidProgressionOrderChange
        ))
    );
    let mut parser = new_parser(&input, &limits).unwrap();
    assert_eq!(
        read(
            &mut parser,
            part,
            1,
            ProgressionChanges::none(),
            MctParameters {
                order: vec![99],
                ..empty_mct()
            },
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(input_error_literal(0, MalformedKind::InvalidTransform))
    );
    assert_eq!(parser.position, 2);
}

#[test]
fn actual_tile_part_zero_length_commits_early_fixed_length_commits_after_packet_finalizers() {
    let limits = ResourceLimits::default();
    let input = [0xff, 0x93, 7, 9, 0xff, 0xd9];
    for zero in [false, true] {
        for encoded in [&[3][..], &[0x80][..]] {
            let mut parser = new_parser(&input, &limits).unwrap();
            parser.packet_length_bytes = 41;
            parser.packet_lengths = 43;
            let lengths = PacketLengths {
                source: PacketLengthSource::Plm(encoded),
                packet_count: 99,
                encoded_bytes: 97,
            };
            assert_eq!(
                read(
                    &mut parser,
                    tile(if zero { 0 } else { 4 }),
                    1,
                    ProgressionChanges::none(),
                    empty_mct(),
                    lengths,
                    PackedPacketHeaders::none()
                ),
                Err(input_error_literal(0, MalformedKind::InvalidPacketLength))
            );
            assert_eq!(
                frame(&parser),
                (
                    input.as_ptr() as usize,
                    input.len(),
                    limits,
                    if zero { 4 } else { 2 },
                    if zero { 4 } else { 1 },
                    41,
                    43
                )
            );
        }
    }
}

#[test]
fn actual_tile_part_complete_real_producers_packet_header_span_and_payload() {
    let limits = ResourceLimits::default();
    let [cod, qcd] = baseline_headers();
    let headers = [
        qcd,
        cod,
        super::segment(RGN, &[0, 0, 9]),
        poc(&[[0, 0, 0, 1, 1, 1, 0]]),
        super::segment(PLT, &[0, 5]),
        super::segment(PPT, &[0, 7, 9]),
        super::segment(DFS, &[0, 1, 1, 0x40]),
        super::segment(ADS, &[2, 1, 0x40, 1, 0]),
        super::segment(NLT, &[0xff, 0xff, 7, 0]),
        super::segment(ATK, &[0x4a, 2, 0x3f, 0x80, 0, 0, 0]),
        mct_i16(1, 1, &[1]),
        mcc(9, 1, true, 1, 0),
        mco(&[9]),
    ]
    .concat();
    let mut input = headers.clone();
    input.extend_from_slice(&SOD.to_be_bytes());
    input.extend_from_slice(&[3, 4, 5, 0xff, 0xd9]);
    for zero in [false, true] {
        let mut parser = new_parser(&input, &limits).unwrap();
        let (payload, parameters, extensions) = read(
            &mut parser,
            tile(if zero { 0 } else { (headers.len() + 5) as u32 }),
            1,
            ProgressionChanges::none(),
            empty_mct(),
            PacketLengths::none(),
            PackedPacketHeaders::none(),
        )
        .unwrap();
        assert_eq!(payload.tile_index, u16::MAX);
        assert_eq!(payload.tile_part_count, u8::MAX);
        assert_eq!(payload.data, &[3, 4, 5]);
        assert_eq!(payload.data.as_ptr(), input[headers.len() + 2..].as_ptr());
        assert_eq!(payload.coding_style.layers, 1);
        assert_eq!(payload.component_coding_styles.components, 1);
        assert_eq!(payload.component_quantizations.components, 1);
        assert_eq!(payload.roi_shifts.shifts[0], 9);
        assert_eq!(payload.progression_changes.records.len(), 1);
        assert_eq!(
            payload
                .multiple_component_transform
                .as_ref()
                .unwrap()
                .stages
                .len(),
            1
        );
        assert_eq!(parameters.order, [9]);
        assert_eq!(parameters.arrays.len(), 1);
        assert_eq!(parameters.records.len(), 1);
        assert_eq!(payload.part2_extensions, extensions);
        assert_eq!(extensions.decomposition_structures.len(), 1);
        assert_eq!(extensions.arbitrary_decompositions.len(), 1);
        assert_eq!(extensions.nonlinear_transforms.len(), 1);
        assert_eq!(extensions.arbitrary_kernels.len(), 1);
        assert_eq!(
            payload.packet_lengths,
            PacketLengths {
                source: PacketLengthSource::Plt(&input[..headers.len()]),
                packet_count: 1,
                encoded_bytes: 1,
            }
        );
        assert_eq!(
            payload.packed_packet_headers,
            PackedPacketHeaders {
                source: PackedPacketHeaderSource::MarkerSegments {
                    header: &input[..headers.len()],
                    marker: PPT,
                    logical_start: 0,
                },
                length: 2,
                fragments: 1,
            }
        );
        assert_eq!(
            payload.packed_packet_headers.reassemble(&limits).unwrap(),
            [7, 9]
        );
        assert!(payload.has_functional_header_marker && payload.has_roi_marker);
        assert_eq!(
            (
                parser.position,
                parser.packet_length_bytes,
                parser.packet_lengths
            ),
            (headers.len() + 5, 3, 1)
        );
    }
}

#[test]
fn actual_tile_part_header_reader_and_packet_partial_commits_are_not_transactional() {
    let limits = ResourceLimits::default();
    let input = [0xff, 0x93];
    for (position, work, expected_position, kind) in [
        (usize::MAX, 7, usize::MAX, MalformedKind::Truncated),
        (0, u64::MAX, 2, MalformedKind::ArithmeticOverflow),
    ] {
        let mut parser = Parser {
            input: &input,
            limits: &limits,
            position,
            work_units: work,
            packet_length_bytes: 41,
            packet_lengths: 43,
        };
        assert_eq!(
            read(
                &mut parser,
                tile(0),
                0,
                ProgressionChanges::none(),
                empty_mct(),
                PacketLengths::none(),
                PackedPacketHeaders::none()
            ),
            Err(input_error_literal(expected_position, kind))
        );
        assert_eq!(
            frame(&parser),
            (
                input.as_ptr() as usize,
                input.len(),
                limits,
                expected_position,
                work,
                41,
                43
            )
        );
    }
    let input = [
        super::segment(PLT, &[0, 3]),
        SOD.to_be_bytes().to_vec(),
        vec![7, 9, 11],
    ]
    .concat();
    let mut parser = new_parser(&input, &limits).unwrap();
    parser.packet_lengths = u64::MAX;
    assert_eq!(
        read(
            &mut parser,
            tile(input.len() as u32),
            0,
            ProgressionChanges::none(),
            empty_mct(),
            PacketLengths::none(),
            PackedPacketHeaders::none()
        ),
        Err(input_error_literal(0, MalformedKind::ArithmeticOverflow))
    );
    assert_eq!(
        frame(&parser),
        (
            input.as_ptr() as usize,
            input.len(),
            limits,
            6,
            2,
            1,
            u64::MAX
        )
    );
}
