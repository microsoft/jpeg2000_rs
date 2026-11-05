use super::*;

#[test]
fn actual_tile_loop_metadata_preserves_raw_tables_offsets_sources_and_reader() {
    let input = [11, 13, 17];
    let limits = ResourceLimits::HARDENED;
    let parser = Parser {
        input: &input,
        limits: &limits,
        position: 19,
        work_units: u64::MAX,
        packet_length_bytes: u64::MAX,
        packet_lengths: 31,
    };
    let before = frame(&parser);
    let mut cases = 0;
    for geometry in 0..27 {
        let lengths = [geometry % 3, geometry / 3 % 3, geometry / 9];
        let lengths = lengths.map(|value| [0, 1, 3][value]);
        for part_index in [0, 1, 3, u32::MAX] {
            for pattern in 0..4 {
                for plm_seen in [false, true] {
                    for fragments in [0, 1, u16::MAX] {
                        for variant in 0..3 {
                            for start in [0, usize::MAX] {
                                let tile = TilePart {
                                    start,
                                    length: [0, 7, u32::MAX][variant],
                                    tile_index: [0, 1, u16::MAX][variant],
                                    tile_part_index: u8::MAX,
                                    tile_part_count: 0,
                                };
                                let tlm: Vec<_> = (0..lengths[0])
                                    .map(|_| TilePartLength {
                                        tile_index: match pattern {
                                            0 => None,
                                            2 => Some(tile.tile_index ^ 1),
                                            _ => Some(tile.tile_index),
                                        },
                                        length: if pattern == 3 {
                                            tile.length ^ 1
                                        } else {
                                            tile.length
                                        },
                                    })
                                    .collect();
                                let plm: Vec<_> = (0..lengths[1])
                                    .map(|index| PacketLengths {
                                        source: match index {
                                            0 => PacketLengthSource::None,
                                            1 => PacketLengthSource::Plm(&input),
                                            _ => PacketLengthSource::Plt(&input[1..]),
                                        },
                                        packet_count: u64::MAX - index as u64,
                                        encoded_bytes: index as u64,
                                    })
                                    .collect();
                                let ppm: Vec<_> = (0..lengths[2])
                                    .map(|index| PackedHeaderFrame {
                                        start: usize::MAX - index,
                                        length: if index == 0 { 0 } else { usize::MAX },
                                    })
                                    .collect();
                                let selected = usize::try_from(u64::from(part_index)).unwrap();
                                let error = if !tlm.is_empty()
                                    && tlm.get(selected).is_none_or(|entry| {
                                        entry.length != tile.length
                                            || entry
                                                .tile_index
                                                .is_some_and(|index| index != tile.tile_index)
                                    }) {
                                    Some(MalformedKind::InvalidTilePart)
                                } else if plm_seen && selected >= plm.len() {
                                    Some(MalformedKind::InvalidPacketLength)
                                } else if fragments != 0 && selected >= ppm.len() {
                                    Some(MalformedKind::InvalidPackedPacketHeader)
                                } else {
                                    None
                                };
                                let expected = match error {
                                    Some(kind) => Err(input_error_literal(start, kind)),
                                    None => Ok((
                                        if plm_seen {
                                            plm[selected]
                                        } else {
                                            PacketLengths::none()
                                        },
                                        if fragments == 0 {
                                            PackedPacketHeaders::none()
                                        } else {
                                            PackedPacketHeaders {
                                                source: PackedPacketHeaderSource::MarkerSegments {
                                                    header: &input,
                                                    marker: PPM,
                                                    logical_start: ppm[selected].start,
                                                },
                                                length: ppm[selected].length,
                                                fragments,
                                            }
                                        },
                                    )),
                                };
                                let result = parser.tile_part_main_metadata(
                                    tile, part_index, &tlm, plm_seen, &plm, &ppm, fragments, &input,
                                );
                                assert_eq!(
                                    result, expected,
                                    "geometry={lengths:?}, part_index={part_index}, pattern={pattern}"
                                );
                                if let Ok(value) = &result {
                                    fn copy_only<T: Copy>(_: &T) {}
                                    copy_only(value);
                                    if let PackedPacketHeaderSource::MarkerSegments {
                                        header, ..
                                    } = value.1.source
                                    {
                                        assert!(core::ptr::eq(header.as_ptr(), input.as_ptr()));
                                    }
                                }
                                assert_eq!(frame(&parser), before);
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 15_552);
}

#[test]
fn actual_tile_loop_termination_preserves_all_error_prefixes_and_reader_frames() {
    let limits = ResourceLimits::HARDENED;
    let inputs: &[(&[u8], usize, Option<MalformedKind>, usize)] = &[
        (&[], 0, Some(MalformedKind::Truncated), 0),
        (&[0xff], 0, Some(MalformedKind::Truncated), 0),
        (&[0xff, 0xd9], 0, None, 2),
        (&[0xff, 0xd9, 17], 0, None, 2),
        (&[0xff, 0x90], 0, Some(MalformedKind::InvalidMarkerOrder), 0),
        (&[0xfe, 0xd9], 0, Some(MalformedKind::InvalidMarker), 0),
        (&[0xff, 0], 0, Some(MalformedKind::InvalidMarker), 0),
        (&[0xff, 0xff], 0, Some(MalformedKind::InvalidMarker), 0),
        (&[0, 0xff, 0xd9], 1, None, 3),
        (&[0, 0xff, 0xd9], 2, Some(MalformedKind::Truncated), 2),
        (
            &[0xff, 0xd9],
            usize::MAX,
            Some(MalformedKind::Truncated),
            usize::MAX,
        ),
    ];
    let mut cases = 0;
    for &(input, position, marker_error, consumed) in inputs {
        for parts in [0, 1, 2, u32::MAX] {
            for plm_seen in [false, true] {
                for fragments in [0, 1, u16::MAX] {
                    for geometry in 0..64 {
                        let counts = [geometry % 4, geometry / 4 % 4, geometry / 16]
                            .map(|index| [0, 1, 2, usize::MAX][index]);
                        for work in [0, limits.maximum_work_units(), u64::MAX] {
                            let mut parser = Parser {
                                input,
                                limits: &limits,
                                position,
                                work_units: work,
                                packet_length_bytes: u64::MAX,
                                packet_lengths: 37,
                            };
                            let mut expected_position = position;
                            let mut expected_work = work;
                            let expected = if parts == 0 {
                                Err(input_error_literal(
                                    position,
                                    MalformedKind::InvalidMarkerOrder,
                                ))
                            } else if let Some(kind) = marker_error {
                                Err(input_error_literal(position, kind))
                            } else {
                                expected_position = consumed;
                                let next_work = u128::from(work) + 1;
                                if next_work > u128::from(u64::MAX) {
                                    Err(input_error_literal(
                                        consumed,
                                        MalformedKind::ArithmeticOverflow,
                                    ))
                                } else {
                                    expected_work = next_work as u64;
                                    if expected_work > limits.maximum_work_units() {
                                        Err(DecodeError::limit(
                                            Resource::WorkUnits,
                                            limits.maximum_work_units(),
                                            expected_work,
                                        ))
                                    } else {
                                        let kind = if plm_seen && counts[0] != parts as usize {
                                            Some(MalformedKind::InvalidPacketLength)
                                        } else if fragments != 0 && counts[1] != parts as usize {
                                            Some(MalformedKind::InvalidPackedPacketHeader)
                                        } else if counts[2] != 0 && counts[2] != parts as usize {
                                            Some(MalformedKind::InvalidTilePart)
                                        } else if consumed != input.len() {
                                            Some(MalformedKind::TrailingData)
                                        } else {
                                            None
                                        };
                                        match kind {
                                            Some(kind) => Err(input_error_literal(consumed, kind)),
                                            None => Ok(()),
                                        }
                                    }
                                }
                            };
                            assert_eq!(
                                parser.finish_tile_part_traversal(
                                    parts, plm_seen, counts[0], fragments, counts[1], counts[2]
                                ),
                                expected,
                                "input={input:?}, position={position}, parts={parts}, counts={counts:?}, work={work}",
                            );
                            assert_eq!(
                                frame(&parser),
                                (
                                    input.as_ptr() as usize,
                                    input.len(),
                                    limits,
                                    expected_position,
                                    expected_work,
                                    u64::MAX,
                                    37,
                                )
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 50_688);
}

#[test]
fn actual_tile_loop_joins_raw_tlm_plm_ppm_and_eoc_first_error_order() {
    let limits = ResourceLimits::default();
    for (plm_count, ppm_count, tlm_count, trailing, expected) in [
        (1, 1, 1, false, None),
        (2, 2, 2, true, Some(MalformedKind::InvalidPacketLength)),
        (
            1,
            2,
            2,
            true,
            Some(MalformedKind::InvalidPackedPacketHeader),
        ),
        (1, 1, 2, true, Some(MalformedKind::InvalidTilePart)),
        (1, 1, 1, true, Some(MalformedKind::TrailingData)),
    ] {
        let mut tlm = vec![0, 0x40];
        for _ in 0..tlm_count {
            tlm.extend(15_u32.to_be_bytes());
        }
        let mut ppm = Vec::new();
        for _ in 0..ppm_count {
            ppm.extend([0, 0, 0, 1, 0]);
        }
        let groups: Vec<&[u32]> = vec![&[2]; plm_count];
        let mut bytes = codestream_with_headers(
            1,
            &[
                segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]),
                segment(QCD, &[0, 0]),
                segment(TLM, &tlm),
                plm(0, &groups),
                super::ppm(0, &ppm),
            ],
            &[],
            &[17],
        );
        let consumed = bytes.len();
        if trailing {
            bytes.push(19);
        }
        match expected {
            Some(kind) => assert_eq!(
                parse_layout(&bytes, &limits).unwrap_err(),
                input_error_literal(consumed, kind)
            ),
            None => {
                let layout = parse_layout(&bytes, &limits).unwrap();
                assert_eq!(layout.info.tile_parts, 1);
                assert_eq!(layout.info.consumed_bytes, bytes.len() as u64);
                let payload = &layout.tile_parts[0];
                assert_eq!(payload.data, &[17]);
                assert_eq!(payload.packet_lengths.packet_count(), 1);
                assert_eq!(
                    payload.packet_lengths.iter().next_length().unwrap(),
                    Some(2)
                );
                assert_eq!(
                    payload.packed_packet_headers.reassemble(&limits).unwrap(),
                    [0]
                );
            }
        }
    }
}

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
