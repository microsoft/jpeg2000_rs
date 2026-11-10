use super::*;

#[test]
fn precinct_context_preparation_preserves_raw_prefixes_and_exact_leaf_metadata() {
    let style = Tier1CodingStyle {
        force_high_throughput: true,
        ..Tier1CodingStyle::default()
    };
    let mut cases = 0;
    for states_len in [0, 1, 3] {
        for contexts_len in [0, 1, 4] {
            for count in [0, 1, 2, 3, 7, 32] {
                for across in [0, 1, 2, 3, u32::MAX] {
                    for maximum_zero in [0, 1, u16::MAX] {
                        let state = CodeBlockPacketState {
                            included: true,
                            zero_bitplanes: Some(u16::MAX),
                            lblock: u8::MAX,
                            total_passes: u32::MAX,
                            high_throughput: Some(true),
                        };
                        let context = CodeBlockPacketContext {
                            leaf_x: u32::MAX,
                            leaf_y: u32::MAX,
                            layer: u16::MAX,
                            maximum_zero_bitplanes: u16::MAX,
                            tier1_style: style,
                        };
                        let states = vec![state; states_len];
                        let contexts = vec![context; contexts_len];
                        let expected = if count != 0 && across == 0 {
                            Err(DecodeError::MalformedInput {
                                offset: 0,
                                kind: MalformedKind::ArithmeticOverflow,
                            })
                        } else {
                            let mut expected_states = states.clone();
                            let mut expected_contexts = contexts.clone();
                            for index in 0..count {
                                expected_states.push(CodeBlockPacketState {
                                    included: false,
                                    zero_bitplanes: None,
                                    lblock: 3,
                                    total_passes: 0,
                                    high_throughput: None,
                                });
                                expected_contexts.push(CodeBlockPacketContext {
                                    leaf_x: u32::try_from(index).unwrap() % across,
                                    leaf_y: u32::try_from(index).unwrap() / across,
                                    layer: 0,
                                    maximum_zero_bitplanes: maximum_zero,
                                    tier1_style: style,
                                });
                            }
                            Ok((expected_states, expected_contexts))
                        };
                        assert_eq!(
                            prepare_precinct_contexts(
                                states,
                                contexts,
                                count,
                                across,
                                maximum_zero,
                                style
                            ),
                            expected
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 810);
}

fn precinct_execution_fixture(
    rows: usize,
    across: u32,
    down: u32,
    maximum_zero: u16,
    count: usize,
) -> Vec<PacketSubbandExecution> {
    (0..rows)
        .map(|row| {
            let last = row + 1 == rows;
            PacketSubbandExecution {
                orientation: [
                    SubbandOrientation::Hh,
                    SubbandOrientation::Ll,
                    SubbandOrientation::Hl,
                ][row % 3],
                code_blocks_across: if last { across } else { 1 },
                code_blocks_down: if last { down } else { 1 },
                maximum_zero_bitplanes: if last { maximum_zero } else { 8 },
                decoders: (0..if last { count } else { 1 })
                    .map(|index| {
                        let mut decoder = Tier1CodeBlockDecoder::new(
                            1,
                            1,
                            8,
                            SubbandOrientation::Lh,
                            Tier1CodingStyle::default(),
                        )
                        .unwrap();
                        decoder.set_multiple_ht_sets_allowed(index % 2 != 0);
                        decoder
                            .set_ht_magnitude_bound(u8::try_from(index % 74 + 1).unwrap())
                            .unwrap();
                        decoder
                    })
                    .collect(),
            }
        })
        .collect()
}

fn reference_precinct_initialization(
    coordinate: (u16, u8, u32),
    style: Tier1CodingStyle,
    executions: Vec<PacketSubbandExecution>,
    limits: &ResourceLimits,
) -> Result<PacketPrecinctDecoder, DecodeError> {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidPacketHeader,
    };
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    if executions.len() > 3 {
        return Err(invalid);
    }
    let mut states = Vec::new();
    let mut contexts = Vec::new();
    let mut decoders = Vec::new();
    let mut subbands = Vec::new();
    let mut total = 0_u64;
    for execution in executions {
        if execution.code_blocks_across == 0
            || execution.code_blocks_down == 0
            || execution.maximum_zero_bitplanes == 0
            || execution.maximum_zero_bitplanes > crate::tier1::MAX_TIER1_BITPLANES
        {
            return Err(invalid);
        }
        let count =
            u128::from(execution.code_blocks_across) * u128::from(execution.code_blocks_down);
        total = u64::try_from(u128::from(total) + count).map_err(|_| arithmetic)?;
        for (resource, limit) in [
            (Resource::CodeBlocks, limits.maximum_code_blocks()),
            (Resource::WorkUnits, limits.maximum_work_units()),
        ] {
            if total > limit {
                return Err(DecodeError::LimitExceeded {
                    resource,
                    limit,
                    actual: total,
                });
            }
        }
        let count = usize::try_from(count).map_err(|_| arithmetic)?;
        if count != execution.decoders.len() {
            return Err(invalid);
        }
        let first_decoder = decoders.len();
        for index in 0..count {
            let index = u32::try_from(index).map_err(|_| arithmetic)?;
            states.push(CodeBlockPacketState {
                included: false,
                zero_bitplanes: None,
                lblock: 3,
                total_passes: 0,
                high_throughput: None,
            });
            contexts.push(CodeBlockPacketContext {
                leaf_x: index % execution.code_blocks_across,
                leaf_y: index / execution.code_blocks_across,
                layer: 0,
                maximum_zero_bitplanes: execution.maximum_zero_bitplanes,
                tier1_style: style,
            });
        }
        decoders.extend(execution.decoders);
        subbands.push(PacketSubbandState {
            orientation: execution.orientation,
            first_decoder,
            decoder_count: count,
            code_blocks_across: execution.code_blocks_across,
            code_blocks_down: execution.code_blocks_down,
            inclusion_tree: TagTree::new(
                execution.code_blocks_across,
                execution.code_blocks_down,
                limits,
            )?,
            zero_bitplane_tree: TagTree::new(
                execution.code_blocks_across,
                execution.code_blocks_down,
                limits,
            )?,
        });
    }
    Ok(PacketPrecinctDecoder {
        component: coordinate.0,
        resolution: coordinate.1,
        precinct: coordinate.2,
        states,
        contexts,
        decoders,
        subbands,
    })
}

#[test]
fn actual_precinct_initialization_keeps_all_owned_state_limits_and_empty_policy() {
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(1)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(1).unwrap(),
    ];
    let styles = [
        Tier1CodingStyle::default(),
        Tier1CodingStyle {
            block_coding: crate::tier1::Tier1BlockCoding::Mixed,
            force_high_throughput: true,
            reset_contexts: true,
            ..Tier1CodingStyle::default()
        },
    ];
    let mut cases = 0;
    let mut successes = 0;
    for rows in 0..=4 {
        for across in [0, 1, 2, u32::MAX] {
            for down in [0, 1, 2, u32::MAX] {
                for maximum_zero in [0, 1, 74, 75] {
                    for count in [0, 1, 2, 3, 4] {
                        for limit in &limits {
                            for coordinate in [(0, 0, 0), (u16::MAX, u8::MAX, u32::MAX), (1, 1, 17)]
                            {
                                for style in styles {
                                    let expected = reference_precinct_initialization(
                                        coordinate,
                                        style,
                                        precinct_execution_fixture(
                                            rows,
                                            across,
                                            down,
                                            maximum_zero,
                                            count,
                                        ),
                                        limit,
                                    )
                                    .map(|value| exact_packet_precinct_snapshot(&value));
                                    let actual = packet_precinct_from_subbands(
                                        coordinate.0,
                                        coordinate.1,
                                        coordinate.2,
                                        style,
                                        precinct_execution_fixture(
                                            rows,
                                            across,
                                            down,
                                            maximum_zero,
                                            count,
                                        ),
                                        limit,
                                    )
                                    .map(|value| exact_packet_precinct_snapshot(&value));
                                    let public = PacketPrecinctDecoder::new_subbands(
                                        coordinate.0,
                                        coordinate.1,
                                        coordinate.2,
                                        style,
                                        precinct_execution_fixture(
                                            rows,
                                            across,
                                            down,
                                            maximum_zero,
                                            count,
                                        ),
                                        limit,
                                    )
                                    .map(|value| exact_packet_precinct_snapshot(&value));
                                    successes += usize::from(expected.is_ok());
                                    assert_eq!(actual, expected);
                                    assert_eq!(public, expected);
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 28_800);
    assert!(successes > 100, "{successes} full precinct states checked");
}

fn literal_one_node_tree(low: u32, value: u32) -> TagTree {
    TagTree {
        levels: vec![TagTreeLevel {
            offset: 0,
            width: 1,
            height: 1,
        }],
        nodes: vec![TagTreeNode { low, value }],
    }
}

fn literal_header_context(style: Tier1CodingStyle) -> CodeBlockPacketContext {
    CodeBlockPacketContext {
        leaf_x: 0,
        leaf_y: 0,
        layer: 0,
        maximum_zero_bitplanes: 2,
        tier1_style: style,
    }
}

#[test]
fn typed_header_factories_observe_real_limits_and_preserve_prefix_admission() {
    let limits = ResourceLimits::default()
        .with_maximum_packet_header_bytes(1)
        .unwrap()
        .with_maximum_work_units(1)
        .unwrap();
    assert_eq!(
        packet_reader_new(&[0, 0], &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::PacketHeaderBytes,
            limit: 1,
            actual: 2,
        })
    );
    let expected = PacketBitReader {
        input: &[0, 0],
        byte_index: 0,
        current_byte: 0,
        bits_remaining: 0,
        previous_byte_was_ff: false,
        bits_read: 0,
        maximum_work_units: 1,
        maximum_header_bytes: 1,
    };
    assert_eq!(packet_reader_prefix(&[0, 0], &limits), expected);
    assert_eq!(
        tag_tree_new(u32::MAX, u32::MAX, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::TagTreeNodes,
            limit: limits.maximum_tag_tree_nodes(),
            actual: u64::from(u32::MAX) * u64::from(u32::MAX),
        })
    );
    let expected = TagTree {
        levels: vec![
            TagTreeLevel {
                offset: 0,
                width: 2,
                height: 1,
            },
            TagTreeLevel {
                offset: 2,
                width: 1,
                height: 1,
            },
        ],
        nodes: vec![
            TagTreeNode {
                low: 0,
                value: u32::MAX
            };
            3
        ],
    };
    assert_eq!(tag_tree_new(2, 1, &limits), Ok(expected.clone()));
    assert_eq!(TagTree::new(2, 1, &limits), Ok(expected));
}

#[test]
fn actual_full_header_literal_and_every_work_prefix_have_independent_whole_results() {
    for cap in 0_u64..=8 {
        let mut state = code_block_packet_state_new();
        let original = state;
        let mut inclusion = literal_one_node_tree(0, u32::MAX);
        let mut zero = literal_one_node_tree(0, u32::MAX);
        let mut reader = packet_reader_prefix_from_input(&[0xc2], 1, cap);
        let result = decode_code_block_contribution(
            &mut state,
            &mut inclusion,
            &mut zero,
            literal_header_context(Tier1CodingStyle::default()),
            &mut reader,
        );
        let consumed = if cap < 7 { cap + 1 } else { 7 };
        assert_eq!(
            reader,
            PacketBitReader {
                input: &[0xc2],
                byte_index: 1,
                current_byte: 0xc2,
                bits_remaining: (8 - consumed) as u8,
                previous_byte_was_ff: false,
                bits_read: consumed,
                maximum_work_units: cap,
                maximum_header_bytes: 1,
            }
        );
        assert_eq!(
            inclusion,
            literal_one_node_tree(0, if cap >= 1 { 0 } else { u32::MAX })
        );
        assert_eq!(
            zero,
            literal_one_node_tree(0, if cap >= 2 { 0 } else { u32::MAX })
        );
        if cap < 7 {
            assert_eq!(state, original);
            assert_eq!(
                result,
                Err(packet_reader_limit(Resource::WorkUnits, cap, cap + 1))
            );
        } else {
            assert_eq!(
                state,
                CodeBlockPacketState {
                    included: true,
                    zero_bitplanes: Some(0),
                    lblock: 3,
                    total_passes: 1,
                    high_throughput: Some(false),
                }
            );
            let mut passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
            let mut lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
            passes[0] = 1;
            lengths[0] = 1;
            assert_eq!(
                result,
                Ok(Some(CodeBlockContribution {
                    first_inclusion: true,
                    zero_bitplanes: 0,
                    new_passes: 1,
                    data_length: 1,
                    high_throughput: false,
                    segment_count: 1,
                    segment_passes: passes,
                    segment_lengths: lengths,
                }))
            );
        }
    }
}

#[test]
fn full_header_admits_every_stored_lblock_byte_and_does_not_validate_unvisited_zero_tree() {
    for lblock in 0..=u8::MAX {
        let mut state = CodeBlockPacketState {
            included: true,
            zero_bitplanes: Some(u16::MAX),
            lblock,
            total_passes: 1,
            high_throughput: Some(false),
        };
        let original = state;
        let mut inclusion = TagTree {
            levels: vec![],
            nodes: vec![],
        };
        let mut zero = TagTree {
            levels: vec![],
            nodes: vec![],
        };
        let input = [0x80, 0, 0, 0, 0];
        let mut reader = packet_reader_prefix_from_input(&input, 5, 64);
        let mut context = literal_header_context(Tier1CodingStyle::default());
        context.maximum_zero_bitplanes = 1;
        let result = decode_code_block_contribution(
            &mut state,
            &mut inclusion,
            &mut zero,
            context,
            &mut reader,
        );
        let consumed = if lblock <= 32 {
            3 + u64::from(lblock)
        } else {
            3
        };
        let index = consumed.div_ceil(8) as usize;
        assert_eq!(
            reader,
            PacketBitReader {
                input: &input,
                byte_index: index,
                current_byte: if index == 1 { 0x80 } else { 0 },
                bits_remaining: ((8 - consumed % 8) % 8) as u8,
                previous_byte_was_ff: false,
                bits_read: consumed,
                maximum_work_units: 64,
                maximum_header_bytes: 5,
            }
        );
        assert!(
            inclusion.levels.is_empty()
                && inclusion.nodes.is_empty()
                && zero.levels.is_empty()
                && zero.nodes.is_empty()
        );
        if lblock > 32 {
            assert_eq!(
                result,
                Err(packet_reader_error(1, MalformedKind::InvalidPacketHeader))
            );
            assert_eq!(state, original);
        } else {
            let mut passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
            passes[0] = 1;
            assert_eq!(
                result,
                Ok(Some(CodeBlockContribution {
                    first_inclusion: false,
                    zero_bitplanes: u16::MAX,
                    new_passes: 1,
                    data_length: 0,
                    high_throughput: false,
                    segment_count: 1,
                    segment_passes: passes,
                    segment_lengths: [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
                }))
            );
            assert_eq!(
                state,
                CodeBlockPacketState {
                    total_passes: 2,
                    ..original
                }
            );
        }
    }
}

#[test]
fn header_none_empty_unused_raw_trees_and_late_error_rollback_are_distinct() {
    let mut state = code_block_packet_state_new();
    let original = state;
    let mut inclusion = literal_one_node_tree(1, 1);
    let mut zero = TagTree {
        levels: vec![],
        nodes: vec![],
    };
    let mut reader = packet_reader_prefix_from_input(&[], 0, 0);
    reader.bits_remaining = u8::MAX;
    let before = reader;
    assert_eq!(
        decode_code_block_contribution(
            &mut state,
            &mut inclusion,
            &mut zero,
            literal_header_context(Tier1CodingStyle::default()),
            &mut reader
        ),
        Ok(None)
    );
    assert_eq!(state, original);
    assert_eq!(reader, before);
    assert_eq!(inclusion, literal_one_node_tree(1, 1));
    assert_eq!(
        zero,
        TagTree {
            levels: vec![],
            nodes: vec![]
        }
    );

    let mut state = CodeBlockPacketState {
        included: true,
        zero_bitplanes: Some(0),
        lblock: 0,
        total_passes: 1,
        high_throughput: Some(false),
    };
    let mut inclusion = TagTree {
        levels: vec![],
        nodes: vec![],
    };
    let mut reader = packet_reader_prefix_from_input(&[0x80], 1, 3);
    let result = decode_code_block_contribution(
        &mut state,
        &mut inclusion,
        &mut zero,
        literal_header_context(Tier1CodingStyle::default()),
        &mut reader,
    )
    .unwrap()
    .unwrap();
    let mut passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    passes[0] = 1;
    assert_eq!(
        result,
        CodeBlockContribution {
            first_inclusion: false,
            zero_bitplanes: 0,
            new_passes: 1,
            data_length: 0,
            high_throughput: false,
            segment_count: 1,
            segment_passes: passes,
            segment_lengths: [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
        }
    );
    assert_eq!(state.total_passes, 2);
    assert_eq!(reader.bits_read, 3);
    assert!(inclusion.levels.is_empty() && zero.levels.is_empty());
    for total in [crate::tier1::MAX_TIER1_PASSES, u32::MAX] {
        let mut state = CodeBlockPacketState {
            included: true,
            zero_bitplanes: Some(0),
            lblock: 3,
            total_passes: total,
            high_throughput: Some(false),
        };
        let before = state;
        let mut reader = packet_reader_prefix_from_input(&[0x84], 1, 64);
        assert_eq!(
            decode_code_block_contribution(
                &mut state,
                &mut inclusion,
                &mut zero,
                literal_header_context(Tier1CodingStyle::default()),
                &mut reader
            ),
            Err(packet_reader_error(
                1,
                if total == u32::MAX {
                    MalformedKind::ArithmeticOverflow
                } else {
                    MalformedKind::InvalidPacketHeader
                }
            ))
        );
        assert_eq!(state, before);
        assert_eq!(
            (reader.bits_read, reader.byte_index, reader.bits_remaining),
            (6, 1, 2)
        );
    }
}

#[test]
fn actual_mixed_header_probe_commits_only_selected_reader_and_preserves_failed_main_cursor() {
    for (lblock, input, primary_bits, expected_passes, expected_length, route, consumed) in [
        (3_u8, 0x38_u8, 3_u8, 4_u32, 7_u32, Some(false), 5_u64),
        (4, 0x1c, 4, 1, 1, Some(true), 4),
        (3, 0, 3, 1, 0, None, 3),
    ] {
        let mut state = CodeBlockPacketState {
            included: true,
            zero_bitplanes: Some(0),
            lblock,
            total_passes: 0,
            high_throughput: None,
        };
        let mut segments = header_segments_new(
            &state,
            Tier1CodingStyle::from_code_block_style(0xc0).unwrap(),
        );
        let data = [input];
        let mut reader = packet_reader_prefix_from_input(&data, 1, 64);
        assert_eq!(
            read_header_segment_length(
                &mut state,
                &mut segments,
                &mut reader,
                0,
                4,
                1,
                primary_bits
            ),
            Ok((expected_passes, expected_length))
        );
        assert_eq!(state.high_throughput, route);
        assert_eq!(segments.routing, route);
        assert_eq!(
            reader,
            PacketBitReader {
                input: &[input],
                byte_index: 1,
                current_byte: input,
                bits_remaining: (8 - consumed) as u8,
                previous_byte_was_ff: false,
                bits_read: consumed,
                maximum_work_units: 64,
                maximum_header_bytes: 1,
            }
        );
    }
    let mut state = CodeBlockPacketState {
        included: true,
        zero_bitplanes: Some(0),
        lblock: 4,
        total_passes: 0,
        high_throughput: None,
    };
    let before = state;
    let mut segments = header_segments_new(
        &state,
        Tier1CodingStyle::from_code_block_style(0xc0).unwrap(),
    );
    let mut reader = packet_reader_prefix_from_input(&[0x1c], 1, 4);
    assert_eq!(
        read_header_segment_length(&mut state, &mut segments, &mut reader, 0, 4, 1, 4),
        Err(packet_reader_limit(Resource::WorkUnits, 4, 5))
    );
    assert_eq!(state, before);
    assert_eq!(segments.routing, None);
    assert_eq!(
        reader,
        PacketBitReader {
            input: &[0x1c],
            byte_index: 1,
            current_byte: 0x1c,
            bits_remaining: 4,
            previous_byte_was_ff: false,
            bits_read: 4,
            maximum_work_units: 4,
            maximum_header_bytes: 1,
        }
    );
    let mut reader = packet_reader_prefix_from_input(&[0x10], 2, 64);
    assert_eq!(
        read_header_segment_length(&mut state, &mut segments, &mut reader, 0, 164, 1, 4),
        Err(packet_reader_error(1, MalformedKind::Truncated))
    );
    assert_eq!(reader.bits_read, 4);
    assert_eq!(reader.bits_remaining, 4);
    assert_eq!(state, before);
}

#[test]
fn native_header_segment_capacity_and_final_count_conversion_keep_exact_order() {
    let mut state = CodeBlockPacketState {
        included: true,
        zero_bitplanes: Some(0),
        lblock: 3,
        total_passes: 0,
        high_throughput: Some(false),
    };
    let original = state;
    for count in [164, 165, usize::MAX] {
        let mut segments = header_segments_new(&state, Tier1CodingStyle::default());
        segments.segment_count = count;
        state.total_passes = u32::MAX;
        let before = state;
        let mut reader = packet_reader_prefix_from_input(&[], 0, 0);
        reader.byte_index = 17;
        let old_reader = reader;
        assert_eq!(
            read_header_segment(
                &mut state,
                &mut segments,
                u8::MAX,
                literal_header_context(Tier1CodingStyle::default()),
                &mut reader
            ),
            Err(packet_reader_error(17, MalformedKind::InvalidPacketHeader))
        );
        assert_eq!(state, before);
        assert_eq!(reader, old_reader);
        assert_eq!(segments.segment_count, count);
    }
    for count in [164, 165, 256] {
        state = original;
        let mut segments = header_segments_new(&state, Tier1CodingStyle::default());
        segments.segment_count = count;
        let next = state;
        let mut reader = packet_reader_prefix_from_input(&[], 0, 0);
        reader.byte_index = 17;
        let result = commit_header_contribution(&mut state, next, segments, false, 1, &reader);
        assert_eq!(
            state,
            CodeBlockPacketState {
                total_passes: 1,
                ..original
            }
        );
        if count <= 255 {
            assert_eq!(result.unwrap().unwrap().segment_count(), count as u8);
        } else {
            assert_eq!(
                result,
                Err(packet_reader_error(17, MalformedKind::ArithmeticOverflow))
            );
        }
    }
}

#[test]
fn packet_reader_words_match_closed_two_byte_oracle_and_all_eight_final_fields() {
    for first in 0..=u8::MAX {
        for second in 0..=u8::MAX {
            let input = [first, second];
            for count in [0_u8, 1, 7, 8, 9, 15, 16, 32] {
                let mut reader = packet_reader_prefix_from_input(&input, 32, 64);
                let result = reader.read_bits(count);
                let stuffed = first == 0xff;
                let invalid_stuff = stuffed && second >= 0x80 && count > 8;
                let available = if stuffed { 15_u8 } else { 16 };
                let read = if invalid_stuff {
                    8
                } else {
                    count.min(available)
                };
                let expected_result = if invalid_stuff {
                    Err(packet_reader_error(1, MalformedKind::InvalidBitStuffing))
                } else if count > available {
                    Err(packet_reader_error(2, MalformedKind::Truncated))
                } else if count == 0 {
                    Ok(0)
                } else if count <= 8 {
                    Ok(u32::from(first) >> (8 - count))
                } else if stuffed {
                    Ok((255_u32 << (count - 8)) | (u32::from(second) >> (15 - count)))
                } else {
                    Ok(((u32::from(first) * 256) + u32::from(second)) >> (16 - count))
                };
                let loaded_second = read > 8;
                assert_eq!(result, expected_result, "input={input:?}, count={count}");
                assert_eq!(
                    reader,
                    PacketBitReader {
                        input: &input,
                        byte_index: if read == 0 {
                            0
                        } else if loaded_second {
                            2
                        } else {
                            1
                        },
                        current_byte: if read == 0 {
                            0
                        } else if loaded_second {
                            second
                        } else {
                            first
                        },
                        bits_remaining: if loaded_second {
                            available - read
                        } else if read == 0 {
                            0
                        } else {
                            8 - read
                        },
                        previous_byte_was_ff: read != 0
                            && if loaded_second {
                                second == 0xff
                            } else {
                                stuffed
                            },
                        bits_read: u64::from(read),
                        maximum_work_units: 64,
                        maximum_header_bytes: 32,
                    }
                );
            }
        }
    }
}

#[test]
fn packet_reader_native_state_errors_preserve_exact_admission_and_consumption_order() {
    let mut reader = packet_reader_prefix_from_input(&[], 0, 0);
    let before = reader;
    assert_eq!(
        reader.read_bit(),
        Err(packet_reader_limit(Resource::PacketHeaderBytes, 0, 1))
    );
    assert_eq!(reader, before);
    reader.byte_index = usize::MAX;
    reader.maximum_header_bytes = u64::MAX;
    let before = reader;
    assert_eq!(
        reader.read_bit(),
        Err(packet_reader_error(
            usize::MAX,
            if usize::BITS == 64 {
                MalformedKind::ArithmeticOverflow
            } else {
                MalformedKind::Truncated
            }
        ))
    );
    assert_eq!(reader, before);
}

#[test]
fn raw_tag_tree_single_node_matches_wide_threshold_and_budget_oracle() {
    for low in [0, 1, 3, u32::MAX - 1, u32::MAX] {
        for value in [0, 1, 4, u32::MAX - 1, u32::MAX] {
            for threshold in [0, 1, 2, 4, u32::MAX] {
                for cap in [0_u64, 1, 2, 8] {
                    let mut tree = TagTree {
                        levels: vec![TagTreeLevel {
                            offset: 0,
                            width: 1,
                            height: 1,
                        }],
                        nodes: vec![TagTreeNode { low, value }],
                    };
                    let before = tree.clone();
                    let mut reader = packet_reader_prefix_from_input(&[0], 1, cap);
                    let needed = u64::from(threshold.min(value)).saturating_sub(u64::from(low));
                    let successful = needed.min(cap).min(8);
                    let mut expected_tree = before;
                    expected_tree.nodes[0].low = (u64::from(low) + successful) as u32;
                    let actual = tree.decode(0, 0, threshold, &mut reader);
                    let consumed = if needed > cap && cap < 8 {
                        cap + 1
                    } else {
                        successful
                    };
                    let expected = if needed > cap && cap < 8 {
                        Err(packet_reader_limit(Resource::WorkUnits, cap, cap + 1))
                    } else if needed > 8 {
                        Err(packet_reader_limit(Resource::PacketHeaderBytes, 1, 2))
                    } else {
                        Ok(TagTreeValue {
                            value: if value < threshold { Some(value) } else { None },
                            is_below_threshold: value < threshold,
                        })
                    };
                    assert_eq!(actual, expected);
                    assert_eq!(tree, expected_tree);
                    assert_eq!(
                        reader,
                        PacketBitReader {
                            input: &[0],
                            byte_index: usize::from(consumed != 0),
                            current_byte: 0,
                            bits_remaining: if consumed == 0 {
                                0
                            } else {
                                (8 - consumed) as u8
                            },
                            previous_byte_was_ff: false,
                            bits_read: consumed,
                            maximum_work_units: cap,
                            maximum_header_bytes: 1,
                        }
                    );
                }
            }
        }
    }
}

#[test]
fn raw_tag_tree_duplicate_paths_and_64_65_levels_keep_real_state_and_error_order() {
    for levels in [2, 64, 65] {
        let mut tree = TagTree {
            levels: vec![
                TagTreeLevel {
                    offset: 0,
                    width: 1,
                    height: 1
                };
                levels
            ],
            nodes: vec![TagTreeNode {
                low: 0,
                value: u32::MAX,
            }],
        };
        let before = tree.clone();
        let mut reader = packet_reader_prefix_from_input(&[0x80], 1, 1);
        let original_reader = reader;
        let result = tree.decode(0, 0, 1, &mut reader);
        if levels == 65 {
            assert_eq!(
                result,
                Err(packet_reader_error(0, MalformedKind::InvalidTagTree))
            );
            assert_eq!(tree, before);
            assert_eq!(reader, original_reader);
        } else {
            assert_eq!(
                result,
                Ok(TagTreeValue {
                    value: Some(0),
                    is_below_threshold: true
                })
            );
            assert_eq!(tree.levels, before.levels);
            assert_eq!(tree.nodes, [TagTreeNode { low: 0, value: 0 }]);
            assert_eq!(
                (reader.bits_read, reader.byte_index, reader.bits_remaining),
                (1, 1, 7)
            );
        }
    }
    for offset in [0, usize::MAX] {
        let mut tree = TagTree {
            levels: vec![TagTreeLevel {
                offset,
                width: 2,
                height: 2,
            }],
            nodes: vec![],
        };
        let before = tree.clone();
        let mut reader = packet_reader_prefix_from_input(&[], u64::MAX, u64::MAX);
        reader.byte_index = 17;
        let original = reader;
        assert_eq!(
            tree.decode(1, 1, u32::MAX, &mut reader),
            Err(if offset == 0 {
                packet_reader_error(17, MalformedKind::InvalidTagTree)
            } else {
                packet_reader_error(0, MalformedKind::ArithmeticOverflow)
            })
        );
        assert_eq!(tree, before);
        assert_eq!(reader, original);
    }
    let mut empty = TagTree {
        levels: vec![],
        nodes: vec![TagTreeNode { low: 7, value: 0 }],
    };
    let mut reader = packet_reader_prefix_from_input(&[], 0, 0);
    reader.byte_index = 17;
    assert_eq!(
        empty.leaf_count(),
        Err(packet_reader_error(0, MalformedKind::InvalidTagTree))
    );
    assert_eq!(
        empty.decode(0, 0, 1, &mut reader),
        Err(packet_reader_error(0, MalformedKind::InvalidTagTree))
    );
    assert_eq!(empty.nodes[0], TagTreeNode { low: 7, value: 0 });
}

#[test]
fn tag_tree_real_constructor_matches_closed_rectangle_levels_and_cap_first_failure() {
    for width in 1_u32..=9 {
        for height in 1_u32..=9 {
            let top = 32 - (width.max(height) - 1).leading_zeros();
            for cap in [0_u64, 1, 8, 64, 200] {
                let mut levels = Vec::new();
                let mut total = 0_u64;
                let mut failure = None;
                for level in 0..=top {
                    let scale = 1_u64 << level;
                    let w = u64::from(width).div_ceil(scale);
                    let h = u64::from(height).div_ceil(scale);
                    let next = total + w * h;
                    if next > cap {
                        failure = Some(packet_reader_limit(Resource::TagTreeNodes, cap, next));
                        break;
                    }
                    levels.push(TagTreeLevel {
                        offset: total as usize,
                        width: w as u32,
                        height: h as u32,
                    });
                    total = next;
                }
                assert_eq!(
                    tag_tree_from_dimensions(width, height, cap),
                    match failure {
                        Some(error) => Err(error),
                        None => Ok(TagTree {
                            levels,
                            nodes: vec![
                                TagTreeNode {
                                    low: 0,
                                    value: u32::MAX
                                };
                                total as usize
                            ]
                        }),
                    }
                );
            }
        }
    }
    assert_eq!(
        tag_tree_from_dimensions(0, u32::MAX, 0),
        Err(packet_reader_error(0, MalformedKind::InvalidTagTree))
    );
    assert_eq!(
        tag_tree_from_dimensions(u32::MAX, u32::MAX, u64::MAX),
        Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow))
    );
}

#[test]
fn packet_state_getters_and_copy_preserve_all_native_fields_without_header_invariants() {
    assert_eq!(
        code_block_packet_state_new(),
        CodeBlockPacketState {
            included: false,
            zero_bitplanes: None,
            lblock: 3,
            total_passes: 0,
            high_throughput: None,
        }
    );
    for lblock in 0..=u8::MAX {
        for included in [false, true] {
            for zero_bitplanes in [None, Some(0), Some(u16::MAX)] {
                for total_passes in [0, crate::tier1::MAX_TIER1_PASSES, u32::MAX] {
                    for high_throughput in [None, Some(false), Some(true)] {
                        let state = CodeBlockPacketState {
                            included,
                            zero_bitplanes,
                            lblock,
                            total_passes,
                            high_throughput,
                        };
                        let copy = state;
                        assert_eq!(
                            (
                                copy.included(),
                                copy.zero_bitplanes(),
                                copy.lblock(),
                                copy.total_passes(),
                                copy.high_throughput()
                            ),
                            (
                                included,
                                zero_bitplanes,
                                lblock,
                                total_passes,
                                high_throughput
                            )
                        );
                        assert_eq!(copy, state);
                    }
                }
            }
        }
    }
}

#[test]
fn packet_reader_budget_stuffing_and_full_width_words() {
    let mut reader = packet_reader_prefix_from_input(&[0x80], 1, 0);
    assert_eq!(
        reader.read_bit(),
        Err(packet_reader_limit(Resource::WorkUnits, 0, 1))
    );
    assert_eq!(
        reader,
        PacketBitReader {
            input: &[0x80],
            byte_index: 1,
            current_byte: 0x80,
            bits_remaining: 7,
            previous_byte_was_ff: false,
            bits_read: 1,
            maximum_work_units: 0,
            maximum_header_bytes: 1,
        }
    );
    reader.bits_read = u64::MAX;
    let mut expected = reader;
    expected.bits_remaining = 6;
    assert_eq!(
        reader.read_bit(),
        Err(packet_reader_error(1, MalformedKind::ArithmeticOverflow))
    );
    assert_eq!(reader, expected);
    reader.bits_remaining = u8::MAX;
    let before = reader;
    assert_eq!(reader.read_bits(0), Ok(0));
    assert_eq!(reader, before);
    for count in 33..=u8::MAX {
        assert_eq!(
            reader.read_bits(count),
            Err(packet_reader_error(1, MalformedKind::InvalidMarkerLength))
        );
        assert_eq!(reader, before);
    }
    assert_eq!(
        reader.read_bit(),
        Err(packet_reader_error(1, MalformedKind::InvalidBitStuffing))
    );
    assert_eq!(reader, before);
    assert_eq!(
        packet_reader_from_input(&[0, 0], 1, 0),
        Err(packet_reader_limit(Resource::PacketHeaderBytes, 1, 2))
    );
    let mut reader = packet_reader_prefix_from_input(&[0xff, 0x80], 2, 64);
    assert_eq!(reader.read_bit(), Ok(true));
    reader.align_to_byte();
    assert!(reader.previous_byte_was_ff);
    let before = reader;
    assert_eq!(
        reader.read_bit(),
        Err(packet_reader_error(1, MalformedKind::InvalidBitStuffing))
    );
    assert_eq!(reader, before);
    let mut reader = packet_reader_prefix_from_input(&[0xff, 0x7f, 0xff, 0x7f, 0xff], 5, 32);
    assert_eq!(reader.read_bits(32), Ok(u32::MAX));
    assert_eq!(
        (
            reader.byte_index,
            reader.bits_remaining,
            reader.bits_read,
            reader.current_byte,
            reader.previous_byte_was_ff
        ),
        (5, 6, 32, 0xff, true)
    );
}

fn literal_empty_ht_contribution(count: u8, passes: u8) -> CodeBlockContribution {
    CodeBlockContribution {
        first_inclusion: true,
        zero_bitplanes: 0,
        new_passes: passes,
        data_length: 0,
        high_throughput: true,
        segment_count: count,
        segment_passes: [1; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
        segment_lengths: [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
    }
}

fn literal_ht_decoder(bitplanes: u16) -> Tier1CodeBlockDecoder {
    Tier1CodeBlockDecoder::new(
        1,
        1,
        bitplanes,
        SubbandOrientation::Ll,
        Tier1CodingStyle::from_code_block_style(0x40).unwrap(),
    )
    .unwrap()
}

#[test]
fn ht_body_zero_setting_precedes_count_error_but_outer_rolls_back_every_field() {
    let limits = ResourceLimits::default();
    let mut header = literal_empty_ht_contribution(0, 0);
    header.zero_bitplanes = 1;
    let mut staged = literal_ht_decoder(3);
    assert_eq!(staged.maximum_passes(), 7);
    assert_eq!(
        decode_code_block_contribution_body_staged(&mut staged, &header, &[], &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock
        }),
    );
    assert_eq!(staged.maximum_passes(), 4);
    assert_eq!(
        (
            staged.next_pass(),
            staged.decoded_segments(),
            staged.decoded_bytes()
        ),
        (0, 0, 0)
    );
    let mut transactional = literal_ht_decoder(3);
    let before = format!("{transactional:?}");
    assert_eq!(
        decode_code_block_contribution_body(&mut transactional, &header, &[], &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock
        }),
    );
    assert_eq!(format!("{transactional:?}"), before);
}

#[test]
fn ht_body_final_pass_mismatch_keeps_staged_progress_and_rolls_back_outer_decoder() {
    let limits = ResourceLimits::default();
    let mut header = literal_empty_ht_contribution(2, 2);
    header.segment_passes[1] = 2;
    let mut staged = literal_ht_decoder(3);
    assert_eq!(
        decode_code_block_contribution_body_staged(&mut staged, &header, &[], &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock
        }),
    );
    assert_eq!(
        (
            staged.next_pass(),
            staged.decoded_segments(),
            staged.decoded_bytes()
        ),
        (3, 2, 0)
    );
    let mut transactional = literal_ht_decoder(3);
    let before = format!("{transactional:?}");
    assert!(
        decode_code_block_contribution_body(&mut transactional, &header, &[], &limits).is_err()
    );
    assert_eq!(format!("{transactional:?}"), before);
    header.new_passes = 3;
    assert_eq!(
        decode_code_block_contribution_body(&mut transactional, &header, &[], &limits),
        Ok(CodeBlockBodyDecode {
            segments: 2,
            passes: 3,
            bytes: 0
        }),
    );
    assert_eq!(
        (
            transactional.next_pass(),
            transactional.decoded_segments(),
            transactional.decoded_bytes()
        ),
        (3, 2, 0)
    );
    assert_eq!(transactional.plane().signed_coefficient(0, 0).unwrap(), 0);
}

#[test]
fn ht_body_native_count_reaches_physical_header_boundary_without_count_normalization() {
    let limits = ResourceLimits::default();
    let header = literal_empty_ht_contribution(165, 0);
    let mut staged = literal_ht_decoder(56);
    assert_eq!(
        decode_code_block_contribution_body_staged(&mut staged, &header, &[], &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidPacketHeader
        }),
    );
    assert_eq!(
        (
            staged.next_pass(),
            staged.decoded_segments(),
            staged.decoded_bytes()
        ),
        (164, 164, 0)
    );
    let mut transactional = literal_ht_decoder(56);
    let before = format!("{transactional:?}");
    assert_eq!(
        decode_code_block_contribution_body(&mut transactional, &header, &[], &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidPacketHeader
        }),
    );
    assert_eq!(format!("{transactional:?}"), before);
}

#[test]
fn shared_code_block_body_prepare_has_exact_native_admission_and_frame() {
    for force in [false, true] {
        for high_throughput in [false, true] {
            for zero_bitplanes in [0, u16::MAX] {
                for wrong_length in [false, true] {
                    let mut decoder = Tier1CodeBlockDecoder::new(
                        1,
                        1,
                        1,
                        crate::tier1::SubbandOrientation::Ll,
                        Tier1CodingStyle {
                            force_high_throughput: force,
                            ..Tier1CodingStyle::default()
                        },
                    )
                    .unwrap();
                    let before = format!("{decoder:?}");
                    let contribution = CodeBlockContribution {
                        first_inclusion: false,
                        zero_bitplanes,
                        new_passes: u8::MAX,
                        data_length: 1,
                        high_throughput,
                        segment_count: u8::MAX,
                        segment_passes: [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
                        segment_lengths: [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
                    };
                    let body: &[u8] = if wrong_length { &[] } else { &[0xff] };
                    let accepted =
                        !wrong_length && (!force || high_throughput) && zero_bitplanes == 0;
                    assert_eq!(
                        prepare_code_block_contribution_body(&mut decoder, &contribution, body),
                        if accepted {
                            Ok(())
                        } else {
                            Err(packet_invalid_code_block())
                        }
                    );
                    assert_eq!(
                        format!("{decoder:?}"),
                        if accepted {
                            before.replacen("zero_bitplanes: None,", "zero_bitplanes: Some(0),", 1)
                        } else {
                            before
                        }
                    );
                }
            }
        }
    }
}

#[test]
fn mixed_packet_union_routes_literal_bytes_and_keeps_empty_count_distinctions() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0xc0).unwrap();
    for high in [false, true] {
        let mut decoder =
            Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
        let mut header = one_ff_legacy_contribution();
        header.high_throughput = high;
        let body: &[u8] = if high { &[0, 0x63, 0] } else { &[0xff] };
        header.data_length = body.len() as u32;
        header.segment_lengths[0] = header.data_length;
        assert_eq!(
            decode_code_block_contribution_body(&mut decoder, &header, body, &limits),
            Ok(CodeBlockBodyDecode {
                segments: 1,
                passes: 1,
                bytes: header.data_length
            }),
        );
        assert_eq!(
            (
                decoder.next_pass(),
                decoder.decoded_segments(),
                decoder.decoded_bytes()
            ),
            (1, 1, body.len() as u64)
        );
        assert_eq!(
            decoder.plane().signed_coefficient(0, 0).unwrap(),
            if high { -1 } else { 0 }
        );

        let mut decoder =
            Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
        let before = format!("{decoder:?}");
        header.segment_count = 0;
        header.new_passes = 0;
        header.data_length = 0;
        let result = decode_code_block_contribution_body(&mut decoder, &header, &[], &limits);
        if high {
            assert_eq!(result, Err(packet_invalid_code_block()));
            assert_eq!(format!("{decoder:?}"), before);
        } else {
            assert_eq!(
                result,
                Ok(CodeBlockBodyDecode {
                    segments: 0,
                    passes: 0,
                    bytes: 0
                })
            );
            assert_eq!(
                (
                    decoder.next_pass(),
                    decoder.decoded_segments(),
                    decoder.decoded_bytes()
                ),
                (0, 0, 0)
            );
        }
    }
}

#[test]
fn mixed_packet_union_preserves_each_route_late_error_and_full_outer_rollback() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0xc0).unwrap();
    for high in [false, true] {
        let mut header = one_ff_legacy_contribution();
        header.high_throughput = high;
        header.new_passes = 2;
        let body: &[u8] = if high { &[0, 0x63, 0] } else { &[0xff] };
        header.data_length = body.len() as u32;
        header.segment_lengths[0] = header.data_length;
        let mut staged =
            Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
        assert_eq!(
            decode_code_block_contribution_body_staged(&mut staged, &header, body, &limits),
            Err(packet_invalid_code_block())
        );
        assert_eq!(
            (
                staged.next_pass(),
                staged.decoded_segments(),
                staged.decoded_bytes()
            ),
            (1, 1, body.len() as u64)
        );
        assert_eq!(
            staged.plane().signed_coefficient(0, 0).unwrap(),
            if high { -1 } else { 0 }
        );
        let mut decoder =
            Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
        let before = format!("{decoder:?}");
        assert_eq!(
            decode_code_block_contribution_body(&mut decoder, &header, body, &limits),
            Err(packet_invalid_code_block())
        );
        assert_eq!(format!("{decoder:?}"), before);
    }
}

#[test]
fn mixed_packet_union_uses_actual_route_specific_input_budget() {
    let limits = ResourceLimits::default()
        .with_maximum_input_bytes(1)
        .unwrap();
    let style = Tier1CodingStyle::from_code_block_style(0xc0).unwrap();
    for high in [false, true] {
        let mut header = one_ff_legacy_contribution();
        header.high_throughput = high;
        let body: &[u8] = if high { &[0, 0x63, 0] } else { &[0xff, 0] };
        header.data_length = body.len() as u32;
        header.segment_lengths[0] = header.data_length;
        let mut decoder =
            Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
        let before = format!("{decoder:?}");
        let result = decode_code_block_contribution_body(&mut decoder, &header, body, &limits);
        if high {
            assert_eq!(
                result,
                Ok(CodeBlockBodyDecode {
                    segments: 1,
                    passes: 1,
                    bytes: 3
                })
            );
            assert_eq!(decoder.plane().signed_coefficient(0, 0).unwrap(), -1);
        } else {
            assert_eq!(
                result,
                Err(DecodeError::LimitExceeded {
                    resource: Resource::InputBytes,
                    limit: 1,
                    actual: 2,
                })
            );
            assert_eq!(format!("{decoder:?}"), before);
        }
    }
}

fn literal_header_subband() -> PacketSubbandState {
    PacketSubbandState {
        orientation: SubbandOrientation::Ll,
        first_decoder: 0,
        decoder_count: 1,
        code_blocks_across: 1,
        code_blocks_down: 1,
        inclusion_tree: tag_tree_new(1, 1, &ResourceLimits::default()).unwrap(),
        zero_bitplane_tree: tag_tree_new(1, 1, &ResourceLimits::default()).unwrap(),
    }
}

fn literal_precinct_header_context() -> CodeBlockPacketContext {
    CodeBlockPacketContext {
        leaf_x: 0,
        leaf_y: 0,
        layer: 0,
        maximum_zero_bitplanes: 3,
        tier1_style: Tier1CodingStyle::default(),
    }
}

fn literal_packet_precinct() -> PacketPrecinctDecoder {
    PacketPrecinctDecoder {
        component: 0,
        resolution: 0,
        precinct: 0,
        states: vec![code_block_packet_state_new()],
        contexts: vec![literal_precinct_header_context()],
        decoders: vec![one_bit_legacy_decoder(false)],
        subbands: vec![literal_header_subband()],
    }
}

#[test]
fn public_single_boundary_keeps_whole_payload_priority_and_real_partial_header_effects() {
    let base = ResourceLimits::default();
    for (payload, limited, error, included, passes, low) in [
        (
            &[0, 0][..],
            true,
            DecodeError::LimitExceeded {
                resource: Resource::PacketHeaderBytes,
                limit: 1,
                actual: 2,
            },
            false,
            0,
            0,
        ),
        (
            &[0, 0][..],
            false,
            packet_reader_error(1, MalformedKind::TrailingData),
            false,
            0,
            0,
        ),
        (
            &[0x80][..],
            false,
            packet_reader_error(1, MalformedKind::InvalidPacketHeader),
            false,
            0,
            1,
        ),
        (&[0xe1][..], false, packet_invalid_code_block(), true, 1, 0),
    ] {
        let limits = if limited {
            base.with_maximum_packet_header_bytes(1).unwrap()
        } else {
            base
        };
        let mut state = code_block_packet_state_new();
        let mut inclusion = tag_tree_new(1, 1, &base).unwrap();
        let mut zero = tag_tree_new(1, 1, &base).unwrap();
        let mut decoder = one_bit_legacy_decoder(false);
        let before = format!("{decoder:?}");
        assert_eq!(
            decode_single_code_block_packet(
                payload,
                &mut state,
                &mut inclusion,
                &mut zero,
                literal_precinct_header_context(),
                &mut decoder,
                &limits
            ),
            Err(error)
        );
        assert_eq!(
            (
                state.included(),
                state.total_passes(),
                inclusion.nodes[0].low
            ),
            (included, passes, low)
        );
        assert_eq!(format!("{decoder:?}"), before);
        if included {
            assert_eq!(zero.nodes[0].value, 0);
        }
    }
    let mut state = code_block_packet_state_new();
    let mut inclusion = tag_tree_new(1, 1, &base).unwrap();
    let mut zero = tag_tree_new(1, 1, &base).unwrap();
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut context = literal_precinct_header_context();
    context.tier1_style = style;
    let mut decoder = Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
    assert_eq!(
        decode_single_code_block_packet(
            &[0xe3, 0, 0x63, 0],
            &mut state,
            &mut inclusion,
            &mut zero,
            context,
            &mut decoder,
            &base
        ),
        Ok(Some(CodeBlockBodyDecode {
            segments: 1,
            passes: 1,
            bytes: 3
        }))
    );
    assert_eq!(decoder.plane().signed_coefficient(0, 0).unwrap(), -1);
}

#[test]
fn public_multi_boundary_preflights_every_body_then_keeps_prior_real_decoder_commits() {
    let limits = ResourceLimits::default();
    for late in [false, true] {
        let mut bytes = vec![0x55; 9];
        bytes.extend_from_slice(&[0xf8, 0xb1, 0, 0x01, 0xae]);
        if late {
            bytes.extend_from_slice(&[0x01, 0xae]);
        }
        let style = coding_style(false, false);
        let tile = TilePartPayload::uniform_for_packet_decoding(
            0,
            0,
            1,
            1,
            style,
            crate::codestream::RoiShifts::none(),
            &bytes,
        )
        .unwrap();
        let mut states = [code_block_packet_state_new(); 2];
        let mut inclusion = tag_tree_new(2, 1, &limits).unwrap();
        let mut zero = tag_tree_new(2, 1, &limits).unwrap();
        let mut first = literal_precinct_header_context();
        first.maximum_zero_bitplanes = 1;
        let contexts = [first, CodeBlockPacketContext { leaf_x: 1, ..first }];
        let mut decoders = [one_bit_legacy_decoder(false), one_bit_legacy_decoder(late)];
        let before = [format!("{:?}", decoders[0]), format!("{:?}", decoders[1])];
        assert_eq!(
            decode_multi_code_block_packet(
                &tile,
                9,
                PacketCodeBlockExecution {
                    states: &mut states,
                    inclusion_tree: &mut inclusion,
                    zero_bitplane_tree: &mut zero,
                    contexts: &contexts,
                    decoders: &mut decoders,
                },
                &limits
            ),
            Err(if late {
                packet_invalid_code_block()
            } else {
                packet_reader_error(9, MalformedKind::Truncated)
            })
        );
        assert!(states.iter().all(|s| s.included() && s.total_passes() == 1));
        assert_eq!(format!("{:?}", decoders[1]), before[1]);
        if late {
            assert_eq!(
                (
                    decoders[0].next_pass(),
                    decoders[0].decoded_segments(),
                    decoders[0].decoded_bytes()
                ),
                (1, 1, 2)
            );
        } else {
            assert_eq!(format!("{:?}", decoders[0]), before[0]);
        }
    }
}

#[test]
fn public_multi_optional_sop_retains_empty_packet_state_and_budgets() {
    let limits = ResourceLimits::default()
        .with_maximum_packet_header_bytes(1)
        .unwrap();
    for marked in [false, true] {
        let data = if marked {
            vec![0xff, 0x91, 0, 4, 0, 0, 0]
        } else {
            vec![0]
        };
        let tile = TilePartPayload::uniform_for_packet_decoding(
            0,
            0,
            1,
            1,
            coding_style(true, false),
            crate::codestream::RoiShifts::none(),
            &data,
        )
        .unwrap();
        let mut states = [code_block_packet_state_new()];
        let mut inclusion = tag_tree_new(1, 1, &limits).unwrap();
        let mut zero = tag_tree_new(1, 1, &limits).unwrap();
        let contexts = [literal_precinct_header_context()];
        let mut decoders = [one_bit_legacy_decoder(false)];
        let before = format!("{:?}", decoders[0]);
        assert_eq!(
            decode_multi_code_block_packet(
                &tile,
                0,
                PacketCodeBlockExecution {
                    states: &mut states,
                    inclusion_tree: &mut inclusion,
                    zero_bitplane_tree: &mut zero,
                    contexts: &contexts,
                    decoders: &mut decoders,
                },
                &limits,
            ),
            Ok(PacketBodyDecode {
                present: false,
                code_blocks: 1,
                contributions: 0,
                segments: 0,
                passes: 0,
                header_bytes: 1,
                body_bytes: 0,
                bytes_consumed: if marked { 7 } else { 1 },
            }),
        );
        assert_eq!(format!("{:?}", decoders[0]), before);
    }
}

#[test]
fn public_multi_uses_prefix_header_budget_and_ignores_sop_sequence_values() {
    let limits = ResourceLimits::default()
        .with_maximum_packet_header_bytes(1)
        .unwrap();
    for sequence in [[0, 0], [0xff, 0xff], [0x12, 0x35]] {
        let data = [0xff, 0x91, 0, 4, sequence[0], sequence[1], 0, 0xff];
        let tile = TilePartPayload::uniform_for_packet_decoding(
            0,
            0,
            1,
            1,
            coding_style(true, false),
            crate::codestream::RoiShifts::none(),
            &data,
        )
        .unwrap();
        let mut states = [code_block_packet_state_new()];
        let mut inclusion = tag_tree_new(1, 1, &ResourceLimits::default()).unwrap();
        let mut zero = tag_tree_new(1, 1, &ResourceLimits::default()).unwrap();
        let contexts = [literal_precinct_header_context()];
        let mut decoders = [one_bit_legacy_decoder(false)];
        assert_eq!(
            decode_multi_code_block_packet(
                &tile,
                0,
                PacketCodeBlockExecution {
                    states: &mut states,
                    inclusion_tree: &mut inclusion,
                    zero_bitplane_tree: &mut zero,
                    contexts: &contexts,
                    decoders: &mut decoders,
                },
                &limits
            ),
            Ok(PacketBodyDecode {
                present: false,
                code_blocks: 1,
                contributions: 0,
                segments: 0,
                passes: 0,
                header_bytes: 1,
                body_bytes: 0,
                bytes_consumed: 7
            })
        );
    }
}

#[test]
fn real_shared_body_policy_retains_nonzero_local_errors_without_remapping_child_errors() {
    let contribution = one_ff_legacy_contribution();
    let mut cursor = PacketBodyPreflight {
        index: 0,
        end: usize::MAX,
    };
    assert_eq!(
        preflight_packet_body_ranges(&[Some(contribution)], &[], &mut cursor, (71, 29)),
        Err(packet_reader_error(29, MalformedKind::ArithmeticOverflow))
    );
    assert_eq!((cursor.index, cursor.end), (0, usize::MAX));
    let mut execution = PacketBodyExecutionProgress {
        index: 0,
        offset: 0,
        segments: 0,
        passes: 0,
    };
    assert_eq!(
        execute_packet_body_contributions(
            &mut [],
            &[Some(contribution)],
            &[0xff],
            &mut execution,
            (71, 29),
            true,
            &ResourceLimits::default()
        ),
        Err(packet_reader_error(29, MalformedKind::InvalidPacketHeader))
    );
    let mut decoder = [one_bit_legacy_decoder(true)];
    let before = format!("{:?}", decoder[0]);
    assert_eq!(
        execute_packet_body_contributions(
            &mut decoder,
            &[Some(contribution)],
            &[0xff],
            &mut execution,
            (71, 29),
            true,
            &ResourceLimits::default()
        ),
        Err(packet_invalid_code_block())
    );
    assert_eq!(format!("{:?}", decoder[0]), before);
}

#[test]
fn actual_multi_header_slot_commits_raw_owner_state_before_count_and_storage_rejections() {
    let limits = ResourceLimits::default();
    for overflow in [false, true] {
        let mut states = [code_block_packet_state_new()];
        let mut inclusion = tag_tree_new(1, 1, &limits).unwrap();
        let mut zero = tag_tree_new(1, 1, &limits).unwrap();
        let contexts = [literal_precinct_header_context()];
        let mut reader = packet_reader_prefix(&[0xc2], &limits);
        let mut contributions = if overflow { vec![None] } else { Vec::new() };
        let mut progress = MultiHeaderProgress {
            index: 0,
            count: if overflow { u32::MAX } else { 0 },
        };
        assert_eq!(
            read_multi_packet_header_slot(
                &mut states,
                &mut inclusion,
                &mut zero,
                MultiHeaderParameters {
                    contexts: &contexts,
                    offset: 23
                },
                &mut contributions,
                &mut reader,
                &mut progress
            ),
            Err(packet_reader_error(
                23,
                if overflow {
                    MalformedKind::ArithmeticOverflow
                } else {
                    MalformedKind::InvalidPacketHeader
                }
            ))
        );
        assert_eq!((states[0].included(), states[0].total_passes()), (true, 1));
        assert_eq!(
            (reader.byte_index, reader.bits_remaining, reader.bits_read),
            (1, 1, 7)
        );
        assert_eq!(
            (progress.index, progress.count),
            (0, if overflow { u32::MAX } else { 1 })
        );
        assert!(contributions.iter().all(Option::is_none));
        assert_eq!(inclusion.nodes[0], TagTreeNode { low: 0, value: 0 });
        assert_eq!(zero.nodes[0], TagTreeNode { low: 0, value: 0 });
    }
}

#[test]
fn actual_jpip_outer_restores_all_raw_fields_and_clone_preserves_unused_tree_words() {
    let limits = ResourceLimits::default();
    let template = literal_progression_tile(&[], 1, 0, 0, 1);
    for empty_states in [false, true] {
        let mut precinct = literal_ht_progression_precinct(0);
        precinct.contexts[0].layer = 7;
        precinct.subbands[0].inclusion_tree.nodes.push(TagTreeNode {
            low: 19,
            value: u32::MAX,
        });
        precinct.subbands[0]
            .zero_bitplane_tree
            .nodes
            .push(TagTreeNode {
                low: u32::MAX,
                value: 23,
            });
        if empty_states {
            precinct.states.clear();
        }
        let before = exact_packet_precinct_snapshot(&precinct);
        let data: &[u8] = if empty_states { &[] } else { &[0xe3] };
        assert!(
            decode_jpip_precinct_packet(&template, data, 0, 0, &mut precinct, &limits).is_err()
        );
        assert_eq!(exact_packet_precinct_snapshot(&precinct), before);
        assert_eq!(
            precinct.subbands[0].inclusion_tree.nodes[1],
            TagTreeNode {
                low: 19,
                value: u32::MAX
            }
        );
        assert_eq!(
            precinct.subbands[0].zero_bitplane_tree.nodes[1],
            TagTreeNode {
                low: u32::MAX,
                value: 23
            }
        );
    }
    let mut inner = literal_ht_progression_precinct(0);
    inner.states.clear();
    inner.contexts[0].layer = 7;
    assert_eq!(
        decode_jpip_precinct_packet_inner(&template, &[], 0, 0, &mut inner, &limits),
        Err(invalid_packet_header())
    );
    assert_eq!(inner.contexts[0].layer, 0);
}

fn literal_ht_progression_precinct(resolution: u8) -> PacketPrecinctDecoder {
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut precinct = literal_packet_precinct();
    precinct.resolution = resolution;
    precinct.contexts[0].tier1_style = style;
    precinct.decoders[0] =
        Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
    precinct
}

fn literal_progression_tile(
    data: &[u8],
    layers: u16,
    levels: u8,
    index: u8,
    count: u8,
) -> TilePartPayload<'_> {
    let mut style = coding_style(false, false);
    style.layers = layers;
    style.decomposition_levels = levels;
    style.code_block_style = 0x40;
    TilePartPayload::uniform_for_packet_decoding(
        7,
        index,
        count,
        1,
        style,
        crate::codestream::RoiShifts::none(),
        data,
    )
    .unwrap()
}

#[test]
fn full_selected_progression_derives_literal_headers_and_skips_only_higher_resolution_coefficients()
{
    let limits = ResourceLimits::default();
    let grid =
        packet_grid_new_with_component_resolutions(1, 1, vec![2], vec![1, 1], &limits).unwrap();
    let parts = [literal_progression_tile(
        &[0xe3, 0, 0x63, 0, 0xe3, 0, 0x63, 0],
        1,
        1,
        0,
        1,
    )];
    let mut precincts = [
        literal_ht_progression_precinct(0),
        literal_ht_progression_precinct(1),
    ];
    assert_eq!(
        decode_progression_tile_packets_selected(
            &parts,
            &grid,
            &mut precincts,
            Some(&[1]),
            &limits
        ),
        Ok(TilePacketDecode {
            tile_index: 7,
            tile_parts: 1,
            packets: 2,
            present_packets: 2,
            contributions: 2,
            segments: 1,
            passes: 1,
            packet_header_bytes: 2,
            packet_body_bytes: 6,
            payload_bytes: 8
        })
    );
    assert_eq!(
        precincts[0].decoders[0]
            .plane()
            .signed_coefficient(0, 0)
            .unwrap(),
        -1
    );
    assert_eq!(
        precincts[1].decoders[0]
            .plane()
            .signed_coefficient(0, 0)
            .unwrap(),
        0
    );
    for precinct in &precincts {
        assert!(precinct.states[0].included());
        assert_eq!(precinct.states[0].total_passes(), 1);
        assert_eq!(precinct.states[0].high_throughput(), Some(true));
    }
}

#[test]
fn full_progression_restarts_actual_tile_iterators_and_retains_real_output_on_late_trailing_data() {
    let limits = ResourceLimits::default();
    let grid = packet_grid_new_with_component_resolutions(2, 1, vec![1], vec![1], &limits).unwrap();
    for trailing in [false, true] {
        let second: &[u8] = if trailing { &[0, 0x55] } else { &[0] };
        let parts = [
            literal_progression_tile(&[0xe3, 0, 0x63, 0], 2, 0, 0, 2),
            literal_progression_tile(second, 2, 0, 1, 2),
        ];
        let mut precincts = [literal_ht_progression_precinct(0)];
        assert_eq!(
            decode_progression_tile_packets(&parts, &grid, &mut precincts, &limits),
            if trailing {
                Err(packet_reader_error(1, MalformedKind::TrailingData))
            } else {
                Ok(TilePacketDecode {
                    tile_index: 7,
                    tile_parts: 2,
                    packets: 2,
                    present_packets: 1,
                    contributions: 1,
                    segments: 1,
                    passes: 1,
                    packet_header_bytes: 2,
                    packet_body_bytes: 3,
                    payload_bytes: 5,
                })
            }
        );
        assert_eq!(
            precincts[0].decoders[0]
                .plane()
                .signed_coefficient(0, 0)
                .unwrap(),
            -1
        );
        assert_eq!(precincts[0].contexts[0].layer, 1);
        assert_eq!(precincts[0].states[0].total_passes(), 1);
    }
}

#[test]
fn actual_progression_work_guard_follows_real_next_and_restart_duplicate_effects() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(3)
        .unwrap();
    let grid = packet_grid_new_with_component_resolutions(2, 1, vec![1], vec![1], &limits).unwrap();
    let parts = [
        literal_progression_tile(&[0], 2, 0, 0, 2),
        literal_progression_tile(&[0], 2, 0, 1, 2),
    ];
    let mut precincts = [literal_ht_progression_precinct(0)];
    let input = prepare_progression_tile_input(&parts, &grid, &precincts, None, &limits).unwrap();
    let params = ProgressionTileParameters {
        tile_parts: &parts,
        grid: &grid,
        input: &input,
        selection: None,
        limits: &limits,
    };
    let mut progress = progression_tile_progress_new(&params).unwrap();
    assert_eq!(
        run_progression_tile_packets(&params, &mut precincts, &mut progress),
        Err(packet_reader_error(
            0,
            MalformedKind::InvalidProgressionOrderChange
        ))
    );
    assert_eq!(
        (
            progress.remaining_packets,
            progress.packets,
            progress.current_tile_part,
            progress.offset,
            progress.packed_offset
        ),
        (0, 1, 1, 0, 0)
    );
    assert_eq!(progress.seen, vec![true, false]);
    assert_eq!(progress.iterator.emitted(), 2);
    assert_eq!(precincts[0].contexts[0].layer, 0);
    assert!(!precincts[0].states[0].included());
}

#[test]
fn actual_progression_accounting_keeps_every_ordered_overflow_and_new_offset_error() {
    let limits = ResourceLimits::default();
    let grid = raw_iterator_grid();
    let parts = [literal_progression_tile(&[0], 1, 0, 0, 1)];
    let precincts = [literal_ht_progression_precinct(0)];
    let input = prepare_progression_tile_input(&parts, &grid, &precincts, None, &limits).unwrap();
    let params = ProgressionTileParameters {
        tile_parts: &parts,
        grid: &grid,
        input: &input,
        selection: None,
        limits: &limits,
    };
    let decoded = PacketBodyDecode {
        present: true,
        code_blocks: 1,
        contributions: 1,
        segments: 1,
        passes: 1,
        header_bytes: 1,
        body_bytes: 1,
        bytes_consumed: 2,
    };
    for field in 0..7 {
        let mut progress = progression_tile_progress_new(&params).unwrap();
        match field {
            0 => progress.packets = u64::MAX,
            1 => progress.present_packets = u64::MAX,
            2 => progress.contributions = u64::MAX,
            3 => progress.segments = u64::MAX,
            4 => progress.passes = u64::MAX,
            5 => progress.packet_header_bytes = u64::MAX,
            6 => progress.packet_body_bytes = u64::MAX,
            _ => unreachable!(),
        }
        assert_eq!(
            account_progression_packet(&mut progress, decoded, 2, 0, Some(2), 0),
            Err(packet_arithmetic_overflow())
        );
        assert_eq!(progress.offset, 2);
        assert_eq!(progress.seen, vec![field != 0]);
        let actual = [
            progress.packets,
            progress.present_packets,
            progress.contributions,
            progress.segments,
            progress.passes,
            progress.packet_header_bytes,
            progress.packet_body_bytes,
        ];
        for (index, value) in actual.into_iter().enumerate() {
            assert_eq!(
                value,
                if index == field {
                    u64::MAX
                } else {
                    u64::from(index < field)
                }
            );
        }
    }
    let mut progress = progression_tile_progress_new(&params).unwrap();
    progress.offset = 3;
    progress.packed_offset = usize::MAX;
    assert_eq!(
        account_progression_packet(&mut progress, decoded, 2, 1, Some(2), 0),
        Err(packet_reader_error(5, MalformedKind::ArithmeticOverflow))
    );
    assert_eq!(
        (progress.offset, progress.packed_offset, progress.packets),
        (5, usize::MAX, 0)
    );
    assert_eq!(progress.seen, vec![false]);
}

#[test]
fn full_progression_uses_real_ppt_reassembly_and_plt_iteration_without_tile_body_bytes() {
    fn segment(stream: &mut Vec<u8>, marker: u16, payload: &[u8]) {
        stream.extend_from_slice(&marker.to_be_bytes());
        stream.extend_from_slice(&u16::try_from(payload.len() + 2).unwrap().to_be_bytes());
        stream.extend_from_slice(payload);
    }
    let mut stream = vec![0xff, 0x4f];
    let mut siz = vec![0, 0];
    for value in [1_u32, 1, 0, 0, 1, 1, 0, 0] {
        siz.extend_from_slice(&value.to_be_bytes());
    }
    siz.extend_from_slice(&[0, 1, 7, 1, 1]);
    segment(&mut stream, 0xff51, &siz);
    segment(&mut stream, 0xff52, &[0, 0, 0, 1, 0, 0, 0, 0, 0, 1]);
    segment(&mut stream, 0xff5c, &[0x20, 0]);
    segment(&mut stream, 0xff90, &[0, 0, 0, 0, 0, 26, 0, 1]);
    segment(&mut stream, 0xff58, &[0, 1]);
    segment(&mut stream, 0xff61, &[0, 0]);
    stream.extend_from_slice(&[0xff, 0x93, 0xff, 0xd9]);
    let limits = ResourceLimits::default();
    let layout = crate::codestream::parse_layout(&stream, &limits).unwrap();
    assert_eq!(layout.tile_parts.len(), 1);
    assert!(layout.tile_parts[0].data.is_empty());
    assert!(layout.tile_parts[0].packed_packet_headers.is_present());
    assert!(layout.tile_parts[0].packet_lengths.is_present());
    let grid = packet_grid_new_with_component_resolutions(1, 1, vec![1], vec![1], &limits).unwrap();
    let mut precincts = [literal_packet_precinct()];
    assert_eq!(
        decode_progression_tile_packets(&layout.tile_parts, &grid, &mut precincts, &limits),
        Ok(TilePacketDecode {
            tile_index: 0,
            tile_parts: 1,
            packets: 1,
            present_packets: 0,
            contributions: 0,
            segments: 0,
            passes: 0,
            packet_header_bytes: 1,
            packet_body_bytes: 0,
            payload_bytes: 0
        })
    );
    assert!(!precincts[0].states[0].included());
    assert_eq!(
        precincts[0].decoders[0]
            .plane()
            .signed_coefficient(0, 0)
            .unwrap(),
        0
    );
    let template = &layout.tile_parts[0];
    let template_before = format!("{template:?}");
    let mut inline = literal_packet_precinct();
    inline.contexts[0].layer = 9;
    let decoder_before = format!("{:?}", inline.decoders[0]);
    assert_eq!(
        decode_jpip_precinct_packet(template, &[0xe1, 0xff], 0, 0, &mut inline, &limits),
        Ok(2)
    );
    assert!(inline.states[0].included());
    assert_eq!(
        (inline.states[0].total_passes(), inline.contexts[0].layer),
        (1, 0)
    );
    assert_eq!(format!("{:?}", inline.decoders[0]), decoder_before);
    assert_eq!(format!("{template:?}"), template_before);
}

fn raw_iterator_grid() -> PacketGrid {
    PacketGrid {
        layers: 1,
        components: 1,
        resolutions: 1,
        component_resolutions: vec![1],
        maximum_precincts_per_resolution: 1,
        precinct_counts: vec![1],
        precinct_offsets: vec![0, 1],
        candidate_count: 1,
        packet_count: 1,
    }
}

#[test]
fn raw_grid_lookup_retains_physical_zero_and_offset_error_priority() {
    let invalid = packet_reader_error(0, MalformedKind::InvalidCodingStyle);
    let mut grid = raw_iterator_grid();
    grid.component_resolutions.clear();
    grid.precinct_counts.clear();
    grid.precinct_offsets.clear();
    assert_eq!(grid.precinct_count(0, 0), Err(invalid));
    grid.component_resolutions.push(0);
    assert_eq!(grid.precinct_count(0, 0), Ok(0));
    assert_eq!(grid.precinct_index(0, 0, 0), Err(invalid));
    grid.component_resolutions[0] = 1;
    assert_eq!(grid.precinct_count(0, 0), Err(invalid));
    grid.precinct_counts.push(2);
    assert_eq!(grid.precinct_index(0, 0, 1), Err(invalid));
    grid.precinct_offsets.push(usize::MAX);
    assert_eq!(grid.precinct_index(0, 0, 0), Ok(usize::MAX));
    assert_eq!(
        grid.precinct_index(0, 0, 1),
        Err(packet_arithmetic_overflow())
    );
    grid.layers = 0;
    assert_eq!(
        grid.total_precinct_count(),
        Err(packet_arithmetic_overflow())
    );
    assert_eq!(grid.selected_packet_count(&[1]), Ok(0));
}

#[test]
fn actual_grid_factory_keeps_full_offsets_and_candidate_work_under_selected_caps() {
    let limits = ResourceLimits::default()
        .with_maximum_packets(10)
        .unwrap()
        .with_maximum_work_units(32)
        .unwrap();
    let grid = packet_grid_new_with_selected_resolutions(
        2,
        2,
        vec![1, 2],
        vec![2, 0, 3, 4],
        Some(&[1, 1]),
        &limits,
    )
    .unwrap();
    assert_eq!((grid.layers, grid.components, grid.resolutions), (2, 2, 2));
    assert_eq!(grid.component_resolutions, vec![1, 2]);
    assert_eq!(grid.precinct_counts, vec![2, 0, 3, 4]);
    assert_eq!(grid.precinct_offsets, vec![0, 2, 2, 5, 9]);
    assert_eq!(
        (
            grid.maximum_precincts_per_resolution,
            grid.candidate_count,
            grid.packet_count
        ),
        (4, 32, 18)
    );
    assert_eq!(grid.selected_packet_count(&[1, 1]), Ok(10));
    let work_limited = limits.with_maximum_work_units(31).unwrap();
    assert!(matches!(
        packet_grid_new_with_selected_resolutions(
            2,
            2,
            vec![1, 2],
            vec![2, 0, 3, 4],
            Some(&[1, 1]),
            &work_limited,
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 31,
            actual: 32
        })
    ));
    assert!(matches!(
        packet_grid_new_with_selected_resolutions(
            2,
            2,
            vec![1, 2],
            vec![2, 1, 3, 4],
            Some(&[1, 1]),
            &work_limited,
        ),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodingStyle
        })
    ));
    assert!(matches!(
        packet_grid_new_with_selected_resolutions(
            2,
            2,
            vec![1, 2],
            vec![2, 0, 3, 4],
            None,
            &limits,
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: 10,
            actual: 18
        })
    ));
}

#[test]
fn raw_packet_iterator_retains_advanced_candidate_and_late_emitted_errors() {
    for case in 0..5 {
        let mut grid = raw_iterator_grid();
        match case {
            0 => grid.maximum_precincts_per_resolution = 0,
            1 => grid.component_resolutions.clear(),
            2 => grid.packet_count = 0,
            3 => {}
            4 => {
                grid.components = 2;
                grid.candidate_count = 2;
                grid.component_resolutions = vec![1, 1];
                grid.precinct_counts = vec![0];
            }
            _ => unreachable!(),
        }
        let before = grid.clone();
        let mut iterator = packet_iterator_new(&grid, ProgressionOrder::Lrcp);
        if case == 3 {
            iterator.emitted = u64::MAX;
        }
        assert_eq!(
            iterator.next_packet(),
            Err(if case == 2 || case == 3 {
                packet_arithmetic_overflow()
            } else {
                packet_reader_error(0, MalformedKind::InvalidCodingStyle)
            })
        );
        assert_eq!(iterator.candidate_index, if case == 4 { 2 } else { 1 });
        assert_eq!(
            iterator.emitted,
            match case {
                2 => 1,
                3 => u64::MAX,
                _ => 0,
            }
        );
        assert_eq!(*iterator.grid, before);
    }
    let grid = raw_iterator_grid();
    let mut iterator = packet_iterator_new(&grid, ProgressionOrder::Cprl);
    iterator.candidate_index = u64::MAX;
    iterator.emitted = u64::MAX;
    assert_eq!(iterator.next_packet(), Ok(None));
    assert_eq!(
        (iterator.candidate_index, iterator.emitted),
        (u64::MAX, u64::MAX)
    );
}

#[test]
fn raw_poc_inverted_component_count_and_decode_keep_distinct_native_policies() {
    let grid = raw_iterator_grid();
    let mut record = ProgressionChange {
        resolution_start: 0,
        component_start: 2,
        layer_end: u16::MAX,
        resolution_end: u8::MAX,
        component_end: 1,
        progression_order: ProgressionOrder::Lrcp,
    };
    assert_eq!(window_candidate_count(&grid, record), Ok(0));
    assert_eq!(
        decode_window_candidate(&grid, record, 0),
        Err(packet_reader_error(
            0,
            MalformedKind::InvalidProgressionOrderChange
        ))
    );
    record.component_end = 3;
    record.resolution_start = 2;
    record.resolution_end = 1;
    assert_eq!(
        window_candidate_count(&grid, record),
        Err(packet_reader_error(
            0,
            MalformedKind::InvalidProgressionOrderChange
        ))
    );
    assert_eq!(
        decode_window_candidate(&grid, record, 0),
        Err(packet_reader_error(
            0,
            MalformedKind::InvalidProgressionOrderChange
        ))
    );
}

fn literal_progression_window() -> ProgressionChange {
    ProgressionChange {
        resolution_start: 0,
        component_start: 0,
        layer_end: 1,
        resolution_end: 1,
        component_end: 1,
        progression_order: ProgressionOrder::Lrcp,
    }
}

#[test]
fn raw_progression_default_error_commits_nested_state_without_syncing_outer_emitted() {
    let mut grid = raw_iterator_grid();
    grid.packet_count = 0;
    let changes = ProgressionChanges::none();
    let mut iterator = progression_packet_iterator_new(
        &grid,
        ProgressionOrder::Lrcp,
        &changes,
        &ResourceLimits::default(),
    )
    .unwrap();
    iterator.emitted = 17;
    assert_eq!(iterator.next_packet(), Err(packet_arithmetic_overflow()));
    assert_eq!(iterator.emitted, 17);
    let default = iterator.default.as_ref().unwrap();
    assert_eq!((default.candidate_index, default.emitted), (1, 1));
    assert_eq!(
        (
            iterator.window_index,
            iterator.window_candidate,
            iterator.window_candidates
        ),
        (0, 0, 0)
    );
}

#[test]
fn raw_progression_window_advance_retains_partial_cursor_before_next_window_rejection() {
    let grid = raw_iterator_grid();
    let good = literal_progression_window();
    let bad = ProgressionChange {
        resolution_start: 2,
        ..good
    };
    let changes = ProgressionChanges::from_records(vec![good, bad]);
    let mut iterator = ProgressionPacketIterator {
        grid: &grid,
        changes: &changes,
        default: None,
        window_index: 0,
        window_candidate: 5,
        window_candidates: 5,
        emitted: 0,
    };
    assert_eq!(
        iterator.next_packet(),
        Err(packet_reader_error(
            0,
            MalformedKind::InvalidProgressionOrderChange
        ))
    );
    assert_eq!(
        (
            iterator.window_index,
            iterator.window_candidate,
            iterator.window_candidates,
            iterator.emitted
        ),
        (1, 0, 5, 0)
    );
    let empty = ProgressionChanges::none();
    iterator.changes = &empty;
    iterator.window_index = 3;
    iterator.window_candidate = 0;
    let record = literal_progression_window();
    assert_eq!(
        iterator.candidate_step(record),
        Err(packet_reader_error(
            0,
            MalformedKind::InvalidProgressionOrderChange
        ))
    );
    assert_eq!(
        (
            iterator.window_index,
            iterator.window_candidate,
            iterator.window_candidates,
            iterator.emitted
        ),
        (3, 1, 5, 0)
    );
}

#[test]
fn actual_progression_constructor_charges_duplicate_windows_and_next_suppresses_only_prior_membership()
 {
    let grid = raw_iterator_grid();
    let record = literal_progression_window();
    let changes = ProgressionChanges::from_records(vec![record, record]);
    let limited = ResourceLimits::default()
        .with_maximum_work_units(1)
        .unwrap();
    assert!(matches!(
        progression_packet_iterator_new(&grid, ProgressionOrder::Cprl, &changes, &limited),
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: 1,
            actual: 2
        })
    ));
    let limits = ResourceLimits::default()
        .with_maximum_work_units(2)
        .unwrap();
    let mut iterator =
        progression_packet_iterator_new(&grid, ProgressionOrder::Cprl, &changes, &limits).unwrap();
    assert_eq!(
        iterator.next_packet(),
        Ok(Some(PacketCoordinate {
            layer: 0,
            resolution: 0,
            component: 0,
            precinct: 0
        }))
    );
    assert_eq!(
        (
            iterator.window_index,
            iterator.window_candidate,
            iterator.window_candidates,
            iterator.emitted
        ),
        (0, 1, 1, 1)
    );
    assert_eq!(iterator.next_packet(), Ok(None));
    assert_eq!(
        (
            iterator.window_index,
            iterator.window_candidate,
            iterator.window_candidates,
            iterator.emitted
        ),
        (2, 0, 0, 1)
    );
    assert_eq!(iterator.next_packet(), Ok(None));
}

fn literal_payload_parameters() -> PrecinctPayloadParameters {
    PrecinctPayloadParameters {
        error_offset: 21,
        packed_offset: 0,
        expected_packet_length: None,
        expected_sop_sequence: 0x1234,
        style: Tier1CodingStyle::default(),
        sop: false,
        eph: false,
        packed: false,
        decode_tier1: true,
    }
}

#[test]
fn checked_packet_header_finish_preserves_bits_and_byte_budget_order() {
    let mut cases = 0;
    for byte in 0_u8..=u8::MAX {
        for tail in 0_u8..=u8::MAX {
            for cap in [1_u64, 2] {
                let limits = ResourceLimits::default()
                    .with_maximum_packet_header_bytes(cap)
                    .unwrap()
                    .with_maximum_work_units(8)
                    .unwrap();
                let data = [byte, tail];
                let mut reader = super::bit_reader::packet_reader_prefix(&data, &limits);
                assert_eq!(reader.read_bits(8), Ok(u32::from(byte)));
                let before = (
                    reader.byte_index,
                    reader.current_byte,
                    reader.bits_remaining,
                    reader.previous_byte_was_ff,
                    reader.bits_read,
                );
                let expected = if byte == 0xff && cap == 1 {
                    Err(packet_reader_limit(Resource::PacketHeaderBytes, 1, 2))
                } else if byte == 0xff && tail & 0x80 != 0 {
                    Err(packet_reader_error(1, MalformedKind::InvalidBitStuffing))
                } else {
                    Ok(())
                };
                assert_eq!(
                    reader.finish_packet_header(),
                    expected,
                    "byte={byte:#x} tail={tail:#x} cap={cap}",
                );
                if expected.is_err() {
                    assert_eq!(
                        (
                            reader.byte_index,
                            reader.current_byte,
                            reader.bits_remaining,
                            reader.previous_byte_was_ff,
                            reader.bits_read
                        ),
                        before,
                    );
                } else {
                    assert_eq!(reader.bytes_consumed(), if byte == 0xff { 2 } else { 1 });
                    assert_eq!(reader.current_byte, if byte == 0xff { tail } else { byte });
                    assert!(reader.is_byte_aligned());
                    assert!(!reader.previous_byte_was_ff);
                    assert_eq!(reader.bits_read(), 8);
                }
                assert_eq!(reader.input, data);
                assert_eq!(reader.maximum_header_bytes, cap);
                assert_eq!(reader.maximum_work_units, 8);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 131_072);
    for (cap, expected) in [
        (1, packet_reader_limit(Resource::PacketHeaderBytes, 1, 2)),
        (2, packet_reader_error(1, MalformedKind::Truncated)),
    ] {
        let limits = ResourceLimits::default()
            .with_maximum_packet_header_bytes(cap)
            .unwrap();
        let mut reader = super::bit_reader::packet_reader_prefix(&[0xff], &limits);
        assert_eq!(reader.read_bits(8), Ok(255));
        assert_eq!(reader.finish_packet_header(), Err(expected));
        assert_eq!(reader.bytes_consumed(), 1);
        assert_eq!(reader.bits_read(), 8);
    }
}

#[test]
fn sarah_dev_ea51acda28_terminal_ff_header_counts_stuffing_before_body() {
    let limits = ResourceLimits::default()
        .with_maximum_packet_header_bytes(4)
        .unwrap();
    let mut cases = 0;
    for sop in [false, true] {
        for marked in [false, true] {
            if marked && !sop {
                continue;
            }
            for eph in [false, true] {
                for packed in [false, true] {
                    let mut precinct = literal_packet_precinct();
                    precinct.contexts[0].maximum_zero_bitplanes = 8;
                    precinct.decoders[0] = Tier1CodeBlockDecoder::new(
                        1,
                        1,
                        8,
                        SubbandOrientation::Ll,
                        Tier1CodingStyle::default(),
                    )
                    .unwrap();
                    let before = format!("{:?}", precinct.decoders[0]);
                    let mut parameters = literal_payload_parameters();
                    parameters.sop = sop;
                    parameters.eph = eph;
                    parameters.packed = packed;
                    parameters.packed_offset = 1;
                    parameters.decode_tier1 = false;
                    parameters.expected_packet_length = None;
                    let mut header = vec![0xc0, 0xbe, 0xff, 0];
                    if eph {
                        header.extend_from_slice(&[0xff, 0x92]);
                    }
                    let mut data = Vec::new();
                    if marked {
                        data.extend_from_slice(&[0xff, 0x91, 0, 4, 0x12, 0x34]);
                    }
                    if !packed {
                        data.extend_from_slice(&header);
                    }
                    data.extend_from_slice(&[0xff; 255]);
                    let mut packed_headers = vec![0xaa];
                    if packed {
                        packed_headers.extend_from_slice(&header);
                    }
                    let (decoded, tile_bytes, packed_bytes) = decode_precinct_packet_payload(
                        &data,
                        &packed_headers,
                        parameters,
                        &mut precinct,
                        &limits,
                    )
                    .unwrap_or_else(|error| {
                        panic!("sop={sop} marked={marked} eph={eph} packed={packed}: {error:?}")
                    });
                    assert_eq!(decoded.header_bytes, 4);
                    assert_eq!(decoded.body_bytes, 255);
                    assert_eq!(
                        decoded.bytes_consumed,
                        259 + u32::from(marked) * 6 + u32::from(eph) * 2
                    );
                    assert_eq!(tile_bytes, data.len());
                    assert_eq!(packed_bytes, if packed { header.len() } else { 0 });
                    assert_eq!(precinct.states[0].zero_bitplanes(), Some(6));
                    assert_eq!(precinct.states[0].lblock, 8);
                    assert_eq!(precinct.states[0].total_passes(), 1);
                    assert_eq!(format!("{:?}", precinct.decoders[0]), before);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 12);
}

#[test]
fn precinct_payload_prefix_checks_actual_markers_before_packed_ranges_and_budgets() {
    let limits = ResourceLimits::default()
        .with_maximum_work_units(1)
        .unwrap();
    let mut parameters = literal_payload_parameters();
    parameters.sop = true;
    parameters.packed = true;
    parameters.packed_offset = usize::MAX;
    for (data, kind, expected_offset) in [
        (&[][..], MalformedKind::Truncated, usize::MAX),
        (&[0xff, 0x91, 0][..], MalformedKind::Truncated, 21),
        (&[0, 0x91, 0, 4][..], MalformedKind::Truncated, usize::MAX),
        (&[0xff, 0x91, 0, 4][..], MalformedKind::Truncated, 21),
        (
            &[0xff, 0x90, 0, 4, 0, 0][..],
            MalformedKind::Truncated,
            usize::MAX,
        ),
        (
            &[0xff, 0x91, 0, 5, 0, 0][..],
            MalformedKind::InvalidPacketHeader,
            0,
        ),
        (
            &[0xff, 0x91, 0, 4, 0x12, 0x35][..],
            MalformedKind::InvalidPacketHeader,
            0,
        ),
    ] {
        assert_eq!(
            decode_precinct_packet_payload_prefix(data, &[], parameters, &limits).err(),
            Some(packet_reader_error(expected_offset, kind)),
            "data={data:?}",
        );
    }
    let mut inline = parameters;
    inline.packed = false;
    assert_eq!(
        decode_precinct_packet_payload_prefix(&[0xff, 0x90, 0, 4, 0, 0], &[], inline, &limits,)
            .err(),
        Some(packet_reader_error(0, MalformedKind::InvalidPacketHeader)),
    );
    let data = [0xff, 0x91, 0, 4, 0x12, 0x34, 0x80];
    assert!(matches!(
        decode_precinct_packet_payload_prefix(&data, &[], parameters, &limits),
        Err(DecodeError::MalformedInput { offset, kind: MalformedKind::Truncated })
            if offset == usize::MAX as u64
    ));
    for packed in [false, true] {
        parameters.packed = packed;
        parameters.packed_offset = 1;
        let prefix =
            decode_precinct_packet_payload_prefix(&data, &[0xaa, 0x80], parameters, &limits)
                .unwrap();
        assert!(prefix.present);
        assert_eq!(prefix.sop_bytes, 6);
        assert_eq!(prefix.packet_data, &[0x80]);
        assert_eq!(prefix.reader.input, &[0x80]);
        assert_eq!(
            (
                prefix.reader.byte_index,
                prefix.reader.bits_remaining,
                prefix.reader.current_byte,
                prefix.reader.previous_byte_was_ff,
                prefix.reader.bits_read,
            ),
            (1, 7, 0x80, false, 1)
        );
    }
}

#[test]
fn precinct_payload_literal_inline_and_packed_streams_account_for_markers_and_real_coefficients() {
    let limits = ResourceLimits::default();
    for packed in [false, true] {
        for decode_tier1 in [false, true] {
            let mut precinct = literal_packet_precinct();
            let mut parameters = literal_payload_parameters();
            parameters.packed = packed;
            parameters.sop = true;
            parameters.eph = true;
            parameters.packed_offset = 1;
            parameters.expected_packet_length = Some(10);
            parameters.decode_tier1 = decode_tier1;
            let inline = [0xff, 0x91, 0, 4, 0x12, 0x34, 0xe1, 0xff, 0x92, 0xff];
            let packed_body = [0xff, 0x91, 0, 4, 0x12, 0x34, 0xff];
            let data: &[u8] = if packed { &packed_body } else { &inline };
            assert_eq!(
                decode_precinct_packet_payload(
                    data,
                    &[0xaa, 0xe1, 0xff, 0x92],
                    parameters,
                    &mut precinct,
                    &limits,
                ),
                Ok((
                    PacketBodyDecode {
                        present: true,
                        code_blocks: 1,
                        contributions: 1,
                        segments: u32::from(decode_tier1),
                        passes: u32::from(decode_tier1),
                        header_bytes: 1,
                        body_bytes: 1,
                        bytes_consumed: 10,
                    },
                    if packed { 7 } else { 10 },
                    if packed { 3 } else { 0 },
                ))
            );
            assert_eq!(precinct.states[0].total_passes(), 1);
            assert!(precinct.states[0].included());
            assert_eq!(
                precinct.decoders[0]
                    .plane()
                    .signed_coefficient(0, 0)
                    .unwrap(),
                0
            );
            assert_eq!(precinct.decoders[0].next_pass(), u32::from(decode_tier1));
            assert_eq!(
                precinct.decoders[0].decoded_segments(),
                u32::from(decode_tier1)
            );
        }
    }
}

#[test]
fn precinct_payload_errors_retain_exact_header_and_late_coefficient_effects() {
    let limits = ResourceLimits::default();
    for (data, eph, expected, error, coefficient) in [
        (&[0xe1][..], false, None, MalformedKind::Truncated, 0),
        (
            &[0xe1, 0xff, 0x93, 0xff][..],
            true,
            None,
            MalformedKind::InvalidPacketHeader,
            0,
        ),
        (
            &[0xe1, 0xff][..],
            false,
            Some(3),
            MalformedKind::InvalidPacketLength,
            0,
        ),
    ] {
        let mut precinct = literal_packet_precinct();
        let mut parameters = literal_payload_parameters();
        parameters.eph = eph;
        parameters.expected_packet_length = expected;
        assert_eq!(
            decode_precinct_packet_payload(data, &[], parameters, &mut precinct, &limits),
            Err(DecodeError::MalformedInput {
                offset: if error == MalformedKind::InvalidPacketHeader {
                    0
                } else {
                    21
                },
                kind: error,
            })
        );
        assert_eq!(precinct.states[0].total_passes(), 1);
        assert_eq!(precinct.states[0].zero_bitplanes(), Some(0));
        assert!(precinct.states[0].included());
        for tree in [
            &precinct.subbands[0].inclusion_tree,
            &precinct.subbands[0].zero_bitplane_tree,
        ] {
            assert_eq!(tree.nodes[0], TagTreeNode { low: 0, value: 0 });
        }
        assert_eq!(
            precinct.decoders[0]
                .plane()
                .signed_coefficient(0, 0)
                .unwrap(),
            coefficient
        );
        assert_eq!(
            precinct.decoders[0].next_pass(),
            u32::from(expected.is_some())
        );
        assert_eq!(
            (precinct.component, precinct.resolution, precinct.precinct),
            (0, 0, 0)
        );
    }
}

#[test]
fn actual_precinct_wrapper_commits_literal_ht_cleanup_before_late_length_mismatch() {
    let limits = ResourceLimits::default();
    let mut style = coding_style(false, false);
    style.code_block_style = 0x40;
    let ht_style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let tile = TilePartPayload::uniform_for_packet_decoding(
        0,
        0,
        1,
        1,
        style,
        crate::codestream::RoiShifts::none(),
        &[0xe3, 0, 0x63, 0],
    )
    .unwrap();
    for expected in [4, 5] {
        let mut precinct = literal_packet_precinct();
        precinct.contexts[0].tier1_style = ht_style;
        precinct.decoders[0] =
            Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, ht_style).unwrap();
        let result = decode_precinct_packet(
            &tile,
            0,
            &[],
            0,
            Some(expected),
            0,
            &mut precinct,
            true,
            &limits,
        );
        assert_eq!(
            result,
            if expected == 4 {
                Ok((
                    PacketBodyDecode {
                        present: true,
                        code_blocks: 1,
                        contributions: 1,
                        segments: 1,
                        passes: 1,
                        header_bytes: 1,
                        body_bytes: 3,
                        bytes_consumed: 4,
                    },
                    4,
                    0,
                ))
            } else {
                Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::InvalidPacketLength,
                })
            }
        );
        assert_eq!(precinct.states[0].total_passes(), 1);
        assert_eq!(precinct.states[0].high_throughput(), Some(true));
        assert_eq!(
            precinct.decoders[0]
                .plane()
                .signed_coefficient(0, 0)
                .unwrap(),
            -1
        );
        assert_eq!(precinct.decoders[0].next_pass(), 1);
    }
}

#[test]
fn actual_precinct_wrapper_preserves_shape_cap_offset_and_component_error_priority() {
    let limits = ResourceLimits::default();
    let tile = TilePartPayload::uniform_for_packet_decoding(
        0,
        0,
        1,
        1,
        coding_style(true, true),
        crate::codestream::RoiShifts::none(),
        &[],
    )
    .unwrap();
    let mut precinct = literal_packet_precinct();
    precinct.component = 1;
    precinct.contexts.clear();
    assert_eq!(
        decode_precinct_packet(&tile, 7, &[], 0, None, 0, &mut precinct, true, &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidPacketHeader
        })
    );
    precinct.contexts.push(literal_precinct_header_context());
    let mut second = literal_packet_precinct();
    precinct.states.append(&mut second.states);
    precinct.contexts.append(&mut second.contexts);
    precinct.decoders.append(&mut second.decoders);
    let limited = limits.with_maximum_code_blocks(1).unwrap();
    assert_eq!(
        decode_precinct_packet(&tile, 7, &[], 0, None, 0, &mut precinct, true, &limited),
        Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlocks,
            limit: 1,
            actual: 2
        })
    );
    precinct.states.pop();
    precinct.contexts.pop();
    precinct.decoders.pop();
    assert_eq!(
        decode_precinct_packet(&tile, 7, &[], 0, None, 0, &mut precinct, true, &limits),
        Err(DecodeError::MalformedInput {
            offset: 7,
            kind: MalformedKind::InvalidPacketLength
        })
    );
    assert_eq!(
        decode_precinct_packet(&tile, 0, &[], 0, None, 0, &mut precinct, true, &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodingStyle
        })
    );
    assert!(!precinct.states[0].included());
    assert_eq!(precinct.states[0].total_passes(), 0);
    assert_eq!(
        precinct.decoders[0]
            .plane()
            .signed_coefficient(0, 0)
            .unwrap(),
        0
    );
}

#[test]
fn precinct_headers_associate_real_bits_and_preserve_overlapping_raw_subbands() {
    let limits = ResourceLimits::default();
    for repeated in [false, true] {
        let mut states = [code_block_packet_state_new()];
        let contexts = [literal_precinct_header_context()];
        let mut subbands = vec![literal_header_subband()];
        if repeated {
            subbands.push(literal_header_subband());
        }
        let mut contributions = [None];
        let bytes: &[u8] = if repeated { &[0xc3, 0] } else { &[0xc2] };
        let mut reader = packet_reader_prefix(bytes, &limits);
        let mut progress = PrecinctHeaderProgress {
            subband_index: 0,
            local_index: 0,
            contribution_count: 0,
        };
        decode_precinct_contribution_headers(
            &mut states,
            &contexts,
            &mut subbands,
            &mut contributions,
            &mut reader,
            PrecinctHeaderParameters {
                layer: 0,
                style: Tier1CodingStyle::default(),
            },
            &mut progress,
        )
        .unwrap();
        let count = if repeated { 2 } else { 1 };
        assert_eq!(
            (
                progress.subband_index,
                progress.local_index,
                progress.contribution_count
            ),
            (count as usize, 1, count)
        );
        assert_eq!(
            states[0],
            CodeBlockPacketState {
                included: true,
                zero_bitplanes: Some(0),
                lblock: 3,
                total_passes: count,
                high_throughput: Some(false),
            }
        );
        let header = contributions[0].unwrap();
        assert_eq!(
            (
                header.first_inclusion,
                header.zero_bitplanes,
                header.new_passes,
                header.data_length,
                header.high_throughput,
                header.segment_count
            ),
            (!repeated, 0, 1, if repeated { 0 } else { 1 }, false, 1)
        );
        assert_eq!(header.segment_passes[0], 1);
        assert_eq!(header.segment_lengths[0], if repeated { 0 } else { 1 });
        assert!(header.segment_passes[1..].iter().all(|value| *value == 0));
        assert!(header.segment_lengths[1..].iter().all(|value| *value == 0));
        assert_eq!(
            (reader.byte_index, reader.bits_remaining, reader.bits_read),
            if repeated { (2, 3, 13) } else { (1, 1, 7) }
        );
        assert_eq!(
            subbands[0].inclusion_tree.nodes[0],
            TagTreeNode { low: 0, value: 0 }
        );
        assert_eq!(
            subbands[0].zero_bitplane_tree.nodes[0],
            TagTreeNode { low: 0, value: 0 }
        );
        if repeated {
            assert_eq!(
                subbands[1].inclusion_tree.nodes[0],
                TagTreeNode {
                    low: 0,
                    value: u32::MAX
                }
            );
            assert_eq!(
                subbands[1].zero_bitplane_tree.nodes[0],
                TagTreeNode {
                    low: 0,
                    value: u32::MAX
                }
            );
        }
    }
}

#[test]
fn precinct_headers_keep_committed_header_before_late_count_or_slot_failure() {
    let limits = ResourceLimits::default();
    for overflow in [false, true] {
        let mut states = [code_block_packet_state_new()];
        let contexts = [literal_precinct_header_context()];
        let mut subbands = [literal_header_subband()];
        let mut contributions = vec![None; usize::from(overflow)];
        let mut reader = packet_reader_prefix(&[0xc2], &limits);
        let mut progress = PrecinctHeaderProgress {
            subband_index: 0,
            local_index: 0,
            contribution_count: if overflow { u32::MAX } else { 0 },
        };
        assert_eq!(
            decode_precinct_contribution_headers(
                &mut states,
                &contexts,
                &mut subbands,
                &mut contributions,
                &mut reader,
                PrecinctHeaderParameters {
                    layer: 0,
                    style: Tier1CodingStyle::default()
                },
                &mut progress,
            ),
            Err(if overflow {
                packet_arithmetic_overflow()
            } else {
                invalid_packet_header()
            })
        );
        assert_eq!(
            (
                progress.subband_index,
                progress.local_index,
                progress.contribution_count
            ),
            (0, 0, if overflow { u32::MAX } else { 1 })
        );
        assert_eq!(states[0].total_passes, 1);
        assert!(states[0].included);
        assert_eq!(states[0].zero_bitplanes, Some(0));
        assert_eq!(
            (reader.byte_index, reader.bits_remaining, reader.bits_read),
            (1, 1, 7)
        );
        assert!(contributions.iter().all(Option::is_none));
        assert_eq!(
            subbands[0].inclusion_tree.nodes[0],
            TagTreeNode { low: 0, value: 0 }
        );
        assert_eq!(
            subbands[0].zero_bitplane_tree.nodes[0],
            TagTreeNode { low: 0, value: 0 }
        );
    }
}

fn literal_precinct_body_descriptors() -> [Option<CodeBlockContribution>; 3] {
    let mut ht = one_ff_legacy_contribution();
    ht.high_throughput = true;
    ht.data_length = 3;
    ht.segment_lengths[0] = 3;
    [Some(ht), None, Some(one_ff_legacy_contribution())]
}

#[test]
fn precinct_body_preflight_reports_exact_cursor_before_any_execution() {
    let contributions = literal_precinct_body_descriptors();
    for (data, expected_end, expected_index, expected_result) in [
        (&[0, 0x63, 0, 0xff][..], 4, 3, Ok(())),
        (
            &[0, 0x63, 0][..],
            4,
            2,
            Err(DecodeError::MalformedInput {
                offset: 71,
                kind: MalformedKind::Truncated,
            }),
        ),
    ] {
        let mut cursor = PacketBodyPreflight { index: 0, end: 0 };
        assert_eq!(
            preflight_packet_body_ranges(&contributions, data, &mut cursor, (71, 0)),
            expected_result
        );
        assert_eq!((cursor.index, cursor.end), (expected_index, expected_end));
    }
    let mut cursor = PacketBodyPreflight {
        index: 0,
        end: usize::MAX,
    };
    assert_eq!(
        preflight_packet_body_ranges(&contributions, &[], &mut cursor, (71, 0)),
        Err(packet_arithmetic_overflow())
    );
    assert_eq!((cursor.index, cursor.end), (0, usize::MAX));
    let mut cursor = PacketBodyPreflight {
        index: usize::MAX,
        end: 19,
    };
    assert_eq!(
        preflight_packet_body_ranges(&contributions, &[], &mut cursor, (71, 0)),
        Ok(())
    );
    assert_eq!((cursor.index, cursor.end), (usize::MAX, 19));
}

#[test]
fn precinct_skipped_execution_consumes_ranges_without_decoder_shape_or_counter_changes() {
    let contributions = literal_precinct_body_descriptors();
    for (data, expected_offset, expected_index, expected_result) in [
        (&[0, 0x63, 0, 0xff][..], 4, 3, Ok(())),
        (
            &[0, 0x63, 0][..],
            3,
            2,
            Err(DecodeError::MalformedInput {
                offset: 71,
                kind: MalformedKind::Truncated,
            }),
        ),
    ] {
        let mut progress = PacketBodyExecutionProgress {
            index: 0,
            offset: 0,
            segments: u32::MAX,
            passes: u32::MAX,
        };
        assert_eq!(
            execute_packet_body_contributions(
                &mut [],
                &contributions,
                data,
                &mut progress,
                (71, 0),
                false,
                &ResourceLimits::default(),
            ),
            expected_result
        );
        assert_eq!(
            (
                progress.index,
                progress.offset,
                progress.segments,
                progress.passes
            ),
            (expected_index, expected_offset, u32::MAX, u32::MAX)
        );
    }
}

#[test]
fn precinct_execution_retains_real_prior_coefficients_and_late_partial_counters() {
    let contributions = literal_precinct_body_descriptors();
    let data = [0, 0x63, 0, 0xff];
    let style = Tier1CodingStyle::from_code_block_style(0xc0).unwrap();
    let decoder = || Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
    let mut decoders = vec![decoder()];
    let mut progress = PacketBodyExecutionProgress {
        index: 0,
        offset: 0,
        segments: 0,
        passes: 0,
    };
    assert_eq!(
        execute_packet_body_contributions(
            &mut decoders,
            &contributions,
            &data,
            &mut progress,
            (71, 0),
            true,
            &ResourceLimits::default(),
        ),
        Err(invalid_packet_header())
    );
    assert_eq!(
        (
            progress.index,
            progress.offset,
            progress.segments,
            progress.passes
        ),
        (2, 3, 1, 1)
    );
    assert_eq!(decoders[0].plane().signed_coefficient(0, 0).unwrap(), -1);
    assert_eq!(
        (decoders[0].next_pass(), decoders[0].decoded_bytes()),
        (1, 3)
    );
    for (segments, passes, expected_segments) in [(u32::MAX, 7, u32::MAX), (9, u32::MAX, 10)] {
        let mut decoders = vec![decoder()];
        let mut progress = PacketBodyExecutionProgress {
            index: 0,
            offset: 0,
            segments,
            passes,
        };
        assert_eq!(
            execute_packet_body_contributions(
                &mut decoders,
                &contributions,
                &data,
                &mut progress,
                (71, 0),
                true,
                &ResourceLimits::default(),
            ),
            Err(packet_arithmetic_overflow())
        );
        assert_eq!(
            (
                progress.index,
                progress.offset,
                progress.segments,
                progress.passes
            ),
            (0, 0, expected_segments, passes)
        );
        assert_eq!(decoders[0].plane().signed_coefficient(0, 0).unwrap(), -1);
        assert_eq!(
            (
                decoders[0].next_pass(),
                decoders[0].decoded_segments(),
                decoders[0].decoded_bytes()
            ),
            (1, 1, 3)
        );
    }
}

fn one_ff_legacy_contribution() -> CodeBlockContribution {
    let mut contribution = CodeBlockContribution {
        first_inclusion: true,
        zero_bitplanes: 0,
        new_passes: 1,
        data_length: 1,
        high_throughput: false,
        segment_count: 1,
        segment_passes: [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
        segment_lengths: [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
    };
    contribution.segment_passes[0] = 1;
    contribution.segment_lengths[0] = 1;
    contribution
}

fn one_bit_legacy_decoder(force_high_throughput: bool) -> Tier1CodeBlockDecoder {
    Tier1CodeBlockDecoder::new(
        1,
        1,
        1,
        crate::tier1::SubbandOrientation::Ll,
        Tier1CodingStyle {
            force_high_throughput,
            ..Tier1CodingStyle::default()
        },
    )
    .unwrap()
}

fn expected_one_ff_decoder(before: &Tier1CodeBlockDecoder, header_prepared: bool) -> String {
    let mut contexts = crate::mq::MqDecoder::new(&[], &ResourceLimits::default()).unwrap();
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
    let mut expected = format!("{before:?}")
        .replacen("next_pass: 0,", "next_pass: 1,", 1)
        .replacen("decoded_segments: 0,", "decoded_segments: 1,", 1)
        .replacen("decoded_bytes: 0,", "decoded_bytes: 1,", 1)
        .replacen("legacy_decode_work: 0,", "legacy_decode_work: 2,", 1)
        .replacen(
            "mq_context_state: None,",
            &format!("mq_context_state: Some({:?}),", contexts.context_state()),
            1,
        );
    if header_prepared {
        expected = expected.replacen("zero_bitplanes: None,", "zero_bitplanes: Some(0),", 1);
    }
    expected
}

#[test]
fn legacy_packet_body_routes_real_mq_bytes_and_retains_late_total_error_mutations() {
    for mismatch in 0..3 {
        let mut decoder = one_bit_legacy_decoder(false);
        let expected = expected_one_ff_decoder(&decoder, false);
        let mut contribution = one_ff_legacy_contribution();
        let body: &[u8] = if mismatch == 2 { &[0xff, 0] } else { &[0xff] };
        if mismatch == 1 {
            contribution.new_passes = 2;
        }
        let result = decode_legacy_code_block_contribution_body(
            &mut decoder,
            &contribution,
            body,
            &ResourceLimits::default(),
        );
        assert_eq!(format!("{decoder:?}"), expected);
        assert_eq!(
            result,
            if mismatch == 0 {
                Ok(CodeBlockBodyDecode {
                    segments: 1,
                    passes: 1,
                    bytes: 1,
                })
            } else {
                Err(packet_invalid_code_block())
            }
        );
    }
    let mut decoder = one_bit_legacy_decoder(false);
    let before = format!("{decoder:?}");
    let mut contribution = one_ff_legacy_contribution();
    contribution.segment_count = 0;
    contribution.new_passes = 0;
    contribution.data_length = u32::MAX;
    contribution.high_throughput = true;
    assert_eq!(
        decode_legacy_code_block_contribution_body(
            &mut decoder,
            &contribution,
            &[],
            &ResourceLimits::default(),
        ),
        Ok(CodeBlockBodyDecode {
            segments: 0,
            passes: 0,
            bytes: u32::MAX
        })
    );
    assert_eq!(format!("{decoder:?}"), before);
}

#[test]
fn legacy_packet_segment_checks_real_range_and_counter_priority_without_input_invariants() {
    let limits = ResourceLimits::default();
    let mut contribution = one_ff_legacy_contribution();
    for offset in [0, usize::MAX] {
        let mut decoder = one_bit_legacy_decoder(false);
        let before = format!("{decoder:?}");
        let expected_decoded = expected_one_ff_decoder(&decoder, false);
        let mut index = 0;
        let mut current_offset = offset;
        let mut passes = u32::MAX;
        assert_eq!(
            decode_legacy_code_block_segment(
                &mut decoder,
                &contribution,
                &[0xff],
                &limits,
                &mut index,
                &mut current_offset,
                &mut passes,
            ),
            Err(packet_arithmetic_overflow())
        );
        assert_eq!((index, current_offset, passes), (0, offset, u32::MAX));
        assert_eq!(
            format!("{decoder:?}"),
            if offset == 0 {
                expected_decoded
            } else {
                before
            }
        );
    }
    contribution.segment_count = u8::MAX;
    let mut decoder = one_bit_legacy_decoder(false);
    let before = format!("{decoder:?}");
    let (mut index, mut offset, mut passes) = (164, usize::MAX, u32::MAX);
    assert_eq!(
        decode_legacy_code_block_segment(
            &mut decoder,
            &contribution,
            &[],
            &limits,
            &mut index,
            &mut offset,
            &mut passes,
        ),
        Err(invalid_packet_header())
    );
    assert_eq!((index, offset, passes), (164, usize::MAX, u32::MAX));
    assert_eq!(format!("{decoder:?}"), before);
}

#[test]
fn real_packet_prefix_and_outer_clone_commit_preserve_order_and_full_rollback() {
    for force in [false, true] {
        for wrong_length in [false, true] {
            let mut decoder = one_bit_legacy_decoder(force);
            let before = format!("{decoder:?}");
            let contribution = one_ff_legacy_contribution();
            let body: &[u8] = if wrong_length { &[] } else { &[0xff] };
            let expected = if !force && !wrong_length {
                before.replacen("zero_bitplanes: None,", "zero_bitplanes: Some(0),", 1)
            } else {
                before
            };
            assert_eq!(
                prepare_code_block_contribution_body(&mut decoder, &contribution, body),
                if force || wrong_length {
                    Err(packet_invalid_code_block())
                } else {
                    Ok(())
                }
            );
            assert_eq!(format!("{decoder:?}"), expected);
        }
    }
    for wrong_total in [false, true] {
        let mut decoder = one_bit_legacy_decoder(false);
        let before = format!("{decoder:?}");
        let decoded = expected_one_ff_decoder(&decoder, true);
        let mut contribution = one_ff_legacy_contribution();
        if wrong_total {
            contribution.new_passes = 2;
        }
        let result = decode_code_block_contribution_body(
            &mut decoder,
            &contribution,
            &[0xff],
            &ResourceLimits::default(),
        );
        assert_eq!(
            result,
            if wrong_total {
                Err(packet_invalid_code_block())
            } else {
                Ok(CodeBlockBodyDecode {
                    segments: 1,
                    passes: 1,
                    bytes: 1,
                })
            }
        );
        assert_eq!(
            format!("{decoder:?}"),
            if wrong_total { before } else { decoded }
        );
    }
}

#[test]
fn native_contribution_segment_lookup_covers_all_counts_indices_and_full_stored_arrays() {
    let mut contribution = CodeBlockContribution {
        first_inclusion: true,
        zero_bitplanes: u16::MAX,
        new_passes: u8::MAX,
        data_length: u32::MAX,
        high_throughput: true,
        segment_count: 0,
        segment_passes: [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
        segment_lengths: [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
    };
    for index in 0..MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION {
        contribution.segment_passes[index] = u8::MAX - index as u8;
        contribution.segment_lengths[index] = u32::MAX - index as u32;
    }
    for count in 0..=u8::MAX {
        contribution.segment_count = count;
        let before = contribution;
        assert_eq!(contribution.segment_count(), count);
        for index in 0..=u8::MAX {
            let expected =
                if index < count && usize::from(index) < MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION {
                    Ok(CodeBlockSegmentContribution {
                        passes: u8::MAX - index,
                        data_length: u32::MAX - u32::from(index),
                    })
                } else {
                    Err(invalid_packet_header())
                };
            assert_eq!(contribution.segment(index), expected);
            assert_eq!(contribution, before);
        }
    }
}

#[test]
fn readonly_precinct_decoder_accessors_use_actual_vec_and_entire_native_indices() {
    for count in 0..=4 {
        let mut decoders = Vec::with_capacity(count + 8);
        for index in 0..count {
            decoders.push(
                Tier1CodeBlockDecoder::new(
                    u16::try_from(index + 1).unwrap(),
                    1,
                    1,
                    SubbandOrientation::Ll,
                    Tier1CodingStyle::default(),
                )
                .unwrap(),
            );
        }
        let precinct = PacketPrecinctDecoder {
            component: u16::MAX,
            resolution: u8::MAX,
            precinct: u32::MAX,
            states: Vec::new(),
            contexts: Vec::new(),
            decoders,
            subbands: Vec::new(),
        };
        assert_eq!(precinct.decoder_count(), count);
        assert_eq!(precinct.decoders().len(), count);
        for index in (0..count + 9).chain([usize::MAX / 2, usize::MAX - 1, usize::MAX]) {
            match precinct.decoder(index) {
                Ok(value) => {
                    assert!(index < count);
                    assert!(core::ptr::eq(value, &precinct.decoders()[index]));
                }
                Err(error) => {
                    assert!(index >= count);
                    assert_eq!(
                        error,
                        DecodeError::MalformedInput {
                            offset: 0,
                            kind: MalformedKind::InvalidPacketHeader
                        }
                    );
                }
            }
        }
    }
}
use crate::codestream::{
    CodingStyle, ComponentCodingStyles, ComponentQuantizations, Quantization, WaveletTransform,
};
use std::collections::HashSet;

fn coding_style(sop_markers: bool, eph_markers: bool) -> CodingStyle {
    CodingStyle {
        progression_order: ProgressionOrder::Lrcp,
        layers: 2,
        multiple_component_transform: false,
        decomposition_levels: 0,
        decomposition_structure: None,
        decomposition_directions: [crate::codestream::DecompositionDirection::TwoDimensional; 32],
        code_block_width: 1,
        code_block_height: 1,
        code_block_style: 0,
        transform: WaveletTransform::Reversible5x3,
        precincts_defined: false,
        sop_markers,
        eph_markers,
        precinct_exponents: [(15, 15); 33],
    }
}

fn component_styles(style: CodingStyle) -> (ComponentCodingStyles, ComponentQuantizations) {
    (
        ComponentCodingStyles::uniform(1, style).unwrap(),
        ComponentQuantizations::uniform(1, Quantization::reversible_default(style)).unwrap(),
    )
}

fn pack_packet_bits(bits: &[bool]) -> Vec<u8> {
    let mut bytes = Vec::new();
    let mut current = 0_u8;
    let mut used = 0_u8;
    let mut capacity = 8_u8;
    for bit in bits {
        current <<= 1;
        current |= u8::from(*bit);
        used += 1;
        if used == capacity {
            bytes.push(current);
            capacity = if current == 0xff { 7 } else { 8 };
            current = 0;
            used = 0;
        }
    }
    if used != 0 {
        current <<= capacity - used;
        bytes.push(current);
    }
    bytes
}

fn two_block_first_layer_header() -> Vec<u8> {
    pack_packet_bits(&[
        true, // non-empty packet
        true, true, // block 0 inclusion tree: root, leaf
        true, true,  // block 0 zero-bitplane tree: root, leaf
        false, // one coding pass
        false, // no Lblock increment
        false, true, false, // two body bytes
        true,  // block 1 inclusion leaf
        true,  // block 1 zero-bitplane leaf
        false, // one coding pass
        false, // no Lblock increment
        false, true, false, // two body bytes
    ])
}

#[test]
fn decodes_every_packet_coding_pass_count_and_length_width() {
    for passes in 1_u32..=164 {
        let (mut bits, suffix, count) = match passes {
            1 => (vec![false], 0, 0),
            2 => (vec![true, false], 0, 0),
            3..=5 => (vec![true, true], passes - 3, 2),
            6..=36 => (vec![true; 4], passes - 6, 5),
            _ => (vec![true; 9], passes - 37, 7),
        };
        for bit in (0..count).rev() {
            bits.push(suffix & (1 << bit) != 0);
        }
        bits.push(true);
        let bytes = pack_packet_bits(&bits);
        let mut reader = PacketBitReader::new(&bytes, &ResourceLimits::default()).unwrap();
        assert_eq!(u32::from(read_new_passes(&mut reader).unwrap()), passes);
        assert!(
            reader.read_bit().unwrap(),
            "pass count consumed the next field"
        );
        assert_eq!(u32::from(floor_log2(passes)), 31 - passes.leading_zeros());
    }
}

#[test]
fn reads_bits_most_significant_first() {
    let mut reader = PacketBitReader::new(&[0b1010_0000], &ResourceLimits::default()).unwrap();
    assert!(reader.read_bit().unwrap());
    assert!(!reader.read_bit().unwrap());
    assert!(reader.read_bit().unwrap());
    assert_eq!(reader.bits_read(), 3);
    assert_eq!(reader.bytes_consumed(), 1);
}

#[test]
fn enforces_stuffed_bit_after_ff() {
    let mut reader = PacketBitReader::new(&[0xff, 0x7f], &ResourceLimits::default()).unwrap();
    assert_eq!(reader.read_bits(8).unwrap(), 0xff);
    assert!(reader.read_bit().unwrap());
    assert_eq!(reader.bits_read(), 9);

    let mut invalid = PacketBitReader::new(&[0xff, 0x80], &ResourceLimits::default()).unwrap();
    assert_eq!(invalid.read_bits(8).unwrap(), 0xff);
    assert!(matches!(
        invalid.read_bit(),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBitStuffing,
            ..
        })
    ));
}

#[test]
fn aligns_and_reports_truncation() {
    let mut reader = PacketBitReader::new(&[0b1000_0000], &ResourceLimits::default()).unwrap();
    assert!(reader.read_bit().unwrap());
    reader.align_to_byte();
    assert!(reader.is_byte_aligned());
    assert!(matches!(
        reader.read_bit(),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::Truncated,
            ..
        })
    ));
}

#[test]
fn rejects_excessive_bit_counts_and_header_bytes() {
    let mut reader = PacketBitReader::new(&[0; 4], &ResourceLimits::default()).unwrap();
    assert!(reader.read_bits(33).is_err());
    let limits = ResourceLimits::default()
        .with_maximum_packet_header_bytes(1)
        .unwrap();
    assert!(matches!(
        PacketBitReader::new(&[0; 4], &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::PacketHeaderBytes,
            ..
        })
    ));
}

#[test]
fn constructs_bounded_tag_tree_topology() {
    let tree = TagTree::new(3, 2, &ResourceLimits::default()).unwrap();
    assert_eq!(tree.leaf_count().unwrap(), 6);
    assert_eq!(tree.node_count(), 9);
}

#[test]
fn decodes_and_reuses_monotonic_tag_tree_state() {
    let mut tree = TagTree::new(1, 1, &ResourceLimits::default()).unwrap();
    let mut reader = PacketBitReader::new(&[0b0010_0000], &ResourceLimits::default()).unwrap();
    let value = tree.decode(0, 0, 3, &mut reader).unwrap();
    assert_eq!(value.value, Some(2));
    assert!(value.is_below_threshold);
    assert_eq!(reader.bits_read(), 3);

    let repeated = tree.decode(0, 0, 4, &mut reader).unwrap();
    assert_eq!(repeated.value, Some(2));
    assert_eq!(reader.bits_read(), 3);
}

#[test]
fn rejects_invalid_tag_tree_coordinates() {
    let mut tree = TagTree::new(2, 2, &ResourceLimits::default()).unwrap();
    let mut reader = PacketBitReader::new(&[0], &ResourceLimits::default()).unwrap();
    assert!(matches!(
        tree.decode(2, 0, 1, &mut reader),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidTagTree,
            ..
        })
    ));
}

#[test]
fn preserves_descendants_when_ancestor_is_not_below_threshold() {
    let mut tree = TagTree::new(2, 1, &ResourceLimits::default()).unwrap();
    let mut reader = PacketBitReader::new(&[0b0110_0000], &ResourceLimits::default()).unwrap();
    let first = tree.decode(0, 0, 1, &mut reader).unwrap();
    assert!(!first.is_below_threshold);
    assert_eq!(reader.bits_read(), 1);

    let second = tree.decode(0, 0, 2, &mut reader).unwrap();
    assert_eq!(second.value, Some(1));
    assert_eq!(reader.bits_read(), 3);
}

#[test]
fn all_progression_orders_emit_identical_packet_sets() {
    let grid = PacketGrid::new(2, 2, 2, vec![1, 2, 3, 1], &ResourceLimits::default()).unwrap();
    assert_eq!(grid.packet_count(), 14);
    let orders = [
        ProgressionOrder::Lrcp,
        ProgressionOrder::Rlcp,
        ProgressionOrder::Rpcl,
        ProgressionOrder::Pcrl,
        ProgressionOrder::Cprl,
    ];
    let mut baseline = None;
    for order in orders {
        let mut iterator = PacketIterator::new(&grid, order);
        let packets = iterator
            .by_ref()
            .collect::<Result<HashSet<PacketCoordinate>, _>>()
            .unwrap();
        assert_eq!(packets.len(), 14);
        assert_eq!(iterator.emitted(), 14);
        if let Some(expected) = &baseline {
            assert_eq!(&packets, expected);
        } else {
            baseline = Some(packets);
        }
    }
}

#[test]
fn progression_iteration_is_order_specific_and_bounded() {
    let grid = PacketGrid::new(2, 2, 1, vec![1, 1], &ResourceLimits::default()).unwrap();
    let mut lrcp = PacketIterator::new(&grid, ProgressionOrder::Lrcp);
    assert_eq!(
        lrcp.next_packet().unwrap(),
        Some(PacketCoordinate {
            layer: 0,
            resolution: 0,
            component: 0,
            precinct: 0,
        })
    );
    assert_eq!(
        lrcp.next_packet().unwrap(),
        Some(PacketCoordinate {
            layer: 0,
            resolution: 0,
            component: 1,
            precinct: 0,
        })
    );

    let limits = ResourceLimits::default().with_maximum_packets(1).unwrap();
    assert!(matches!(
        PacketGrid::new(2, 1, 1, vec![1], &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            ..
        })
    ));
}

#[test]
fn progression_change_windows_emit_each_packet_once_in_window_order() {
    let limits = ResourceLimits::default();
    let grid = PacketGrid::new(2, 2, 1, vec![1, 1], &limits).unwrap();
    let changes = ProgressionChanges::from_records(vec![
        ProgressionChange {
            resolution_start: 0,
            component_start: 0,
            layer_end: 2,
            resolution_end: 1,
            component_end: 1,
            progression_order: ProgressionOrder::Lrcp,
        },
        ProgressionChange {
            resolution_start: 0,
            component_start: 1,
            layer_end: 2,
            resolution_end: 1,
            component_end: 2,
            progression_order: ProgressionOrder::Rlcp,
        },
    ]);
    let mut iterator =
        ProgressionPacketIterator::new(&grid, ProgressionOrder::Cprl, &changes, &limits).unwrap();
    let mut packets = Vec::new();
    while let Some(packet) = iterator.next_packet().unwrap() {
        packets.push(packet);
    }
    assert_eq!(
        packets,
        vec![
            PacketCoordinate {
                layer: 0,
                resolution: 0,
                component: 0,
                precinct: 0,
            },
            PacketCoordinate {
                layer: 1,
                resolution: 0,
                component: 0,
                precinct: 0,
            },
            PacketCoordinate {
                layer: 0,
                resolution: 0,
                component: 1,
                precinct: 0,
            },
            PacketCoordinate {
                layer: 1,
                resolution: 0,
                component: 1,
                precinct: 0,
            },
        ]
    );
    assert_eq!(iterator.emitted(), grid.packet_count());
}

#[test]
fn overlapping_progression_windows_skip_previously_emitted_packets() {
    let limits = ResourceLimits::default();
    let grid = PacketGrid::new(2, 1, 1, vec![1], &limits).unwrap();
    let changes = ProgressionChanges::from_records(vec![
        ProgressionChange {
            resolution_start: 0,
            component_start: 0,
            layer_end: 1,
            resolution_end: 1,
            component_end: 1,
            progression_order: ProgressionOrder::Rlcp,
        },
        ProgressionChange {
            resolution_start: 0,
            component_start: 0,
            layer_end: 2,
            resolution_end: 1,
            component_end: 1,
            progression_order: ProgressionOrder::Lrcp,
        },
    ]);
    let mut iterator =
        ProgressionPacketIterator::new(&grid, ProgressionOrder::Cprl, &changes, &limits).unwrap();
    let mut unique = HashSet::new();
    while let Some(packet) = iterator.next_packet().unwrap() {
        assert!(unique.insert(packet));
    }
    assert_eq!(unique.len() as u64, grid.packet_count());
}

#[test]
fn decodes_code_block_packet_contributions() {
    let limits = ResourceLimits::default();
    let mut inclusion = TagTree::new(1, 1, &limits).unwrap();
    let mut zero_bitplanes = TagTree::new(1, 1, &limits).unwrap();
    let mut state = CodeBlockPacketState::new();
    let mut first_reader = PacketBitReader::new(&[0xca], &limits).unwrap();
    let first = decode_code_block_contribution(
        &mut state,
        &mut inclusion,
        &mut zero_bitplanes,
        CodeBlockPacketContext {
            leaf_x: 0,
            leaf_y: 0,
            layer: 0,
            maximum_zero_bitplanes: 8,
            tier1_style: Tier1CodingStyle::default(),
        },
        &mut first_reader,
    )
    .unwrap()
    .unwrap();
    assert!(first.first_inclusion);
    assert_eq!(first.zero_bitplanes, 0);
    assert_eq!(first.new_passes, 1);
    assert_eq!(first.data_length, 5);
    assert_eq!(first.segment_count(), 1);
    assert_eq!(
        first.segment(0).unwrap(),
        CodeBlockSegmentContribution {
            passes: 1,
            data_length: 5,
        }
    );
    assert_eq!(state.total_passes(), 1);

    let mut second_reader = PacketBitReader::new(&[0xd0, 0xc0], &limits).unwrap();
    let second = decode_code_block_contribution(
        &mut state,
        &mut inclusion,
        &mut zero_bitplanes,
        CodeBlockPacketContext {
            leaf_x: 0,
            leaf_y: 0,
            layer: 1,
            maximum_zero_bitplanes: 8,
            tier1_style: Tier1CodingStyle::default(),
        },
        &mut second_reader,
    )
    .unwrap()
    .unwrap();
    assert!(!second.first_inclusion);
    assert_eq!(second.new_passes, 2);
    assert_eq!(second.data_length, 3);
    assert_eq!(second.segment_count(), 1);
    assert_eq!(second.segment(0).unwrap().passes, 2);
    assert_eq!(state.total_passes(), 3);
    assert_eq!(state.lblock(), 4);

    let previous = state;
    let mut absent_reader = PacketBitReader::new(&[0], &limits).unwrap();
    assert!(
        decode_code_block_contribution(
            &mut state,
            &mut inclusion,
            &mut zero_bitplanes,
            CodeBlockPacketContext {
                leaf_x: 0,
                leaf_y: 0,
                layer: 2,
                maximum_zero_bitplanes: 8,
                tier1_style: Tier1CodingStyle::default(),
            },
            &mut absent_reader,
        )
        .unwrap()
        .is_none()
    );
    assert_eq!(state, previous);
}

#[test]
fn preserves_code_block_state_on_invalid_length() {
    let limits = ResourceLimits::default();
    let mut inclusion = TagTree::new(1, 1, &limits).unwrap();
    let mut zero_bitplanes = TagTree::new(1, 1, &limits).unwrap();
    let mut state = CodeBlockPacketState::new();
    let initial = state;
    let mut reader = PacketBitReader::new(&[0xc0], &limits).unwrap();
    assert!(matches!(
        decode_code_block_contribution(
            &mut state,
            &mut inclusion,
            &mut zero_bitplanes,
            CodeBlockPacketContext {
                leaf_x: 0,
                leaf_y: 0,
                layer: 0,
                maximum_zero_bitplanes: 8,
                tier1_style: Tier1CodingStyle::default(),
            },
            &mut reader,
        ),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidPacketHeader,
            ..
        })
    ));
    assert_eq!(state, initial);
}

#[test]
fn permits_zero_byte_legacy_continuation_without_accepting_an_empty_initial_segment() {
    let limits = ResourceLimits::default();
    let mut inclusion = TagTree::new(1, 1, &limits).unwrap();
    let mut zero_bitplanes = TagTree::new(1, 1, &limits).unwrap();
    let mut state = CodeBlockPacketState {
        included: true,
        zero_bitplanes: Some(0),
        lblock: 3,
        total_passes: 9,
        high_throughput: Some(false),
    };
    let mut reader = PacketBitReader::new(&[0x80], &limits).unwrap();
    let contribution = decode_code_block_contribution(
        &mut state,
        &mut inclusion,
        &mut zero_bitplanes,
        CodeBlockPacketContext {
            leaf_x: 0,
            leaf_y: 0,
            layer: 1,
            maximum_zero_bitplanes: 8,
            tier1_style: Tier1CodingStyle::from_code_block_style(1).unwrap(),
        },
        &mut reader,
    )
    .unwrap()
    .unwrap();
    assert!(!contribution.first_inclusion);
    assert_eq!(contribution.new_passes, 1);
    assert_eq!(contribution.data_length, 0);
    assert_eq!(contribution.segment_count(), 1);
    assert_eq!(contribution.segment(0).unwrap().data_length, 0);
    assert_eq!(state.total_passes(), 10);

    let initial = CodeBlockPacketState::new();
    state = initial;
    let mut reader = PacketBitReader::new(&[0xc0], &limits).unwrap();
    assert!(
        decode_code_block_contribution(
            &mut state,
            &mut inclusion,
            &mut zero_bitplanes,
            CodeBlockPacketContext {
                leaf_x: 0,
                leaf_y: 0,
                layer: 0,
                maximum_zero_bitplanes: 8,
                tier1_style: Tier1CodingStyle::default(),
            },
            &mut reader,
        )
        .is_err()
    );
    assert_eq!(state, initial);
}

#[test]
fn mixed_mode_routes_from_first_nonzero_segment_length() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0xc0).unwrap();

    let mut ht_inclusion = TagTree::new(1, 1, &limits).unwrap();
    let mut ht_zero_bitplanes = TagTree::new(1, 1, &limits).unwrap();
    let mut ht_state = CodeBlockPacketState::new();
    let ht_header = pack_packet_bits(&[true, true, false, true, false, false, true, false, false]);
    let mut ht_reader = PacketBitReader::new(&ht_header, &limits).unwrap();
    let ht = decode_code_block_contribution(
        &mut ht_state,
        &mut ht_inclusion,
        &mut ht_zero_bitplanes,
        CodeBlockPacketContext {
            leaf_x: 0,
            leaf_y: 0,
            layer: 0,
            maximum_zero_bitplanes: 3,
            tier1_style: style,
        },
        &mut ht_reader,
    )
    .unwrap()
    .unwrap();
    assert!(ht.high_throughput);
    assert_eq!(ht_state.high_throughput(), Some(true));
    assert_eq!(ht.data_length, 4);

    let mut legacy_inclusion = TagTree::new(1, 1, &limits).unwrap();
    let mut legacy_zero_bitplanes = TagTree::new(1, 1, &limits).unwrap();
    let mut legacy_state = CodeBlockPacketState::new();
    let legacy_header = pack_packet_bits(&[true, true, false, false, false, true, false]);
    let mut legacy_reader = PacketBitReader::new(&legacy_header, &limits).unwrap();
    let legacy = decode_code_block_contribution(
        &mut legacy_state,
        &mut legacy_inclusion,
        &mut legacy_zero_bitplanes,
        CodeBlockPacketContext {
            leaf_x: 0,
            leaf_y: 0,
            layer: 0,
            maximum_zero_bitplanes: 3,
            tier1_style: style,
        },
        &mut legacy_reader,
    )
    .unwrap()
    .unwrap();
    assert!(!legacy.high_throughput);
    assert_eq!(legacy_state.high_throughput(), Some(false));
    assert_eq!(legacy.data_length, 2);

    let mut extended_inclusion = TagTree::new(1, 1, &limits).unwrap();
    let mut extended_zero_bitplanes = TagTree::new(1, 1, &limits).unwrap();
    let mut extended_state = CodeBlockPacketState::new();
    let extended_header =
        pack_packet_bits(&[true, true, true, false, false, false, false, false, true]);
    let mut extended_reader = PacketBitReader::new(&extended_header, &limits).unwrap();
    let extended = decode_code_block_contribution(
        &mut extended_state,
        &mut extended_inclusion,
        &mut extended_zero_bitplanes,
        CodeBlockPacketContext {
            leaf_x: 0,
            leaf_y: 0,
            layer: 0,
            maximum_zero_bitplanes: 3,
            tier1_style: style,
        },
        &mut extended_reader,
    )
    .unwrap()
    .unwrap();
    assert!(!extended.high_throughput);
    assert_eq!(extended.new_passes, 2);
    assert_eq!(extended.segment(0).unwrap().passes, 2);
    assert_eq!(extended.data_length, 1);
}

#[test]
fn continues_one_legacy_coding_segment_across_quality_layers() {
    let limits = ResourceLimits::default();
    let contribution = |passes: u8, bytes: u32, first_inclusion: bool| {
        let mut segment_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
        let mut segment_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
        segment_passes[0] = passes;
        segment_lengths[0] = bytes;
        CodeBlockContribution {
            first_inclusion,
            zero_bitplanes: 2,
            new_passes: passes,
            data_length: bytes,
            high_throughput: false,
            segment_count: 1,
            segment_passes,
            segment_lengths,
        }
    };
    let mut whole = Tier1CodeBlockDecoder::new(
        1,
        1,
        9,
        crate::tier1::SubbandOrientation::Ll,
        Tier1CodingStyle::default(),
    )
    .unwrap();
    let mut layered = whole.clone();
    decode_code_block_contribution_body(
        &mut whole,
        &contribution(19, 2, true),
        &[0x04, 0x4f],
        &limits,
    )
    .unwrap();
    decode_code_block_contribution_body(&mut layered, &contribution(1, 1, true), &[0x04], &limits)
        .unwrap();
    let before = layered.plane().coefficients().to_vec();
    let tight = limits.with_maximum_work_units(22).unwrap();
    assert!(matches!(
        decode_code_block_contribution_body(
            &mut layered,
            &contribution(18, 1, false),
            &[0x4f],
            &tight,
        ),
        Err(DecodeError::LimitExceeded {
            resource: crate::Resource::WorkUnits,
            ..
        })
    ));
    assert_eq!(layered.plane().coefficients(), before);
    assert_eq!(layered.next_pass(), 1);
    decode_code_block_contribution_body(
        &mut layered,
        &contribution(18, 1, false),
        &[0x4f],
        &limits,
    )
    .unwrap();
    assert_eq!(layered.plane().coefficients(), whole.plane().coefficients());
    assert_eq!(layered.decoded_bytes(), 2);
    assert_eq!(layered.next_pass(), 19);
}

#[test]
fn decodes_bounded_code_block_contribution_body() {
    let limits = ResourceLimits::default();
    let mut segment_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    let mut segment_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    segment_passes[0] = 1;
    segment_lengths[0] = 2;
    let contribution = CodeBlockContribution {
        first_inclusion: true,
        zero_bitplanes: 0,
        new_passes: 1,
        data_length: 2,
        high_throughput: false,
        segment_count: 1,
        segment_passes,
        segment_lengths,
    };
    let mut decoder = Tier1CodeBlockDecoder::new(
        1,
        1,
        1,
        crate::tier1::SubbandOrientation::Ll,
        Tier1CodingStyle::default(),
    )
    .unwrap();
    let decoded =
        decode_code_block_contribution_body(&mut decoder, &contribution, &[0x01, 0xae], &limits)
            .unwrap();
    assert_eq!(
        decoded,
        CodeBlockBodyDecode {
            segments: 1,
            passes: 1,
            bytes: 2,
        }
    );
    assert!(decoder.is_complete());

    let mut truncated_decoder = Tier1CodeBlockDecoder::new(
        1,
        1,
        1,
        crate::tier1::SubbandOrientation::Ll,
        Tier1CodingStyle::default(),
    )
    .unwrap();
    assert!(
        decode_code_block_contribution_body(
            &mut truncated_decoder,
            &contribution,
            &[0x01],
            &limits,
        )
        .is_err()
    );
    assert_eq!(truncated_decoder.next_pass(), 0);
}

#[test]
fn decodes_ht_cleanup_with_packet_missing_msbs() {
    // Independently encoded one-pixel residuals from OpenJPH 0.33.0.
    for (body, magnitude) in [
        ([0x8e, 0x01, 0x07, 0x74, 0x00], 72),
        ([0xfc, 0x01, 0x07, 0x74, 0x00], 127),
    ] {
        let mut segment_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
        let mut segment_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
        segment_passes[0] = 1;
        segment_lengths[0] = 5;
        let contribution = CodeBlockContribution {
            first_inclusion: true,
            zero_bitplanes: 6,
            new_passes: 1,
            data_length: 5,
            high_throughput: true,
            segment_count: 1,
            segment_passes,
            segment_lengths,
        };
        let mut decoder = Tier1CodeBlockDecoder::new(
            1,
            1,
            7,
            crate::tier1::SubbandOrientation::Ll,
            Tier1CodingStyle::from_code_block_style(0x40).unwrap(),
        )
        .unwrap();
        decoder.set_ht_magnitude_bound(8).unwrap();
        decode_code_block_contribution_body(
            &mut decoder,
            &contribution,
            &body,
            &ResourceLimits::default(),
        )
        .unwrap();
        let coefficient = decoder.plane().coefficient(0, 0).unwrap();
        assert!(coefficient.significant);
        assert!(!coefficient.negative);
        assert_eq!(coefficient.magnitude, magnitude);
        assert_eq!(decoder.next_pass(), 1);
    }
}

#[test]
fn decodes_ht_embedded_precision_separately_from_value() {
    let mut segment_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    let mut segment_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    segment_passes[0] = 1;
    segment_lengths[0] = 8;
    let contribution = CodeBlockContribution {
        first_inclusion: true,
        zero_bitplanes: 6,
        new_passes: 1,
        data_length: 8,
        high_throughput: true,
        segment_count: 1,
        segment_passes,
        segment_lengths,
    };
    let mut decoder = Tier1CodeBlockDecoder::new(
        2,
        2,
        7,
        crate::tier1::SubbandOrientation::Ll,
        Tier1CodingStyle::from_code_block_style(0x40).unwrap(),
    )
    .unwrap();
    decoder.set_ht_magnitude_bound(8).unwrap();
    let body = [0x00, 0x82, 0xc0, 0xf1, 0x00, 0x43, 0x94, 0x00];
    decode_code_block_contribution_body(
        &mut decoder,
        &contribution,
        &body,
        &ResourceLimits::default(),
    )
    .unwrap();
    for (x, y, value) in [(0, 0, 1), (1, 0, 2), (0, 1, 3), (1, 1, 72)] {
        assert_eq!(decoder.plane().signed_coefficient(x, y).unwrap(), value);
    }
}

#[test]
fn ht_final_magnitude_refinement_truncates_the_integer_half_bin() {
    for (bit, magnitude) in [(0, 2), (1, 3)] {
        let mut segment_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
        let mut segment_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
        segment_passes[0] = 1;
        segment_passes[1] = 2;
        segment_lengths[0] = 4;
        segment_lengths[1] = 1;
        let contribution = CodeBlockContribution {
            first_inclusion: true,
            zero_bitplanes: 5,
            new_passes: 3,
            data_length: 5,
            high_throughput: true,
            segment_count: 2,
            segment_passes,
            segment_lengths,
        };
        let mut decoder = Tier1CodeBlockDecoder::new(
            1,
            1,
            7,
            crate::tier1::SubbandOrientation::Ll,
            Tier1CodingStyle::from_code_block_style(0x40).unwrap(),
        )
        .unwrap();
        decoder.set_ht_magnitude_bound(8).unwrap();
        let body = [0xfe, 0x00, 0x63, 0x00, bit];
        decode_code_block_contribution_body(
            &mut decoder,
            &contribution,
            &body,
            &ResourceLimits::default(),
        )
        .unwrap();
        assert_eq!(decoder.plane().signed_coefficient(0, 0).unwrap(), magnitude);
        assert!(decoder.plane().coefficient(0, 0).unwrap().refined);
    }
}

#[test]
fn routes_valid_ht_body_after_grouping_to_coefficient_boundary() {
    let limits = ResourceLimits::default();
    let mut segment_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    let mut segment_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    segment_passes[0] = 1;
    segment_lengths[0] = 3;
    segment_passes[1] = 1;
    segment_lengths[1] = 0;
    let contribution = CodeBlockContribution {
        first_inclusion: true,
        zero_bitplanes: 0,
        new_passes: 2,
        data_length: 3,
        high_throughput: true,
        segment_count: 2,
        segment_passes,
        segment_lengths,
    };
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut decoder = Tier1CodeBlockDecoder::new(1, 1, 3, SubbandOrientation::Ll, style).unwrap();
    let decoded = decode_code_block_contribution_body(
        &mut decoder,
        &contribution,
        &[0x00, 0x63, 0x00],
        &limits,
    )
    .unwrap();
    assert_eq!(decoded.passes, 2);
    assert_eq!(decoded.segments, 2);
    assert_eq!(decoder.next_pass(), 2);
    assert_eq!(decoder.plane().signed_coefficient(0, 0).unwrap(), -6);

    let mut malformed_decoder =
        Tier1CodeBlockDecoder::new(1, 1, 3, SubbandOrientation::Ll, style).unwrap();
    assert!(matches!(
        decode_code_block_contribution_body(
            &mut malformed_decoder,
            &contribution,
            &[0x01, 0x00, 0x00],
            &limits,
        ),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidCodeBlock,
            ..
        })
    ));
}

#[test]
fn routes_cleanup_only_ht_body_into_coefficient_plane() {
    let limits = ResourceLimits::default();
    let mut segment_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    let mut segment_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    segment_passes[0] = 1;
    segment_lengths[0] = 4;
    let contribution = CodeBlockContribution {
        first_inclusion: true,
        zero_bitplanes: 0,
        new_passes: 1,
        data_length: 4,
        high_throughput: true,
        segment_count: 1,
        segment_passes,
        segment_lengths,
    };
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut decoder = Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
    let decoded = decode_code_block_contribution_body(
        &mut decoder,
        &contribution,
        &[0xfe, 0x00, 0x63, 0x00],
        &limits,
    )
    .unwrap();
    assert_eq!(
        decoded,
        CodeBlockBodyDecode {
            segments: 1,
            passes: 1,
            bytes: 4,
        }
    );
    assert_eq!(decoder.plane().signed_coefficient(0, 0).unwrap(), 1);
    assert!(decoder.is_complete());
}

#[test]
fn routes_ht_refinement_across_layer_contributions() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut decoder = Tier1CodeBlockDecoder::new(1, 1, 2, SubbandOrientation::Ll, style).unwrap();

    let mut cleanup_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    let mut cleanup_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    cleanup_passes[0] = 1;
    cleanup_lengths[0] = 3;
    let cleanup = CodeBlockContribution {
        first_inclusion: true,
        zero_bitplanes: 0,
        new_passes: 1,
        data_length: 3,
        high_throughput: true,
        segment_count: 1,
        segment_passes: cleanup_passes,
        segment_lengths: cleanup_lengths,
    };
    decode_code_block_contribution_body(&mut decoder, &cleanup, &[0x00, 0x63, 0x00], &limits)
        .unwrap();
    assert_eq!(decoder.plane().signed_coefficient(0, 0).unwrap(), -3);

    let mut refinement_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    let refinement_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    refinement_passes[0] = 1;
    let significance = CodeBlockContribution {
        first_inclusion: false,
        zero_bitplanes: 0,
        new_passes: 1,
        data_length: 0,
        high_throughput: true,
        segment_count: 1,
        segment_passes: refinement_passes,
        segment_lengths: refinement_lengths,
    };
    decode_code_block_contribution_body(&mut decoder, &significance, &[], &limits).unwrap();
    assert_eq!(decoder.next_pass(), 2);

    let mut magnitude_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    magnitude_lengths[0] = 1;
    let magnitude = CodeBlockContribution {
        data_length: 1,
        segment_lengths: magnitude_lengths,
        ..significance
    };
    decode_code_block_contribution_body(&mut decoder, &magnitude, &[0x01], &limits).unwrap();
    assert_eq!(decoder.next_pass(), 3);
    assert_eq!(decoder.plane().signed_coefficient(0, 0).unwrap(), -3);
    assert_eq!(decoder.decoded_segments(), 3);
    assert_eq!(decoder.decoded_bytes(), 4);
}

#[test]
fn routes_placeholder_passes_before_first_ht_cleanup() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut decoder = Tier1CodeBlockDecoder::new(1, 1, 3, SubbandOrientation::Ll, style).unwrap();

    let mut placeholder_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    let placeholder_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    placeholder_passes[0] = 1;
    placeholder_passes[1] = 2;
    let placeholders = CodeBlockContribution {
        first_inclusion: true,
        zero_bitplanes: 0,
        new_passes: 3,
        data_length: 0,
        high_throughput: true,
        segment_count: 2,
        segment_passes: placeholder_passes,
        segment_lengths: placeholder_lengths,
    };
    decode_code_block_contribution_body(&mut decoder, &placeholders, &[], &limits).unwrap();
    assert_eq!(decoder.next_pass(), 3);
    assert_eq!(decoder.plane().signed_coefficient(0, 0).unwrap(), 0);

    let mut cleanup_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    let mut cleanup_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    cleanup_passes[0] = 1;
    cleanup_lengths[0] = 4;
    let cleanup = CodeBlockContribution {
        first_inclusion: false,
        zero_bitplanes: 0,
        new_passes: 1,
        data_length: 4,
        high_throughput: true,
        segment_count: 1,
        segment_passes: cleanup_passes,
        segment_lengths: cleanup_lengths,
    };
    decode_code_block_contribution_body(&mut decoder, &cleanup, &[0xfe, 0x00, 0x63, 0x00], &limits)
        .unwrap();
    assert_eq!(decoder.next_pass(), 4);
    assert_ne!(decoder.plane().signed_coefficient(0, 0).unwrap(), 0);
}

#[test]
fn enforces_singleht_and_routes_multiple_ht_sets_transactionally() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let cleanup_bytes = [0xfe, 0x00, 0x63, 0x00];
    let mut set_passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    let mut set_lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    set_passes[0] = 1;
    set_lengths[0] = 4;
    set_passes[1] = 2;
    let first_set = CodeBlockContribution {
        first_inclusion: true,
        zero_bitplanes: 0,
        new_passes: 3,
        data_length: 4,
        high_throughput: true,
        segment_count: 2,
        segment_passes: set_passes,
        segment_lengths: set_lengths,
    };
    let cleanup_only = CodeBlockContribution {
        new_passes: 1,
        segment_count: 1,
        ..first_set
    };
    let second_set = CodeBlockContribution {
        first_inclusion: false,
        zero_bitplanes: 0,
        new_passes: 1,
        data_length: 4,
        high_throughput: true,
        segment_count: 1,
        segment_passes: {
            let mut passes = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
            passes[0] = 1;
            passes
        },
        segment_lengths: {
            let mut lengths = [0; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
            lengths[0] = 4;
            lengths
        },
    };

    let mut single = Tier1CodeBlockDecoder::new(1, 1, 3, SubbandOrientation::Ll, style).unwrap();
    let mut cleanup_reference =
        Tier1CodeBlockDecoder::new(1, 1, 3, SubbandOrientation::Ll, style).unwrap();
    decode_code_block_contribution_body(
        &mut cleanup_reference,
        &cleanup_only,
        &cleanup_bytes,
        &limits,
    )
    .unwrap();
    decode_code_block_contribution_body(&mut single, &first_set, &cleanup_bytes, &limits).unwrap();
    assert_eq!(
        single.plane().signed_coefficient(0, 0).unwrap(),
        cleanup_reference.plane().signed_coefficient(0, 0).unwrap()
    );
    let before_pass = single.next_pass();
    let before_value = single.plane().signed_coefficient(0, 0).unwrap();
    assert!(
        decode_code_block_contribution_body(&mut single, &second_set, &cleanup_bytes, &limits,)
            .is_err()
    );
    assert_eq!(single.next_pass(), before_pass);
    assert_eq!(
        single.plane().signed_coefficient(0, 0).unwrap(),
        before_value
    );

    let mut multiple = Tier1CodeBlockDecoder::new(1, 1, 3, SubbandOrientation::Ll, style).unwrap();
    multiple.set_multiple_ht_sets_allowed(true);
    decode_code_block_contribution_body(&mut multiple, &first_set, &cleanup_bytes, &limits)
        .unwrap();
    decode_code_block_contribution_body(&mut multiple, &second_set, &cleanup_bytes, &limits)
        .unwrap();
    assert_eq!(multiple.next_pass(), 4);
    assert_eq!(multiple.decoded_segments(), 3);
}

#[test]
fn executes_retained_multi_code_block_packet_and_advances_by_prefix() {
    let limits = ResourceLimits::default();
    let mut data = two_block_first_layer_header();
    data.extend_from_slice(&[0x01, 0xae, 0x01, 0xae]);
    data.push(0);
    let tile_part = TilePartPayload {
        tile_index: 0,
        tile_part_index: 0,
        tile_part_count: 1,
        coding_style: coding_style(false, false),
        quantization: Quantization::reversible_default(coding_style(false, false)),
        component_coding_styles: component_styles(coding_style(false, false)).0,
        component_quantizations: component_styles(coding_style(false, false)).1,
        roi_shifts: crate::codestream::RoiShifts::none(),
        progression_changes: ProgressionChanges::none(),
        multiple_component_transform: None,
        part2_extensions: crate::codestream::Part2Extensions::default(),
        packet_lengths: crate::codestream::PacketLengths::none(),
        packed_packet_headers: crate::codestream::PackedPacketHeaders::none(),
        has_functional_header_marker: false,
        has_roi_marker: false,
        data: &data,
    };
    let mut states = [CodeBlockPacketState::new(), CodeBlockPacketState::new()];
    let mut inclusion = TagTree::new(2, 1, &limits).unwrap();
    let mut zero_bitplanes = TagTree::new(2, 1, &limits).unwrap();
    let contexts = [
        CodeBlockPacketContext {
            leaf_x: 0,
            leaf_y: 0,
            layer: 0,
            maximum_zero_bitplanes: 1,
            tier1_style: Tier1CodingStyle::default(),
        },
        CodeBlockPacketContext {
            leaf_x: 1,
            leaf_y: 0,
            layer: 0,
            maximum_zero_bitplanes: 1,
            tier1_style: Tier1CodingStyle::default(),
        },
    ];
    let first = Tier1CodeBlockDecoder::new(
        1,
        1,
        1,
        crate::tier1::SubbandOrientation::Ll,
        Tier1CodingStyle::default(),
    )
    .unwrap();
    let second = Tier1CodeBlockDecoder::new(
        1,
        1,
        1,
        crate::tier1::SubbandOrientation::Ll,
        Tier1CodingStyle::default(),
    )
    .unwrap();
    let mut decoders = [first, second];
    let decoded = decode_multi_code_block_packet(
        &tile_part,
        0,
        PacketCodeBlockExecution {
            states: &mut states,
            inclusion_tree: &mut inclusion,
            zero_bitplane_tree: &mut zero_bitplanes,
            contexts: &contexts,
            decoders: &mut decoders,
        },
        &limits,
    )
    .unwrap();
    assert_eq!(
        decoded,
        PacketBodyDecode {
            present: true,
            code_blocks: 2,
            contributions: 2,
            segments: 2,
            passes: 2,
            header_bytes: 3,
            body_bytes: 4,
            bytes_consumed: 7,
        }
    );
    assert!(states.iter().all(CodeBlockPacketState::included));
    assert!(decoders.iter().all(Tier1CodeBlockDecoder::is_complete));

    let absent = decode_multi_code_block_packet(
        &tile_part,
        usize::try_from(decoded.bytes_consumed).unwrap(),
        PacketCodeBlockExecution {
            states: &mut states,
            inclusion_tree: &mut inclusion,
            zero_bitplane_tree: &mut zero_bitplanes,
            contexts: &contexts,
            decoders: &mut decoders,
        },
        &limits,
    )
    .unwrap();
    assert_eq!(absent.bytes_consumed, 1);
    assert!(!absent.present);
    assert_eq!(absent.contributions, 0);
}

#[test]
fn empty_resolution_precinct_consumes_either_packet_present_flag() {
    let limits = ResourceLimits::default();
    for header in [0_u8, 0x80] {
        let data = [header];
        let style = coding_style(false, false);
        let tile = TilePartPayload {
            tile_index: 0,
            tile_part_index: 0,
            tile_part_count: 1,
            coding_style: style,
            quantization: Quantization::reversible_default(style),
            component_coding_styles: component_styles(style).0,
            component_quantizations: component_styles(style).1,
            roi_shifts: crate::codestream::RoiShifts::none(),
            progression_changes: ProgressionChanges::none(),
            multiple_component_transform: None,
            part2_extensions: crate::codestream::Part2Extensions::default(),
            packet_lengths: crate::codestream::PacketLengths::none(),
            packed_packet_headers: crate::codestream::PackedPacketHeaders::none(),
            has_functional_header_marker: false,
            has_roi_marker: false,
            data: &data,
        };
        let mut precinct = PacketPrecinctDecoder::new_subbands(
            0,
            1,
            0,
            Tier1CodingStyle::default(),
            Vec::new(),
            &limits,
        )
        .unwrap();
        let (decoded, consumed, packed) =
            decode_precinct_packet(&tile, 0, &[], 0, Some(1), 0, &mut precinct, true, &limits)
                .unwrap();
        assert_eq!(decoded.present, header != 0);
        assert_eq!(decoded.code_blocks, 0);
        assert_eq!(decoded.passes, 0);
        assert_eq!(consumed, 1);
        assert_eq!(packed, 0);
        assert!(
            decode_precinct_packet(&tile, 0, &[], 0, Some(2), 0, &mut precinct, true, &limits,)
                .is_err()
        );
    }
}

#[test]
fn validates_packet_markers_and_preflights_all_bodies() {
    let limits = ResourceLimits::default();
    let marker_data = [0xff, 0x91, 0, 4, 0x12, 0x34, 0, 0xff, 0x92];
    let marked_tile = TilePartPayload {
        tile_index: 0,
        tile_part_index: 0,
        tile_part_count: 1,
        coding_style: coding_style(true, true),
        quantization: Quantization::reversible_default(coding_style(true, true)),
        component_coding_styles: component_styles(coding_style(true, true)).0,
        component_quantizations: component_styles(coding_style(true, true)).1,
        roi_shifts: crate::codestream::RoiShifts::none(),
        progression_changes: ProgressionChanges::none(),
        multiple_component_transform: None,
        part2_extensions: crate::codestream::Part2Extensions::default(),
        packet_lengths: crate::codestream::PacketLengths::none(),
        packed_packet_headers: crate::codestream::PackedPacketHeaders::none(),
        has_functional_header_marker: false,
        has_roi_marker: false,
        data: &marker_data,
    };
    let mut states = [CodeBlockPacketState::new()];
    let mut inclusion = TagTree::new(1, 1, &limits).unwrap();
    let mut zero_bitplanes = TagTree::new(1, 1, &limits).unwrap();
    let contexts = [CodeBlockPacketContext {
        leaf_x: 0,
        leaf_y: 0,
        layer: 0,
        maximum_zero_bitplanes: 1,
        tier1_style: Tier1CodingStyle::default(),
    }];
    let decoder = Tier1CodeBlockDecoder::new(
        1,
        1,
        1,
        crate::tier1::SubbandOrientation::Ll,
        Tier1CodingStyle::default(),
    )
    .unwrap();
    let mut decoders = [decoder];
    let empty = decode_multi_code_block_packet(
        &marked_tile,
        0,
        PacketCodeBlockExecution {
            states: &mut states,
            inclusion_tree: &mut inclusion,
            zero_bitplane_tree: &mut zero_bitplanes,
            contexts: &contexts,
            decoders: &mut decoders,
        },
        &limits,
    )
    .unwrap();
    assert_eq!(empty.bytes_consumed, 9);
    assert_eq!(empty.header_bytes, 1);
    assert!(!empty.present);

    let mut truncated = two_block_first_layer_header();
    truncated.extend_from_slice(&[0x01, 0xae]);
    let truncated_tile = TilePartPayload {
        tile_index: 0,
        tile_part_index: 0,
        tile_part_count: 1,
        coding_style: coding_style(false, false),
        quantization: Quantization::reversible_default(coding_style(false, false)),
        component_coding_styles: component_styles(coding_style(false, false)).0,
        component_quantizations: component_styles(coding_style(false, false)).1,
        roi_shifts: crate::codestream::RoiShifts::none(),
        progression_changes: ProgressionChanges::none(),
        multiple_component_transform: None,
        part2_extensions: crate::codestream::Part2Extensions::default(),
        packet_lengths: crate::codestream::PacketLengths::none(),
        packed_packet_headers: crate::codestream::PackedPacketHeaders::none(),
        has_functional_header_marker: false,
        has_roi_marker: false,
        data: &truncated,
    };
    let mut states = [CodeBlockPacketState::new(), CodeBlockPacketState::new()];
    let mut inclusion = TagTree::new(2, 1, &limits).unwrap();
    let mut zero_bitplanes = TagTree::new(2, 1, &limits).unwrap();
    let contexts = [
        CodeBlockPacketContext {
            leaf_x: 0,
            leaf_y: 0,
            layer: 0,
            maximum_zero_bitplanes: 1,
            tier1_style: Tier1CodingStyle::default(),
        },
        CodeBlockPacketContext {
            leaf_x: 1,
            leaf_y: 0,
            layer: 0,
            maximum_zero_bitplanes: 1,
            tier1_style: Tier1CodingStyle::default(),
        },
    ];
    let first = Tier1CodeBlockDecoder::new(
        1,
        1,
        1,
        crate::tier1::SubbandOrientation::Ll,
        Tier1CodingStyle::default(),
    )
    .unwrap();
    let second = Tier1CodeBlockDecoder::new(
        1,
        1,
        1,
        crate::tier1::SubbandOrientation::Ll,
        Tier1CodingStyle::default(),
    )
    .unwrap();
    let mut decoders = [first, second];
    assert!(matches!(
        decode_multi_code_block_packet(
            &truncated_tile,
            0,
            PacketCodeBlockExecution {
                states: &mut states,
                inclusion_tree: &mut inclusion,
                zero_bitplane_tree: &mut zero_bitplanes,
                contexts: &contexts,
                decoders: &mut decoders,
            },
            &limits,
        ),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::Truncated,
            ..
        })
    ));
    assert!(decoders.iter().all(|decoder| decoder.next_pass() == 0));

    let limits = limits.with_maximum_code_blocks(1).unwrap();
    assert!(matches!(
        decode_multi_code_block_packet(
            &truncated_tile,
            0,
            PacketCodeBlockExecution {
                states: &mut states,
                inclusion_tree: &mut inclusion,
                zero_bitplane_tree: &mut zero_bitplanes,
                contexts: &contexts,
                decoders: &mut decoders,
            },
            &limits,
        ),
        Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlocks,
            ..
        })
    ));
}

#[test]
fn traverses_retained_tile_parts_and_preserves_precinct_state() {
    let limits = ResourceLimits::default();
    let mut first_data = pack_packet_bits(&[
        true,  // non-empty packet
        true,  // first inclusion
        true,  // zero bitplanes
        false, // one pass
        false, // no Lblock increment
        true, false, true, // five body bytes
    ]);
    first_data.extend_from_slice(&[0; 5]);
    let second_data = [0];
    let style = coding_style(false, false);
    let tile_parts = [
        TilePartPayload {
            tile_index: 3,
            tile_part_index: 0,
            tile_part_count: 2,
            coding_style: style,
            quantization: Quantization::reversible_default(style),
            component_coding_styles: component_styles(style).0,
            component_quantizations: component_styles(style).1,
            roi_shifts: crate::codestream::RoiShifts::none(),
            progression_changes: ProgressionChanges::none(),
            multiple_component_transform: None,
            part2_extensions: crate::codestream::Part2Extensions::default(),
            packet_lengths: crate::codestream::PacketLengths::none(),
            packed_packet_headers: crate::codestream::PackedPacketHeaders::none(),
            has_functional_header_marker: false,
            has_roi_marker: false,
            data: &first_data,
        },
        TilePartPayload {
            tile_index: 3,
            tile_part_index: 1,
            tile_part_count: 2,
            coding_style: style,
            quantization: Quantization::reversible_default(style),
            component_coding_styles: component_styles(style).0,
            component_quantizations: component_styles(style).1,
            roi_shifts: crate::codestream::RoiShifts::none(),
            progression_changes: ProgressionChanges::none(),
            multiple_component_transform: None,
            part2_extensions: crate::codestream::Part2Extensions::default(),
            packet_lengths: crate::codestream::PacketLengths::none(),
            packed_packet_headers: crate::codestream::PackedPacketHeaders::none(),
            has_functional_header_marker: false,
            has_roi_marker: false,
            data: &second_data,
        },
    ];
    let grid = PacketGrid::new(2, 1, 1, vec![1], &limits).unwrap();
    let decoder = Tier1CodeBlockDecoder::new(
        1,
        1,
        1,
        crate::tier1::SubbandOrientation::Ll,
        Tier1CodingStyle::default(),
    )
    .unwrap();
    let precinct = PacketPrecinctDecoder::new(
        PacketPrecinctGeometry {
            component: 0,
            resolution: 0,
            precinct: 0,
            code_blocks_across: 1,
            code_blocks_down: 1,
            maximum_zero_bitplanes: 1,
        },
        Tier1CodingStyle::default(),
        vec![decoder],
        &limits,
    )
    .unwrap();
    let mut precincts = [precinct];
    let decoded =
        decode_progression_tile_packets(&tile_parts, &grid, &mut precincts, &limits).unwrap();
    assert_eq!(
        decoded,
        TilePacketDecode {
            tile_index: 3,
            tile_parts: 2,
            packets: 2,
            present_packets: 1,
            contributions: 1,
            segments: 1,
            passes: 1,
            packet_header_bytes: 2,
            packet_body_bytes: 5,
            payload_bytes: 7,
        }
    );
    assert_eq!(precincts[0].coordinate(), (0, 0, 0));
    assert!(precincts[0].states()[0].included());
    assert_eq!(precincts[0].states()[0].total_passes(), 1);
    assert!(precincts[0].decoders()[0].is_complete());
}

#[test]
fn progression_traversal_requires_exact_payload_and_tile_part_sequence() {
    let limits = ResourceLimits::default();
    let style = coding_style(false, false);
    let grid = PacketGrid::new(2, 1, 1, vec![1], &limits).unwrap();
    let make_precinct = || {
        let decoder = Tier1CodeBlockDecoder::new(
            1,
            1,
            1,
            crate::tier1::SubbandOrientation::Ll,
            Tier1CodingStyle::default(),
        )
        .unwrap();
        PacketPrecinctDecoder::new(
            PacketPrecinctGeometry {
                component: 0,
                resolution: 0,
                precinct: 0,
                code_blocks_across: 1,
                code_blocks_down: 1,
                maximum_zero_bitplanes: 1,
            },
            Tier1CodingStyle::default(),
            vec![decoder],
            &limits,
        )
        .unwrap()
    };

    let trailing_data = [0, 0, 0];
    let trailing_part = [TilePartPayload {
        tile_index: 0,
        tile_part_index: 0,
        tile_part_count: 1,
        coding_style: style,
        quantization: Quantization::reversible_default(style),
        component_coding_styles: component_styles(style).0,
        component_quantizations: component_styles(style).1,
        roi_shifts: crate::codestream::RoiShifts::none(),
        progression_changes: ProgressionChanges::none(),
        multiple_component_transform: None,
        part2_extensions: crate::codestream::Part2Extensions::default(),
        packet_lengths: crate::codestream::PacketLengths::none(),
        packed_packet_headers: crate::codestream::PackedPacketHeaders::none(),
        has_functional_header_marker: false,
        has_roi_marker: false,
        data: &trailing_data,
    }];
    assert!(matches!(
        decode_progression_tile_packets(&trailing_part, &grid, &mut [make_precinct()], &limits,),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::TrailingData,
            ..
        })
    ));

    let truncated_data = [0];
    let truncated_part = [TilePartPayload {
        tile_index: 0,
        tile_part_index: 0,
        tile_part_count: 1,
        coding_style: style,
        quantization: Quantization::reversible_default(style),
        component_coding_styles: component_styles(style).0,
        component_quantizations: component_styles(style).1,
        roi_shifts: crate::codestream::RoiShifts::none(),
        progression_changes: ProgressionChanges::none(),
        multiple_component_transform: None,
        part2_extensions: crate::codestream::Part2Extensions::default(),
        packet_lengths: crate::codestream::PacketLengths::none(),
        packed_packet_headers: crate::codestream::PackedPacketHeaders::none(),
        has_functional_header_marker: false,
        has_roi_marker: false,
        data: &truncated_data,
    }];
    assert!(matches!(
        decode_progression_tile_packets(&truncated_part, &grid, &mut [make_precinct()], &limits,),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::Truncated,
            ..
        })
    ));

    let empty = [];
    let invalid_parts = [
        TilePartPayload {
            tile_index: 0,
            tile_part_index: 0,
            tile_part_count: 2,
            coding_style: style,
            quantization: Quantization::reversible_default(style),
            component_coding_styles: component_styles(style).0,
            component_quantizations: component_styles(style).1,
            roi_shifts: crate::codestream::RoiShifts::none(),
            progression_changes: ProgressionChanges::none(),
            multiple_component_transform: None,
            part2_extensions: crate::codestream::Part2Extensions::default(),
            packet_lengths: crate::codestream::PacketLengths::none(),
            packed_packet_headers: crate::codestream::PackedPacketHeaders::none(),
            has_functional_header_marker: false,
            has_roi_marker: false,
            data: &empty,
        },
        TilePartPayload {
            tile_index: 0,
            tile_part_index: 2,
            tile_part_count: 2,
            coding_style: style,
            quantization: Quantization::reversible_default(style),
            component_coding_styles: component_styles(style).0,
            component_quantizations: component_styles(style).1,
            roi_shifts: crate::codestream::RoiShifts::none(),
            progression_changes: ProgressionChanges::none(),
            multiple_component_transform: None,
            part2_extensions: crate::codestream::Part2Extensions::default(),
            packet_lengths: crate::codestream::PacketLengths::none(),
            packed_packet_headers: crate::codestream::PackedPacketHeaders::none(),
            has_functional_header_marker: false,
            has_roi_marker: false,
            data: &empty,
        },
    ];
    assert!(matches!(
        decode_progression_tile_packets(&invalid_parts, &grid, &mut [make_precinct()], &limits,),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidTilePart,
            ..
        })
    ));
}
