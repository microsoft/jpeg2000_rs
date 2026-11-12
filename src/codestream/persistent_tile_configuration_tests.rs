use super::*;

pub(super) fn interleaved_persistent_parts(last_roi: Option<u8>) -> (Vec<u8>, Vec<usize>) {
    let mut bytes = SOC.to_be_bytes().to_vec();
    let mut size = siz();
    size[22..26].copy_from_slice(&32_u32.to_be_bytes());
    bytes.extend(size);
    bytes.extend(segment(COD, &[0, 0, 0, 2, 0, 0, 2, 2, 0, 1]));
    bytes.extend(segment(QCD, &[0, 0]));
    let mut starts = Vec::new();
    for (part, tile) in [0_u16, 1, 0, 1, 0, 1].into_iter().enumerate() {
        let start = bytes.len();
        starts.push(start);
        let mut sot = tile.to_be_bytes().to_vec();
        sot.extend(0_u32.to_be_bytes());
        sot.extend([u8::try_from(part / 2).unwrap(), 3]);
        bytes.extend(segment(SOT, &sot));
        if part < 2 {
            let layers = if tile == 0 { 3 } else { 5 };
            bytes.extend(segment(COD, &[0, 0, 0, layers, 0, 0, 2, 2, 0, 1]));
            bytes.extend(segment(QCD, &[if tile == 0 { 0x40 } else { 0x80 }, 0]));
            bytes.extend(segment(RGN, &[0, 0, if tile == 0 { 7 } else { 9 }]));
            bytes.extend(poc(&[[0, 0, 0, layers, 1, 1, 0]]));
            bytes.extend(segment(DFS, &[0, tile as u8 + 1, 1, 0x40]));
            bytes.extend(mct_i16(1, 1, &[1, if tile == 0 { 4 } else { 8 }]));
            bytes.extend(mct_i16(200, 1, &[1, if tile == 0 { 16 } else { 32 }]));
            bytes.extend(mcc(7, 1, true, 1, 0));
            bytes.extend(mco(&[7]));
        } else if part == 2 {
            bytes.extend(segment(COD, &[0, 0, 0, 3, 0, 0, 3, 2, 0, 1]));
            bytes.extend(segment(QCD, &[0x60, 0]));
            bytes.extend(mcc(8, 1, true, 200, 0));
            bytes.extend(mco(&[8]));
        } else if part == 5 {
            if let Some(shift) = last_roi {
                bytes.extend(segment(RGN, &[0, 0, shift]));
            }
            bytes.extend(mcc(8, 1, true, 200, 0));
            bytes.extend(mco(&[8]));
        }
        bytes.extend(SOD.to_be_bytes());
        bytes.push(u8::try_from(part).unwrap());
        let length = u32::try_from(bytes.len() - start).unwrap();
        bytes[start + 6..start + 10].copy_from_slice(&length.to_be_bytes());
    }
    bytes.extend(EOC.to_be_bytes());
    (bytes, starts)
}

#[test]
fn actual_persistent_fold_keeps_all_eight_owners_per_tile_and_appends_source_payloads() {
    let (bytes, starts) = interleaved_persistent_parts(None);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(layout.info.tile_parts, 6);
    assert_eq!(layout.tile_parts.len(), 6);
    assert_eq!(layout.info.consumed_bytes, bytes.len() as u64);
    for (part, layers, guard, matrix) in [
        (0, 3, 2, 4),
        (1, 5, 4, 8),
        (2, 3, 3, 16),
        (3, 5, 4, 8),
        (4, 3, 3, 16),
        (5, 5, 4, 32),
    ] {
        let payload = &layout.tile_parts[part];
        let tile = part % 2;
        assert_eq!(payload.tile_index, tile as u16);
        assert_eq!(payload.tile_part_index, (part / 2) as u8);
        assert_eq!(payload.tile_part_count, 3);
        assert_eq!(payload.coding_style.layers, layers);
        assert_eq!(
            payload.coding_style.code_block_width,
            if part == 2 || part == 4 { 32 } else { 16 },
        );
        assert_eq!(
            payload
                .component_coding_styles
                .style(0)
                .unwrap()
                .code_block_width,
            payload.coding_style.code_block_width,
        );
        assert_eq!(
            payload.component_coding_styles.style(0).unwrap().layers,
            layers
        );
        assert_eq!(payload.quantization.guard_bits, guard);
        assert_eq!(
            payload
                .component_quantizations
                .quantization(0)
                .unwrap()
                .guard_bits,
            guard,
        );
        assert_eq!(
            payload.roi_shifts.shift(0).unwrap(),
            if tile == 0 { 7 } else { 9 }
        );
        assert_eq!(payload.progression_changes.records.len(), 1);
        assert_eq!(
            payload.progression_changes.records[0].layer_end,
            if tile == 0 { 3 } else { 5 },
        );
        assert_eq!(payload.part2_extensions.decomposition_structures.len(), 1);
        assert_eq!(
            payload.part2_extensions.decomposition_structures[0].index,
            tile as u8 + 1,
        );
        assert_eq!(
            payload
                .multiple_component_transform
                .as_ref()
                .unwrap()
                .stages()[0]
                .collections()[0]
                .matrix()
                .unwrap()
                .values(),
            &[1, matrix],
        );
        assert_eq!(payload.has_roi_marker, part < 2);
        let next = if part + 1 < starts.len() {
            starts[part + 1]
        } else {
            bytes.len() - 2
        };
        assert_eq!(payload.data, &[part as u8]);
        assert!(core::ptr::eq(
            payload.data.as_ptr(),
            bytes[next - 1..].as_ptr()
        ));
    }
}

#[test]
fn actual_persistent_fold_rejects_late_tile_roi_change_before_trailing_data() {
    let limits = ResourceLimits::default();
    let (valid, _) = interleaved_persistent_parts(Some(9));
    assert_eq!(parse_layout(&valid, &limits).unwrap().tile_parts.len(), 6);
    let (mut invalid, starts) = interleaved_persistent_parts(Some(8));
    invalid.extend([17, 19]);
    assert_eq!(
        parse_layout(&invalid, &limits).unwrap_err(),
        DecodeError::malformed(starts[5] as u64, MalformedKind::InvalidRegionOfInterest),
    );
}

#[test]
fn actual_inherited_selection_preserves_raw_fallbacks_indexes_owners_and_frames() {
    let input = [11, 13];
    let limits = ResourceLimits::HARDENED;
    let parser = Parser {
        input: &input,
        limits: &limits,
        position: 17,
        work_units: u64::MAX,
        packet_length_bytes: 97,
        packet_lengths: 101,
    };
    let mut cases = 0;
    for main_count in [0, u16::MAX] {
        let main = raw_owned_tile_part_fixture(3);
        let main_components = ComponentCodingStyles {
            components: main_count,
            styles: core::array::from_fn(|index| raw_resolution_style(index as u8, index)),
        };
        for geometry in 0..243 {
            let mut digits = geometry;
            let lengths: [usize; 5] = core::array::from_fn(|_| {
                let length = [0, 1, 3][digits % 3];
                digits /= 3;
                length
            });
            let payloads: Vec<_> = (0..lengths[4])
                .map(|index| {
                    let mut payload = raw_owned_tile_part_fixture(index);
                    payload.tile_index = u16::MAX;
                    payload.component_coding_styles.components =
                        if index.is_multiple_of(2) { 0 } else { u16::MAX };
                    payload.component_coding_styles.styles[MAX_COMPONENTS - 1] =
                        raw_resolution_style(17, index + 31);
                    payload
                })
                .collect();
            for index in [0, 1, 2, usize::MAX] {
                for pattern in 0..5 {
                    let mut state = state([lengths[0], lengths[1], lengths[2], lengths[3], 0, 0]);
                    for (slot, roi) in state.roi.iter_mut().enumerate() {
                        *roi = if (pattern + slot).is_multiple_of(2) {
                            None
                        } else {
                            Some(RoiShifts {
                                shifts: core::array::from_fn(|shift| (shift + slot) as u8),
                            })
                        };
                    }
                    for part in &mut state.parts {
                        *part = match pattern {
                            0 => None,
                            1 => Some(0),
                            2 => Some(lengths[4].saturating_sub(1)),
                            3 => Some(usize::MAX),
                            _ => Some(index),
                        };
                    }
                    let before = state.clone();
                    let payloads_before = payloads.clone();
                    let previous = before.roi.get(index).copied().flatten();
                    let part = before.parts.get(index).copied().flatten();
                    let expected =
                        if index >= lengths[0] || part.is_some_and(|part| part >= lengths[4]) {
                            Err(DecodeError::malformed(17, MalformedKind::InvalidTilePart))
                        } else {
                            Ok((
                                previous,
                                previous.unwrap_or(main.roi_shifts),
                                before
                                    .styles
                                    .get(index)
                                    .copied()
                                    .flatten()
                                    .unwrap_or(main.coding_style),
                                before
                                    .quantizations
                                    .get(index)
                                    .copied()
                                    .flatten()
                                    .unwrap_or(main.quantization),
                                part.map_or(main_components, |part| {
                                    payloads[part].component_coding_styles
                                }),
                            ))
                        };
                    let result = parser.select_inherited_tile_configuration(
                        index,
                        &main.roi_shifts,
                        &main.coding_style,
                        &main.quantization,
                        &main_components,
                        &state.roi,
                        &state.styles,
                        &state.quantizations,
                        &state.parts,
                        &payloads,
                    );
                    assert_eq!(
                        result, expected,
                        "geometry={lengths:?}, index={index}, pattern={pattern}"
                    );
                    if let Ok(value) = &result {
                        fn copy_only<T: Copy>(_: &T) {}
                        copy_only(value);
                    }
                    assert_eq!(state, before);
                    assert_eq!(payloads, payloads_before);
                    assert_eq!(parser.position, 17);
                    assert_eq!(parser.work_units, u64::MAX);
                    assert_eq!(parser.packet_length_bytes, 97);
                    assert_eq!(parser.packet_lengths, 101);
                    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
                    assert!(core::ptr::eq(parser.limits, &limits));
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 9_720);
}

#[test]
fn actual_inherited_selection_returns_independent_copy_of_every_physical_style() {
    let limits = ResourceLimits::default();
    let parser = new_parser(&[], &limits).unwrap();
    let mut main = raw_owned_tile_part_fixture(0);
    let mut payload = raw_owned_tile_part_fixture(3);
    payload.component_coding_styles.components = 0;
    payload.component_coding_styles.styles[MAX_COMPONENTS - 1] = raw_resolution_style(255, 31);
    let state = state([1; 6]);
    let selected = parser
        .select_inherited_tile_configuration(
            0,
            &main.roi_shifts,
            &main.coding_style,
            &main.quantization,
            &main.component_coding_styles,
            &state.roi,
            &state.styles,
            &state.quantizations,
            &[Some(0)],
            core::slice::from_ref(&payload),
        )
        .unwrap();
    let before = payload.component_coding_styles;
    payload.component_coding_styles.styles[MAX_COMPONENTS - 1] = main.coding_style;
    main.component_coding_styles.components = 17;
    assert_ne!(payload.component_coding_styles, before);
    assert_eq!(main.component_coding_styles.components, 17);
    assert_eq!(selected.4, before);
    assert_eq!(selected.4.components, 0);
    assert_eq!(
        selected.4.styles[MAX_COMPONENTS - 1].decomposition_levels,
        255
    );
}

#[test]
fn actual_layout_inherits_latest_component_owner_not_tile_index_or_first_part() {
    let first = [
        segment(COD, &[0, 0, 0, 3, 0, 0, 2, 2, 0, 1]),
        segment(QCD, &[0x40, 0]),
    ];
    let second = [
        segment(COD, &[0, 0, 0, 4, 0, 0, 2, 2, 0, 1]),
        segment(QCD, &[0x60, 0]),
    ];
    let mut bytes = two_part_codestream(&first, &second);
    let starts: Vec<_> = bytes
        .windows(2)
        .enumerate()
        .filter_map(|(offset, pair)| (pair == SOT.to_be_bytes()).then_some(offset))
        .collect();
    assert_eq!(starts.len(), 2);
    for start in starts {
        bytes[start + 11] = 3;
    }
    bytes.truncate(bytes.len() - 2);
    bytes.extend(segment(SOT, &[0, 0, 0, 0, 0, 15, 2, 3]));
    bytes.extend(SOD.to_be_bytes());
    bytes.push(0);
    bytes.extend(EOC.to_be_bytes());
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(layout.tile_parts.len(), 3);
    for (index, expected_layers, expected_guard) in [(0, 3, 2), (1, 4, 3), (2, 4, 3)] {
        let payload = &layout.tile_parts[index];
        assert_eq!(payload.tile_part_index, index as u8);
        assert_eq!(payload.tile_part_count, 3);
        assert_eq!(payload.coding_style.layers, expected_layers);
        assert_eq!(
            payload.component_coding_styles.style(0).unwrap().layers,
            expected_layers
        );
        assert_eq!(payload.quantization.guard_bits, expected_guard);
        assert_eq!(payload.data, &[0]);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct State {
    roi: Vec<Option<RoiShifts>>,
    styles: Vec<Option<CodingStyle>>,
    quantizations: Vec<Option<Quantization>>,
    parts: Vec<Option<usize>>,
    owners: Vec<Option<ComponentQuantizations>>,
    progression: Vec<Option<ProgressionChanges>>,
}

fn slots<T: Clone>(length: usize, value: T) -> Vec<Option<T>> {
    (0..length)
        .map(|index| (index != 1).then(|| value.clone()))
        .collect()
}

fn state(lengths: [usize; 6]) -> State {
    let old = raw_owned_tile_part_fixture(0);
    State {
        roi: slots(lengths[0], RoiShifts::none()),
        styles: slots(lengths[1], raw_resolution_style(0, 0)),
        quantizations: slots(
            lengths[2],
            raw_subband_quantization(QuantizationStyle::None, 0, 0),
        ),
        parts: slots(lengths[3], 31),
        owners: slots(lengths[4], old.component_quantizations),
        progression: slots(lengths[5], ProgressionChanges::none()),
    }
}

fn commit(
    parser: &Parser<'_>,
    state: &mut State,
    start: usize,
    index: usize,
    payload_index: usize,
    previous: Option<RoiShifts>,
    payload: &TilePartPayload<'_>,
) -> Result<(), DecodeError> {
    parser.commit_persistent_tile_configuration(
        start,
        index,
        payload_index,
        previous,
        payload,
        &mut state.roi,
        &mut state.styles,
        &mut state.quantizations,
        &mut state.parts,
        &mut state.owners,
        &mut state.progression,
    )
}

#[test]
fn actual_roi_equality_compares_every_physical_shift() {
    let original = RoiShifts {
        shifts: core::array::from_fn(|index| index as u8),
    };
    assert!(original.equals(&original));
    for index in 0..MAX_COMPONENTS {
        let mut changed = original;
        changed.shifts[index] ^= 0xff;
        assert!(!original.equals(&changed), "physical index {index}");
        assert!(!changed.equals(&original), "physical index {index}");
    }
}

#[test]
fn actual_persistent_configuration_raw_geometry_first_errors_and_partial_frames() {
    let input = [11, 13, 17];
    let limits = ResourceLimits::HARDENED;
    let parser = Parser {
        input: &input,
        limits: &limits,
        position: 13,
        work_units: u64::MAX,
        packet_length_bytes: 97,
        packet_lengths: 101,
    };
    let mut cases = 0;
    for variant in 0..4 {
        let payload = raw_owned_tile_part_fixture(variant);
        let payload_before = payload.clone();
        let mut different_roi = payload.roi_shifts;
        different_roi.shifts[MAX_COMPONENTS - 1] ^= 1;
        for geometry in 0..729 {
            let mut digits = geometry;
            let lengths = core::array::from_fn(|_| {
                let length = [0, 1, 3][digits % 3];
                digits /= 3;
                length
            });
            for index in [0, 1, 2, usize::MAX] {
                for previous in [None, Some(payload.roi_shifts), Some(different_roi)] {
                    let mut actual = state(lengths);
                    let mut expected = actual.clone();
                    let inconsistent =
                        previous.is_some_and(|roi| roi.shifts != payload.roi_shifts.shifts);
                    let prefix = if inconsistent {
                        0
                    } else {
                        lengths
                            .iter()
                            .position(|length| index >= *length)
                            .unwrap_or(6)
                    };
                    if prefix > 0 {
                        expected.roi[index] = Some(payload.roi_shifts);
                    }
                    if prefix > 1 {
                        expected.styles[index] = Some(payload.coding_style);
                    }
                    if prefix > 2 {
                        expected.quantizations[index] = Some(payload.quantization);
                    }
                    if prefix > 3 {
                        expected.parts[index] = Some(usize::MAX);
                    }
                    if prefix > 4 {
                        expected.owners[index] = Some(payload.component_quantizations.clone());
                    }
                    if prefix > 5 {
                        expected.progression[index] = Some(payload.progression_changes.clone());
                    }
                    let expected_result = if inconsistent {
                        Err(DecodeError::malformed(
                            usize::MAX as u64,
                            MalformedKind::InvalidRegionOfInterest,
                        ))
                    } else if prefix != 6 {
                        Err(DecodeError::malformed(13, MalformedKind::InvalidTilePart))
                    } else {
                        Ok(())
                    };
                    assert_eq!(
                        commit(
                            &parser,
                            &mut actual,
                            usize::MAX,
                            index,
                            usize::MAX,
                            previous,
                            &payload,
                        ),
                        expected_result,
                        "geometry={lengths:?}, index={index}, previous={previous:?}",
                    );
                    assert_eq!(actual, expected);
                    assert_eq!(payload, payload_before);
                    assert_eq!(parser.position, 13);
                    assert_eq!(parser.work_units, u64::MAX);
                    assert_eq!(parser.packet_length_bytes, 97);
                    assert_eq!(parser.packet_lengths, 101);
                    assert!(core::ptr::eq(parser.input.as_ptr(), input.as_ptr()));
                    assert!(core::ptr::eq(parser.limits, &limits));
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 34_992);
}

#[test]
fn actual_persistent_configuration_clones_only_stored_owned_fields_without_aliases() {
    let limits = ResourceLimits::default();
    let parser = new_parser(&[], &limits).unwrap();
    let mut payload = raw_owned_tile_part_fixture(3);
    let before = payload.clone();
    let mut state = state([3; 6]);
    commit(&parser, &mut state, 17, 1, 97, None, &payload).unwrap();
    let quantizations = state.owners[1].as_ref().unwrap();
    assert_eq!(quantizations.components, u16::MAX);
    assert_eq!(quantizations.quantizations.len(), 3);
    assert_ne!(
        quantizations.quantizations.as_ptr(),
        payload.component_quantizations.quantizations.as_ptr(),
    );
    assert_ne!(
        state.progression[1].as_ref().unwrap().records.as_ptr(),
        payload.progression_changes.records.as_ptr(),
    );
    payload.component_quantizations.quantizations[2].guard_bits ^= 1;
    payload.progression_changes.records[0].layer_end = 17;
    assert_eq!(
        state.owners[1].as_ref().unwrap(),
        &before.component_quantizations,
    );
    assert_eq!(
        state.progression[1].as_ref().unwrap(),
        &before.progression_changes,
    );
    assert_eq!(state.parts, vec![Some(31), Some(97), Some(31)]);
}

#[test]
fn actual_layout_persists_configuration_through_real_parts_and_rejects_roi_change() {
    let first = [
        segment(COD, &[0, 0, 0, 3, 0, 0, 2, 2, 0, 1]),
        segment(QCD, &[0x40, 0]),
        poc(&[[0, 0, 0, 3, 1, 1, 0]]),
        segment(RGN, &[0, 0, 7]),
    ];
    let bytes = two_part_codestream(&first, &[]);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(layout.tile_parts.len(), 2);
    for (index, payload) in layout.tile_parts.iter().enumerate() {
        assert_eq!(payload.tile_part_index, index as u8);
        assert_eq!(payload.coding_style.layers, 3);
        assert_eq!(payload.quantization.guard_bits, 2);
        assert_eq!(payload.component_coding_styles.style(0).unwrap().layers, 3);
        assert_eq!(
            payload
                .component_quantizations
                .quantization(0)
                .unwrap()
                .guard_bits,
            2
        );
        assert_eq!(payload.progression_changes.records.len(), 1);
        assert_eq!(payload.progression_changes.records[0].layer_end, 3);
        assert_eq!(payload.roi_shifts.shift(0).unwrap(), 7);
        assert_eq!(payload.data, &[0]);
        let offset = payload.data.as_ptr() as usize - bytes.as_ptr() as usize;
        assert!(offset < bytes.len());
        assert!(core::ptr::eq(
            payload.data.as_ptr(),
            bytes[offset..].as_ptr()
        ));
    }
    let changed = two_part_codestream(&first, &[segment(RGN, &[0, 0, 8])]);
    let second_start = changed
        .windows(2)
        .enumerate()
        .filter_map(|(offset, pair)| (pair == SOT.to_be_bytes()).then_some(offset))
        .nth(1)
        .unwrap();
    assert_eq!(
        parse_layout(&changed, &limits).unwrap_err(),
        DecodeError::malformed(second_start as u64, MalformedKind::InvalidRegionOfInterest),
    );
}
