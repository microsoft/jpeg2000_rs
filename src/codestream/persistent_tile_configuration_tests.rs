use super::*;

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
                            u64::MAX,
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
