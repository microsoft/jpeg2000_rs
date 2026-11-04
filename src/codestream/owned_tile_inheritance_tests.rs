use super::super::persistent_tile_configuration::inherited_tile_owner;
use super::*;

type Owners = (
    ComponentQuantizations,
    ProgressionChanges,
    MctParameters,
    Part2Extensions,
);

fn owners(variant: usize) -> Owners {
    let payload = raw_owned_tile_part_fixture(variant % 4);
    let parameters = MctParameters {
        arrays: vec![MctArray {
            index: u8::MAX,
            kind: MctArrayKind::Dependency,
            numeric_format: MctNumericFormat::Float64,
            fraction_bits: u8::MAX,
            values: vec![i64::MIN, variant as i64, i64::MAX],
        }],
        records: vec![MctRecord {
            index: variant as u8,
            collections: vec![raw_mct_graph_reference(
                3,
                4,
                MctArrayKind::Offset,
                true,
                u8::MAX,
                u8::MAX,
            )],
        }],
        order: if variant == 0 {
            Vec::new()
        } else {
            vec![u8::MAX, variant as u8, u8::MAX]
        },
    };
    let quantizations = ComponentQuantizations {
        components: [0, 1, u16::MAX][variant % 3],
        quantizations: payload.component_quantizations.quantizations,
    };
    (
        quantizations,
        payload.progression_changes,
        parameters,
        payload.part2_extensions,
    )
}

#[test]
fn actual_inherited_owner_choice_requires_neither_clone_nor_copy_and_preserves_identity() {
    struct NonClone(Vec<u8>);
    let main = NonClone(vec![1, 3, 5]);
    let states = [None, Some(NonClone(vec![7, 11, 13]))];
    for index in [0, 1, 2, usize::MAX] {
        let actual = inherited_tile_owner(index, &main, &states);
        let expected = if index == 1 {
            states[1].as_ref().unwrap()
        } else {
            &main
        };
        assert!(core::ptr::eq(actual, expected));
        assert_eq!(actual.0, expected.0);
    }
}

#[test]
fn actual_four_owned_inheritance_preserves_raw_defaults_slots_tails_and_clone_independence() {
    let inherited: Vec<_> = (1..=3).map(owners).collect();
    let mut cases = 0;
    for main_variant in [0, 3] {
        let main = owners(main_variant);
        for geometry in 0..81 {
            let mut digits = geometry;
            let lengths: [usize; 4] = core::array::from_fn(|_| {
                let length = [0, 1, 3][digits % 3];
                digits /= 3;
                length
            });
            for index in [0, 1, 2, usize::MAX] {
                for mask in 0..16 {
                    let quantizations: Vec<_> = (0..lengths[0])
                        .map(|slot| (mask & 1 != 0).then(|| inherited[slot].0.clone()))
                        .collect();
                    let progression: Vec<_> = (0..lengths[1])
                        .map(|slot| (mask & 2 != 0).then(|| inherited[slot].1.clone()))
                        .collect();
                    let parameters: Vec<_> = (0..lengths[2])
                        .map(|slot| (mask & 4 != 0).then(|| inherited[slot].2.clone()))
                        .collect();
                    let extensions: Vec<_> = (0..lengths[3])
                        .map(|slot| (mask & 8 != 0).then(|| inherited[slot].3.clone()))
                        .collect();
                    let expected_q = quantizations
                        .get(index)
                        .and_then(Option::as_ref)
                        .unwrap_or(&main.0);
                    let expected_p = progression
                        .get(index)
                        .and_then(Option::as_ref)
                        .unwrap_or(&main.1);
                    let expected_m = parameters
                        .get(index)
                        .and_then(Option::as_ref)
                        .unwrap_or(&main.2);
                    let expected_e = extensions
                        .get(index)
                        .and_then(Option::as_ref)
                        .unwrap_or(&main.3);
                    let selected_q = inherited_tile_owner(index, &main.0, &quantizations);
                    let selected_p = inherited_tile_owner(index, &main.1, &progression);
                    let selected_m = inherited_tile_owner(index, &main.2, &parameters);
                    let selected_e = inherited_tile_owner(index, &main.3, &extensions);
                    assert!(core::ptr::eq(selected_q, expected_q));
                    assert!(core::ptr::eq(selected_p, expected_p));
                    assert!(core::ptr::eq(selected_m, expected_m));
                    assert!(core::ptr::eq(selected_e, expected_e));
                    let copied_q = selected_q.clone();
                    let copied_p = selected_p.clone();
                    let copied_m = selected_m.clone();
                    let copied_e = selected_e.clone();
                    assert_eq!(&copied_q, expected_q);
                    assert_eq!(&copied_p, expected_p);
                    assert_eq!(&copied_m, expected_m);
                    assert_eq!(&copied_e, expected_e);
                    if !expected_q.quantizations.is_empty() {
                        assert_ne!(
                            copied_q.quantizations.as_ptr(),
                            expected_q.quantizations.as_ptr()
                        );
                    }
                    if !expected_p.records.is_empty() {
                        assert_ne!(copied_p.records.as_ptr(), expected_p.records.as_ptr());
                    }
                    assert_ne!(copied_m.arrays.as_ptr(), expected_m.arrays.as_ptr());
                    assert_ne!(
                        copied_m.arrays[0].values.as_ptr(),
                        expected_m.arrays[0].values.as_ptr()
                    );
                    assert_ne!(copied_m.records.as_ptr(), expected_m.records.as_ptr());
                    assert_ne!(
                        copied_m.records[0].collections[0].input_components.as_ptr(),
                        expected_m.records[0].collections[0]
                            .input_components
                            .as_ptr(),
                    );
                    if !expected_e.component_bit_depths.is_empty() {
                        assert_ne!(
                            copied_e.component_bit_depths.as_ptr(),
                            expected_e.component_bit_depths.as_ptr()
                        );
                    }
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 10_368);
}

#[test]
fn actual_layout_owned_inheritance_retains_all_four_owner_families_between_parts() {
    let first = [
        segment(COD, &[0, 0, 0, 3, 0, 0, 2, 2, 0, 1]),
        segment(QCD, &[0x40, 0]),
        poc(&[[0, 0, 0, 3, 1, 1, 0]]),
        segment(DFS, &[0, 1, 1, 0x40]),
        mct_i16(1, 1, &[3]),
        mct_i16(200, 1, &[9]),
        mcc(7, 1, true, 1, 0),
        mco(&[7]),
    ];
    let second = [mcc(8, 1, true, 200, 0), mco(&[8])];
    let bytes = two_part_codestream(&first, &second);
    let limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(layout.tile_parts.len(), 2);
    for (index, matrix) in [(0, 3), (1, 9)] {
        let payload = &layout.tile_parts[index];
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
        assert_eq!(payload.part2_extensions.decomposition_structures.len(), 1);
        assert_eq!(
            payload.part2_extensions.decomposition_structures[0].index,
            1
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
            &[matrix],
        );
        assert_eq!(payload.data, &[0]);
    }
}
