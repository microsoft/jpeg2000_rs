use super::*;

#[test]
fn actual_raw_main_header_initializers_preserve_all_physical_empty_owners() {
    let roi = super::super::quantization::new_roi_shifts();
    assert_eq!(roi, RoiShifts::none());
    assert_eq!(roi.shifts, [0; MAX_COMPONENTS]);
    let progression = super::super::coding_style::new_progression_changes();
    assert_eq!(progression, ProgressionChanges::none());
    assert_eq!(progression.records.len(), 0);
    assert_eq!(progression.records.capacity(), 0);
    let extensions = super::super::extensions::new_part2_extensions();
    assert_eq!(extensions, Part2Extensions::default());
    assert_eq!(extensions.metadata_bytes, 0);
    for (length, capacity) in [
        (
            extensions.decomposition_structures.len(),
            extensions.decomposition_structures.capacity(),
        ),
        (
            extensions.arbitrary_decompositions.len(),
            extensions.arbitrary_decompositions.capacity(),
        ),
        (
            extensions.nonlinear_transforms.len(),
            extensions.nonlinear_transforms.capacity(),
        ),
        (
            extensions.component_bit_depths.len(),
            extensions.component_bit_depths.capacity(),
        ),
        (
            extensions.arbitrary_kernels.len(),
            extensions.arbitrary_kernels.capacity(),
        ),
        (
            extensions.component_registrations.len(),
            extensions.component_registrations.capacity(),
        ),
        (
            extensions.tile_part_lengths.len(),
            extensions.tile_part_lengths.capacity(),
        ),
    ] {
        assert_eq!((length, capacity), (0, 0));
    }
}

#[test]
fn actual_raw_main_header_result_composes_all_deferred_component_orders_and_geometry() {
    let limits = ResourceLimits::default();
    let mut cases = 0;
    for components in [1_u16, 2, 64] {
        for precision in [1_u8, 8, 38] {
            for signed in [false, true] {
                for shift in [0_u8, 1, 255] {
                    let [cod, qcd] = baseline_headers();
                    let fields = [
                        cod,
                        qcd,
                        segment(COC, &[0, 0, 0, 2, 2, 0, 1]),
                        segment(QCC, &[0, 0, 0]),
                    ];
                    for first in 0..4 {
                        for second in 0..4 {
                            for third in 0..4 {
                                for fourth in 0..4 {
                                    let order = [first, second, third, fourth];
                                    if order
                                        .iter()
                                        .enumerate()
                                        .any(|(index, item)| order[..index].contains(item))
                                    {
                                        continue;
                                    }
                                    let mut headers: Vec<_> =
                                        order.map(|index| fields[index].clone()).into();
                                    headers.push(segment(RGN, &[0, 0, shift]));
                                    let mut depths = components.to_be_bytes().to_vec();
                                    depths.resize(
                                        usize::from(components) + 2,
                                        precision - 1 + if signed { 0x80 } else { 0 },
                                    );
                                    headers.push(segment(CBD, &depths));
                                    let registrations: Vec<_> = (0..components)
                                        .flat_map(|component| {
                                            [component.to_be_bytes(), (component + 1).to_be_bytes()]
                                                .concat()
                                        })
                                        .collect();
                                    headers.push(segment(CRG, &registrations));
                                    headers.push(segment(CAP, &[0x80, 0, 0, 0, 0xde, 0xad]));
                                    headers.push(segment(PRF, &[0x12, 0x34, 0x56, 0x78]));
                                    headers.push(segment(COM, &[0, 1, shift, precision]));
                                    let bytes =
                                        codestream_with_headers(components, &headers, &[], &[]);
                                    let layout = parse_layout(&bytes, &limits).unwrap();
                                    let info = &layout.info;
                                    assert_eq!(info.main_header_segments, 11);
                                    assert_eq!(info.image_size.components, components);
                                    assert_eq!(info.image_size.uniform_bit_depth, Some(precision));
                                    assert_eq!(info.image_size.uniform_signed, Some(signed));
                                    for component in 0..components {
                                        let actual = info.image_size.component(component).unwrap();
                                        assert_eq!(
                                            (actual.precision, actual.signed),
                                            (precision, signed)
                                        );
                                        assert_eq!(actual.x_registration, component);
                                        assert_eq!(actual.y_registration, component + 1);
                                        assert_eq!(
                                            info.roi_shifts.shift(component).unwrap(),
                                            if component == 0 { shift } else { 0 }
                                        );
                                    }
                                    assert!(
                                        info.image_size.component_info[usize::from(components)..]
                                            .iter()
                                            .all(|value| *value == ComponentInfo::default())
                                    );
                                    let caps = info.profile.extended_capabilities.as_ref().unwrap();
                                    assert_eq!(caps.p_cap, 0x8000_0000);
                                    assert_eq!(caps.c_capabilities, [0xdead]);
                                    assert_eq!(
                                        info.profile.profile.as_ref().unwrap().words,
                                        [0x1234, 0x5678]
                                    );
                                    assert_eq!(info.consumed_bytes, bytes.len() as u64);
                                    assert_eq!(layout.tile_parts.len(), 1);
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 1_296);
}

#[test]
fn actual_raw_main_header_result_preserves_dispatch_and_finalization_first_errors() {
    let limits = ResourceLimits::default();
    let [cod, qcd] = baseline_headers();
    let start = 2 + siz().len();
    let mut cases = 0;
    for shift in [0_u8, 1, 255] {
        let roi = segment(RGN, &[0, 0, shift]);
        let prefix = vec![qcd.clone(), cod.clone(), roi.clone()];
        let duplicate_offset = start + prefix.iter().map(Vec::len).sum::<usize>();
        let mut headers = prefix;
        headers.extend([roi, segment(QCD, &[0])]);
        let bytes = codestream_with_headers(1, &headers, &[], &[]);
        assert_eq!(
            parse_layout(&bytes, &limits).unwrap_err(),
            input_error_literal(duplicate_offset, MalformedKind::InvalidMarkerOrder)
        );
        cases += 1;
    }
    let incomplete_mct = mct_i16_segmented(1, 1, &[1], 1)[0].clone();
    let record = mcc(3, 1, true, 1, 0);
    let incomplete_mcc = segmented_mcc(&record, 1)[0].clone();
    for fragment in [incomplete_mct, incomplete_mcc] {
        for present in 0_u8..4 {
            let mut headers = Vec::new();
            if present & 1 != 0 {
                headers.push(cod.clone());
            }
            if present & 2 != 0 {
                headers.push(qcd.clone());
            }
            headers.push(fragment.clone());
            let end = start + headers.iter().map(Vec::len).sum::<usize>();
            let bytes = codestream_with_headers(1, &headers, &[], &[]);
            assert_eq!(
                parse_layout(&bytes, &limits).unwrap_err(),
                input_error_literal(end, MalformedKind::MissingRequiredStructure)
            );
            cases += 1;
        }
    }
    for qcd_payload in [&[][..], &[0][..]] {
        let mut invalid_cod = cod.clone();
        invalid_cod[12] = 0x80;
        let invalid_qcd = segment(QCD, qcd_payload);
        let offset = start + invalid_qcd.len();
        let bytes = codestream_with_headers(1, &[invalid_qcd, invalid_cod], &[], &[]);
        assert_eq!(
            parse_layout(&bytes, &limits).unwrap_err(),
            input_error_literal(offset, MalformedKind::InvalidCodingStyle)
        );
        cases += 1;
    }
    for marker in [COD, QCD, CAP, PRF, CPF, POC, MCO] {
        let value = match marker {
            COD => cod.clone(),
            QCD => qcd.clone(),
            CAP => segment(CAP, &[0x80, 0, 0, 0, 0, 1]),
            PRF | CPF => segment(marker, &[0, 1]),
            POC => segment(POC, &[0, 0, 0, 1, 1, 1, 0]),
            MCO => mco(&[]),
            _ => unreachable!(),
        };
        let offset = start + value.len();
        let bytes = codestream_with_headers(1, &[value.clone(), value], &[], &[]);
        assert_eq!(
            parse_layout(&bytes, &limits).unwrap_err(),
            input_error_literal(offset, MalformedKind::InvalidMarkerOrder),
            "duplicate marker {marker:#06x}",
        );
        cases += 1;
    }
    assert_eq!(cases, 20);
}

#[test]
fn actual_raw_main_header_result_joins_fragment_packet_metadata_and_owned_extensions() {
    let limits = ResourceLimits::default();
    let [cod, qcd] = baseline_headers();
    for metadata in 0_u8..8 {
        let parts = mct_i16_segmented(1, 1, &[1, 0, 0, 1], 3);
        let record = mcc(3, 2, true, 1, 0);
        let record_parts = segmented_mcc(&record, 2);
        let mut headers = vec![
            qcd.clone(),
            cod.clone(),
            parts[0].clone(),
            record_parts[0].clone(),
            parts[1].clone(),
            record_parts[1].clone(),
            mco(&[3]),
            segment(DFS, &[0, 1, 4, 0x1b]),
            segment(ADS, &[2, 1, 0x40, 1, 0]),
            segment(NLT, &[0xff, 0xff, 7, 0]),
            segment(CBD, &[0, 2, 7, 0x87]),
            segment(ATK, &[0x4a, 2, 0x3f, 0x80, 0, 0, 0]),
            segment(CRG, &[0, 1, 0, 2, 0, 3, 0, 4]),
        ];
        if metadata & 1 != 0 {
            headers.push(plm(0, &[&[1 + u32::from(metadata & 2 != 0)]]));
        }
        if metadata & 2 != 0 {
            headers.push(ppm(0, &[0, 0, 0, 1, 0x11]));
        }
        if metadata & 4 != 0 {
            headers.push(segment(TLM, &[0, 0, 0, 15]));
        }
        let bytes = codestream_with_headers(2, &headers, &[], &[0x5a]);
        let layout = parse_layout(&bytes, &limits).unwrap();
        assert_eq!(layout.info.main_header_segments, headers.len() as u64 + 1);
        assert_eq!(layout.info.image_size.component(1).unwrap().precision, 8);
        assert!(layout.info.image_size.component(1).unwrap().signed);
        assert_eq!(
            layout.info.image_size.component(1).unwrap().x_registration,
            3
        );
        let graph = layout.info.multiple_component_transform.as_ref().unwrap();
        assert_eq!(
            graph.stages()[0].collections()[0]
                .matrix()
                .unwrap()
                .values(),
            [1, 0, 0, 1]
        );
        let extensions = &layout.info.part2_extensions;
        assert_eq!(extensions.decomposition_structures.len(), 1);
        assert_eq!(extensions.arbitrary_decompositions.len(), 1);
        assert_eq!(extensions.nonlinear_transforms.len(), 1);
        assert_eq!(extensions.arbitrary_kernels.len(), 1);
        assert_eq!(extensions.component_bit_depths.len(), 2);
        assert_eq!(extensions.component_registrations.len(), 2);
        assert_eq!(
            extensions.tile_part_lengths.len(),
            usize::from(metadata & 4 != 0)
        );
        assert_eq!(
            layout.tile_parts[0].data.as_ptr(),
            bytes[bytes.len() - 3..].as_ptr()
        );
        assert_eq!(layout.tile_parts[0].data, [0x5a]);
        assert_eq!(
            layout.tile_parts[0].packed_packet_headers.length,
            usize::from(metadata & 2 != 0)
        );
        assert_eq!(layout.info.consumed_bytes, bytes.len() as u64);
    }
}
