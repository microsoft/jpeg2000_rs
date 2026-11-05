use super::persistent_tile_configuration::interleaved_persistent_parts;
use super::*;

#[test]
fn actual_complete_raw_layout_result_keeps_interleaved_source_parts_and_public_info() {
    let limits = ResourceLimits::default();
    for last_roi in [None, Some(9)] {
        let (bytes, starts) = interleaved_persistent_parts(last_roi);
        for count in 1..=6 {
            let end = if count == 6 {
                bytes.len() - 2
            } else {
                starts[count]
            };
            let mut input = bytes[..end].to_vec();
            input.extend(EOC.to_be_bytes());
            let layout = parse_layout(&input, &limits).unwrap();
            assert_eq!(parse(&input, &limits).unwrap(), layout.info);
            assert_eq!(layout.info.main_header_segments, 3);
            assert_eq!(layout.info.tile_parts, count as u32);
            assert_eq!(layout.info.consumed_bytes, input.len() as u64);
            assert_eq!(layout.info.image_size.width, 64);
            assert_eq!(layout.info.image_size.height, 32);
            assert_eq!(layout.info.image_size.tiles_across, 2);
            assert_eq!(layout.info.image_size.tiles_down, 1);
            assert_eq!(layout.info.coding_style.layers, 2);
            assert_eq!(
                layout.info.profile.block_coding,
                CodestreamBlockCoding::Legacy
            );
            assert_eq!(layout.tile_parts.len(), count);
            for (index, payload) in layout.tile_parts.iter().enumerate() {
                let tile = index % 2;
                let length = usize::try_from(u32::from_be_bytes(
                    input[starts[index] + 6..starts[index] + 10]
                        .try_into()
                        .unwrap(),
                ))
                .unwrap();
                let data_offset = starts[index] + length - 1;
                assert_eq!(payload.tile_index, tile as u16);
                assert_eq!(payload.tile_part_index, (index / 2) as u8);
                assert_eq!(payload.tile_part_count, 3);
                assert_eq!(payload.data, [index as u8]);
                assert_eq!(payload.data.as_ptr(), input[data_offset..].as_ptr());
                assert_eq!(payload.coding_style.layers, if tile == 0 { 3 } else { 5 });
                assert_eq!(
                    payload.roi_shifts.shift(0).unwrap(),
                    if tile == 0 { 7 } else { 9 }
                );
                assert_eq!(
                    payload
                        .component_coding_styles
                        .style(0)
                        .unwrap()
                        .code_block_width,
                    if index == 2 || index == 4 { 32 } else { 16 }
                );
                assert_eq!(payload.part2_extensions.decomposition_structures.len(), 1);
                assert_eq!(payload.progression_changes.records.len(), 1);
                assert!(payload.multiple_component_transform.is_some());
            }
        }
    }
}

#[test]
fn actual_complete_raw_layout_result_preserves_late_roi_end_and_profile_error_priority() {
    let limits = ResourceLimits::default();
    let (invalid_roi, starts) = interleaved_persistent_parts(Some(8));
    for end_delta in [0, 1, 2] {
        let mut bytes = invalid_roi[..invalid_roi.len() - end_delta].to_vec();
        if end_delta == 0 {
            bytes.extend([0x12, 0x34]);
        }
        let expected = input_error_literal(starts[5], MalformedKind::InvalidRegionOfInterest);
        assert_eq!(parse_layout(&bytes, &limits).unwrap_err(), expected);
        assert_eq!(parse(&bytes, &limits).unwrap_err(), expected);
    }
    let (original, _) = interleaved_persistent_parts(None);
    let cod = 2 + siz().len();
    assert_eq!(&original[cod..cod + 2], &COD.to_be_bytes());
    for invalid_profile in [false, true] {
        for trailing in [false, true] {
            let mut bytes = original.clone();
            if invalid_profile {
                bytes[cod + 12] = 0x40;
            }
            if trailing {
                bytes.push(0);
            }
            let expected = if trailing {
                Some(input_error_literal(
                    original.len(),
                    MalformedKind::TrailingData,
                ))
            } else if invalid_profile {
                Some(input_error_literal(0, MalformedKind::InvalidProfile))
            } else {
                None
            };
            if let Some(error) = expected {
                assert_eq!(parse_layout(&bytes, &limits).unwrap_err(), error);
                assert_eq!(parse(&bytes, &limits).unwrap_err(), error);
            } else {
                assert_eq!(
                    parse(&bytes, &limits).unwrap(),
                    parse_layout(&bytes, &limits).unwrap().info
                );
            }
        }
    }
}

#[test]
fn actual_complete_raw_layout_result_keeps_input_work_and_tile_limit_first_errors() {
    let (mut bytes, starts) = interleaved_persistent_parts(None);
    bytes[starts[1] + 2..starts[1] + 4].copy_from_slice(&2_u16.to_be_bytes());
    let base = ResourceLimits::default();
    for (limits, expected) in [
        (
            base.with_maximum_input_bytes(0).unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::InputBytes,
                limit: 0,
                actual: bytes.len() as u64,
            },
        ),
        (
            base.with_maximum_work_units(0).unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 0,
                actual: 1,
            },
        ),
        (
            base.with_maximum_tile_parts(1).unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::TileParts,
                limit: 1,
                actual: 2,
            },
        ),
        (
            base,
            input_error_literal(starts[1], MalformedKind::InvalidTilePart),
        ),
    ] {
        assert_eq!(parse_layout(&bytes, &limits).unwrap_err(), expected);
        assert_eq!(parse(&bytes, &limits).unwrap_err(), expected);
    }
}

#[test]
fn actual_complete_raw_layout_result_retains_full_owned_profile_words_and_classes() {
    let limits = ResourceLimits::default();
    for (code, word, class) in [
        (0, 0x8008_u16, CodestreamBlockCoding::Legacy),
        (0x40, 8, CodestreamBlockCoding::HighThroughput),
        (0xc0, 0xc008, CodestreamBlockCoding::Mixed),
    ] {
        let mut bytes = ht_codestream_with_capability(code, word);
        let cap = bytes
            .windows(2)
            .position(|pair| pair == CAP.to_be_bytes())
            .unwrap();
        let old_length = usize::from(u16::from_be_bytes([bytes[cap + 2], bytes[cap + 3]])) + 2;
        let mut words = vec![0x80, 2, 0, 0, 0xa5, 0x5a];
        words.extend(word.to_be_bytes());
        bytes.splice(cap..cap + old_length, segment(CAP, &words));
        let sot = bytes
            .windows(2)
            .position(|pair| pair == SOT.to_be_bytes())
            .unwrap();
        let mut profiles = segment(PRF, &[0x12, 0x34, 0, 1]);
        profiles.extend(segment(CPF, &[0x56, 0x78, 0, 1]));
        bytes.splice(sot..sot, profiles);
        let layout = parse_layout(&bytes, &limits).unwrap();
        assert_eq!(parse(&bytes, &limits).unwrap(), layout.info);
        assert_eq!(layout.info.profile.block_coding, class);
        let caps = layout.info.profile.extended_capabilities.as_ref().unwrap();
        assert_eq!(caps.p_cap, 0x8002_0000);
        assert_eq!(caps.c_capabilities, [0xa55a, word]);
        assert_eq!(
            layout.info.profile.profile.as_ref().unwrap().words,
            [0x1234, 1]
        );
        assert_eq!(
            layout
                .info
                .profile
                .corresponding_profile
                .as_ref()
                .unwrap()
                .words,
            [0x5678, 1]
        );
        assert_eq!(layout.info.consumed_bytes, bytes.len() as u64);
        assert_eq!(layout.info.tile_parts, 1);
    }
}
