use super::super::profile::classify_codestream_profile;
use super::*;

fn styles(logical: u16, code: u8, transform: WaveletTransform) -> ComponentCodingStyles {
    let mut value = raw_resolution_style(31, 17);
    value.code_block_style = code;
    value.transform = transform;
    ComponentCodingStyles {
        components: logical,
        styles: [value; MAX_COMPONENTS],
    }
}

fn capabilities(word: u16) -> Option<ExtendedCapabilities> {
    Some(ExtendedCapabilities {
        p_cap: PART_15_CAPABILITY_FLAG,
        c_capabilities: vec![word],
    })
}

#[test]
fn actual_complete_profile_result_exhausts_capability_words_and_retains_every_owned_word() {
    let roi = RoiShifts::none();
    let mut cases = 0;
    for (code, expected_class) in [
        (0, CodestreamBlockCoding::Legacy),
        (0x40, CodestreamBlockCoding::HighThroughput),
        (0xc0, CodestreamBlockCoding::Mixed),
    ] {
        let main = styles(1, code, WaveletTransform::Reversible5x3);
        for word in 0..=u16::MAX {
            let preceding = word & 1 != 0;
            let mask = PART_15_CAPABILITY_FLAG | if preceding { 0x8000_0000 } else { 0 };
            let words = if preceding {
                vec![0xa55a, word, 0xdead, 0xbeef]
            } else {
                vec![word, 0xdead, 0xbeef]
            };
            let pointer = words.as_ptr();
            let capacity = words.capacity();
            let profile_words = vec![0, u16::MAX, word];
            let profile_pointer = profile_words.as_ptr();
            let corresponding_words = if preceding { vec![u16::MAX, 0] } else { vec![] };
            let corresponding_pointer = corresponding_words.as_ptr();
            let result = classify_codestream_profile(
                HT_RSIZ_FLAG | 0x0123,
                Some(ExtendedCapabilities {
                    p_cap: mask,
                    c_capabilities: words,
                }),
                Some(ProfileNumber {
                    words: profile_words,
                }),
                Some(ProfileNumber {
                    words: corresponding_words,
                }),
                &main,
                &roi,
                &[],
                1,
                false,
            );
            let mode = word / 16384;
            let reserved = (word / 64) % 32;
            let mode_allowed = match mode {
                0 => code != 0,
                2 => code != 0xc0,
                3 => true,
                _ => false,
            };
            if reserved != 0 || !mode_allowed {
                assert_eq!(
                    result,
                    Err(input_error_literal(0, MalformedKind::InvalidProfile)),
                    "code={code}, word={word}"
                );
            } else {
                let result = result.unwrap();
                assert_eq!(result.r_siz, HT_RSIZ_FLAG | 0x0123);
                assert_eq!(result.block_coding, expected_class);
                let caps = result.extended_capabilities.unwrap();
                assert_eq!(caps.p_cap, mask);
                assert_eq!(caps.c_capabilities.as_ptr(), pointer);
                assert_eq!(caps.c_capabilities.capacity(), capacity);
                if preceding {
                    assert_eq!(caps.c_capabilities, [0xa55a, word, 0xdead, 0xbeef]);
                } else {
                    assert_eq!(caps.c_capabilities, [word, 0xdead, 0xbeef]);
                }
                let profile = result.profile.unwrap();
                assert_eq!(profile.words, [0, u16::MAX, word]);
                assert_eq!(profile.words.as_ptr(), profile_pointer);
                let corresponding = result.corresponding_profile.unwrap();
                assert_eq!(corresponding.words.as_ptr(), corresponding_pointer);
                assert_eq!(
                    corresponding.words.as_slice(),
                    if preceding {
                        &[u16::MAX, 0][..]
                    } else {
                        &[][..]
                    }
                );
            }
            cases += 1;
        }
    }
    assert_eq!(cases, 196_608);
}

#[test]
fn actual_complete_profile_result_preserves_raw_owner_counts_tails_and_first_style_errors() {
    let roi = RoiShifts {
        shifts: core::array::from_fn(|index| (index * 7) as u8),
    };
    let mut cases = 0;
    for main_count in [0, 1, 63, 64, u16::MAX] {
        for tile_count in [0, 1, 63, 64, u16::MAX] {
            for components in [0, 1, 2, 63, 64, 65, u16::MAX] {
                for parts in [0, 1, 3] {
                    let main = styles(main_count, 0, WaveletTransform::Arbitrary(255));
                    let main_before = main;
                    let mut tiles: Vec<_> = (0..parts)
                        .map(|index| {
                            let mut tile = raw_owned_tile_part_fixture(index + 1);
                            tile.tile_index = u16::MAX;
                            tile.component_coding_styles =
                                styles(tile_count, 0, WaveletTransform::Arbitrary(255));
                            tile.roi_shifts = roi;
                            tile.has_roi_marker = false;
                            tile.has_functional_header_marker = false;
                            tile
                        })
                        .collect();
                    let before = tiles.clone();
                    let result = classify_codestream_profile(
                        HT_RSIZ_FLAG,
                        capabilities(0x8000),
                        None,
                        None,
                        &main,
                        &roi,
                        &tiles,
                        components,
                        false,
                    );
                    if components > main_count
                        || usize::from(components) > MAX_COMPONENTS
                        || (parts != 0 && components > tile_count)
                    {
                        assert_eq!(
                            result,
                            Err(input_error_literal(0, MalformedKind::InvalidCodingStyle))
                        );
                    } else {
                        assert_eq!(result.unwrap().block_coding, CodestreamBlockCoding::Legacy);
                    }
                    assert_eq!(main, main_before);
                    assert_eq!(tiles, before);
                    if parts != 0 && components != 0 && main_count != 0 && tile_count != 0 {
                        tiles[parts - 1].component_coding_styles.styles[0].code_block_style = 0x80;
                        assert_eq!(
                            classify_codestream_profile(
                                0, None, None, None, &main, &roi, &tiles, components, false
                            ),
                            Err(input_error_literal(0, MalformedKind::InvalidCodingStyle)),
                        );
                    }
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 525);
}

#[test]
fn actual_complete_profile_result_composes_all_flag_combinations_and_raw_roi_policies() {
    for flags in 0_u8..8 {
        let codes: Vec<_> = [(1, 0), (2, 0x40), (4, 0xc0)]
            .into_iter()
            .filter_map(|(bit, code)| (flags & bit != 0).then_some(code))
            .collect();
        let main = styles(
            1,
            codes.first().copied().unwrap_or(0x80),
            WaveletTransform::Reversible5x3,
        );
        let components = u16::from(flags != 0);
        let tiles: Vec<_> = codes
            .iter()
            .skip(1)
            .enumerate()
            .map(|(index, code)| {
                let mut tile = raw_owned_tile_part_fixture(index);
                tile.component_coding_styles = styles(1, *code, WaveletTransform::Reversible5x3);
                tile.roi_shifts = RoiShifts::none();
                tile.has_roi_marker = false;
                tile.has_functional_header_marker = false;
                tile
            })
            .collect();
        let result = classify_codestream_profile(
            HT_RSIZ_FLAG,
            capabilities(0xc000),
            None,
            None,
            &main,
            &RoiShifts::none(),
            &tiles,
            components,
            false,
        )
        .unwrap();
        let expected = if flags & 4 != 0 || flags & 3 == 3 {
            CodestreamBlockCoding::Mixed
        } else if flags & 2 != 0 {
            CodestreamBlockCoding::HighThroughput
        } else {
            CodestreamBlockCoding::Legacy
        };
        assert_eq!(result.block_coding, expected, "flags={flags}");
    }
    let legacy = styles(1, 0, WaveletTransform::Reversible5x3);
    let ht_irreversible = styles(1, 0x40, WaveletTransform::Irreversible9x7);
    for (word, shifts, marker, components, main, accepted) in [
        (0x8000, 0, true, 0, legacy, false),
        (0x9000, 255, true, 0, legacy, true),
        (0x9000, 37, true, 1, legacy, true),
        (0x9000, 38, true, 1, legacy, false),
        (0x9000, 255, false, 1, legacy, true),
        (0, 0, false, 1, ht_irreversible, false),
        (0x20, 0, false, 1, ht_irreversible, true),
    ] {
        let roi = RoiShifts {
            shifts: [shifts; MAX_COMPONENTS],
        };
        let result = classify_codestream_profile(
            HT_RSIZ_FLAG,
            capabilities(word),
            None,
            None,
            &main,
            &roi,
            &[],
            components,
            marker,
        );
        if accepted {
            assert!(result.is_ok());
        } else {
            assert_eq!(
                result,
                Err(input_error_literal(0, MalformedKind::InvalidProfile))
            );
        }
    }
}

#[test]
fn actual_complete_profile_result_uses_real_raw_header_and_layout_producers() {
    let limits = ResourceLimits::default();
    for (code, word, expected) in [
        (0, 0x8008, CodestreamBlockCoding::Legacy),
        (0x40, 8, CodestreamBlockCoding::HighThroughput),
        (0xc0, 0xc008, CodestreamBlockCoding::Mixed),
    ] {
        let bytes = ht_codestream_with_capability(code, word);
        let layout = parse_layout(&bytes, &limits).unwrap();
        assert_eq!(layout.info.profile.block_coding, expected);
        assert_eq!(
            layout
                .info
                .profile
                .extended_capabilities
                .as_ref()
                .unwrap()
                .c_capabilities,
            [word]
        );
        assert_eq!(layout.info.consumed_bytes, bytes.len() as u64);
        assert_eq!(layout.tile_parts.len(), 1);
    }
    let invalid_style = ht_codestream_with_capability(0x80, 0x4000);
    assert_eq!(
        parse_layout(&invalid_style, &limits).unwrap_err(),
        input_error_literal(
            invalid_style
                .windows(2)
                .position(|pair| pair == COD.to_be_bytes())
                .unwrap(),
            MalformedKind::InvalidCodingStyle
        )
    );
}
