use super::*;

fn with_terminal_trailer(mut bytes: Vec<u8>, count: usize, open_ended: bool) -> Vec<u8> {
    let sot = bytes
        .windows(2)
        .position(|pair| pair == [255, 144])
        .unwrap();
    let psot = u32::from_be_bytes(bytes[sot + 6..sot + 10].try_into().unwrap());
    let length = if open_ended { 0 } else { psot + count as u32 };
    bytes[sot + 6..sot + 10].copy_from_slice(&length.to_be_bytes());
    let end = bytes.len() - 2;
    bytes.splice(end..end, std::iter::repeat_n(0xee, count));
    bytes
}

fn terminal_trailer_codestream(count: usize, open_ended: bool) -> Vec<u8> {
    with_terminal_trailer(dimension_recovery_codestream(), count, open_ended)
}

#[test]
fn pdf_trailer_preserves_selected_geometry_reduction_and_fractional_headroom() {
    let options = DecodeOptions::default();
    let original = prepared_codestream(
        8,
        8,
        1,
        &[0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50],
        &[0, 0, 0],
    );
    let bytes = with_terminal_trailer(original.clone(), 4, false);
    for selection in [
        DecodeSelection::full_image().with_discard_levels(1),
        DecodeSelection::full_image().with_discard_levels(2),
        DecodeSelection::full_image().with_region(crate::ImageRegion::new(1, 1, 5, 5)),
    ] {
        let expected =
            decode_codestream_reconstructed_selected(&original, &options, &selection).unwrap();
        let wide = crate::decode_codestream_reconstructed_recover_trailer_selected(
            &bytes, &options, &selection,
        )
        .unwrap();
        assert_eq!(wide.image, expected);
        assert_eq!(wide.report.discarded_tile_trailer_bytes, 4);
        let typed = crate::decode_codestream_recover_trailer_selected(&bytes, &options, &selection)
            .unwrap();
        assert_eq!(typed.image, expected.typed(options.limits()).unwrap());
        let jp2 = jp2_for_codestream(&bytes, 8, 8);
        assert_eq!(
            crate::decode_jp2_reconstructed_recover_trailer_selected(&jp2, &options, &selection)
                .unwrap(),
            wide
        );
    }
    let mut fractional = prepared_codestream(1, 1, 0, &[0x42, 0x44, 0], &[0xcf, 0xb4, 0x04, 0x09]);
    let cod = fractional
        .windows(2)
        .position(|pair| pair == [255, 82])
        .unwrap();
    fractional[cod + 9] = 0;
    let bytes = with_terminal_trailer(fractional, 4, false);
    let wide = crate::decode_codestream_reconstructed_recover_trailer_selected(
        &bytes,
        &options,
        &DecodeSelection::full_image(),
    )
    .unwrap();
    assert_eq!(
        wide.image.component(0).unwrap().samples(),
        &[-765 * (1 << 14)]
    );
    assert_eq!(wide.image.component(0).unwrap().fraction_bits(), 16);
}

#[test]
fn pdf_trailer_bounds_complete_packets_and_preserves_all_output_domains() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let original = dimension_recovery_codestream();
    let expected = decode_codestream(&original, &options).unwrap();
    let wide = decode_codestream_reconstructed_selected(&original, &options, &selection).unwrap();
    for open in [false, true] {
        for count in [0, 1, 4, 16] {
            let bytes = terminal_trailer_codestream(count, open);
            if count > 0 {
                assert!(matches!(
                    decode_codestream(&bytes, &options),
                    Err(DecodeError::MalformedInput {
                        kind: MalformedKind::TrailingData,
                        ..
                    })
                ));
            }
            let recovered =
                crate::decode_codestream_recover_trailer_selected(&bytes, &options, &selection)
                    .unwrap();
            assert_eq!(recovered.image, expected);
            assert_eq!(recovered.report.discarded_tile_trailer_bytes, count as u8);
            let reconstructed = crate::decode_codestream_reconstructed_recover_trailer_selected(
                &bytes, &options, &selection,
            )
            .unwrap();
            assert_eq!(reconstructed.image, wide);
            assert_eq!(reconstructed.report, recovered.report);
            let container = jp2_for_codestream(&bytes, 1, 1);
            assert_eq!(
                crate::decode_jp2_recover_trailer_selected(&container, &options, &selection)
                    .unwrap(),
                recovered
            );
            assert_eq!(
                crate::decode_jp2_reconstructed_recover_trailer_selected(
                    &container, &options, &selection
                )
                .unwrap(),
                reconstructed
            );
        }
        let bytes = terminal_trailer_codestream(17, open);
        let container = jp2_for_codestream(&bytes, 1, 1);
        for error in [
            crate::decode_codestream_recover_trailer_selected(&bytes, &options, &selection)
                .unwrap_err(),
            crate::decode_codestream_reconstructed_recover_trailer_selected(
                &bytes, &options, &selection,
            )
            .unwrap_err(),
            crate::decode_jp2_recover_trailer_selected(&container, &options, &selection)
                .unwrap_err(),
            crate::decode_jp2_reconstructed_recover_trailer_selected(
                &container, &options, &selection,
            )
            .unwrap_err(),
        ] {
            assert!(matches!(
                error,
                DecodeError::MalformedInput {
                    kind: MalformedKind::TrailingData,
                    ..
                }
            ));
        }
    }
}

#[test]
fn pdf_trailer_requires_complete_bodies_final_parts_and_absent_length_metadata() {
    fn update_length(bytes: &mut [u8]) {
        let sot = bytes
            .windows(2)
            .position(|pair| pair == [255, 144])
            .unwrap();
        let length = (bytes.len() - 2 - sot) as u32;
        bytes[sot + 6..sot + 10].copy_from_slice(&length.to_be_bytes());
    }

    fn append_final(mut bytes: Vec<u8>, count: usize) -> Vec<u8> {
        let sot = bytes
            .windows(2)
            .position(|pair| pair == [255, 144])
            .unwrap();
        bytes[sot + 11] = 2;
        bytes.truncate(bytes.len() - 2);
        let mut header = vec![0, 0];
        header.extend_from_slice(&(14 + count as u32).to_be_bytes());
        header.extend_from_slice(&[1, 2]);
        bytes.extend(segment(0xff90, &header));
        bytes.extend_from_slice(&[255, 147]);
        bytes.extend(std::iter::repeat_n(0xee, count));
        bytes.extend_from_slice(&[255, 217]);
        bytes
    }

    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let original = dimension_recovery_codestream();
    let expected = decode_codestream(&original, &options).unwrap();
    let layout = codestream::parse_layout(&original, options.limits()).unwrap();
    let first = &layout.tile_parts[0];
    let mut plan = plan_progression_tile(
        &layout.info.image_size,
        first.coding_style,
        &first.quantization,
        options.limits(),
    )
    .unwrap();
    let (grid, precincts) = plan.packet_execution();
    let packet = crate::packet::decode_progression_tile_packets(
        &layout.tile_parts,
        grid,
        precincts,
        options.limits(),
    )
    .unwrap();
    assert_eq!(packet.packets, 1);
    let header_bytes = packet.packet_header_bytes as usize;
    assert!(0 < header_bytes && header_bytes < first.data.len());
    let sod = original
        .windows(2)
        .position(|pair| pair == [255, 147])
        .unwrap();

    let mut plt = original.clone();
    plt.splice(sod..sod, segment(0xff58, &[0, first.data.len() as u8]));
    update_length(&mut plt);
    assert_eq!(decode_codestream(&plt, &options).unwrap(), expected);
    let mut packed = vec![0];
    packed.extend_from_slice(&first.data[..header_bytes]);
    let mut ppt = original[..sod].to_vec();
    ppt.extend(segment(0xff61, &packed));
    ppt.extend_from_slice(&[255, 147]);
    ppt.extend_from_slice(&first.data[header_bytes..]);
    ppt.extend_from_slice(&[255, 217]);
    update_length(&mut ppt);
    assert_eq!(decode_codestream(&ppt, &options).unwrap(), expected);
    for mut bytes in [plt, ppt] {
        let end = bytes.len() - 2;
        bytes.splice(end..end, [0xee; 4]);
        update_length(&mut bytes);
        assert_eq!(
            crate::decode_codestream_recover_trailer_selected(&bytes, &options, &selection)
                .unwrap_err(),
            decode_codestream(&bytes, &options).unwrap_err()
        );
    }

    for kept in [1, first.data.len() - 1] {
        let mut bytes = original[..sod + 2 + kept].to_vec();
        bytes.extend_from_slice(&[255, 217]);
        update_length(&mut bytes);
        let error = decode_codestream(&bytes, &options).unwrap_err();
        assert_eq!(
            crate::decode_codestream_recover_trailer_selected(&bytes, &options, &selection)
                .unwrap_err(),
            error,
        );
    }
    let intact = append_final(original, 0);
    assert_eq!(decode_codestream(&intact, &options).unwrap(), expected);
    let final_trailer = append_final(dimension_recovery_codestream(), 4);
    let recovered =
        crate::decode_codestream_recover_trailer_selected(&final_trailer, &options, &selection)
            .unwrap();
    assert_eq!(recovered.image, expected);
    assert_eq!(recovered.report.discarded_tile_trailer_bytes, 4);
    let nonfinal = append_final(terminal_trailer_codestream(4, false), 0);
    assert!(matches!(
        crate::decode_codestream_recover_trailer_selected(&nonfinal, &options, &selection),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::TrailingData,
            ..
        })
    ));
}

#[test]
fn pdf_trailer_allowance_is_cumulative_and_does_not_change_other_calls() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    for (second_count, admitted) in [(8, true), (9, false)] {
        let mut bytes = terminal_trailer_codestream(8, false);
        let second = terminal_trailer_codestream(second_count, false);
        let sot = second
            .windows(2)
            .position(|pair| pair == [255, 144])
            .unwrap();
        let mut part = second[sot..second.len() - 2].to_vec();
        part[4..6].copy_from_slice(&1_u16.to_be_bytes());
        bytes.truncate(bytes.len() - 2);
        bytes.extend_from_slice(&part);
        bytes.extend_from_slice(&[255, 217]);
        bytes[8..12].copy_from_slice(&2_u32.to_be_bytes());
        let result =
            crate::decode_codestream_recover_trailer_selected(&bytes, &options, &selection);
        if admitted {
            let recovered = result.unwrap();
            assert_eq!(recovered.report.discarded_tile_trailer_bytes, 16);
            assert_eq!((recovered.image.width(), recovered.image.height()), (2, 1));
            assert_eq!(
                recovered.image.component(0).unwrap().samples(),
                &TypedSamples::Unsigned(vec![1, 1])
            );
            let tile = crate::decode_codestream_recover_trailer_selected(
                &bytes,
                &options,
                &DecodeSelection::tile(1),
            )
            .unwrap();
            assert_eq!(tile.report.discarded_tile_trailer_bytes, 8);
            assert_eq!((tile.image.width(), tile.image.x_origin()), (1, 1));
        } else {
            assert!(matches!(
                result,
                Err(DecodeError::MalformedInput {
                    kind: MalformedKind::TrailingData,
                    ..
                })
            ));
        }
    }
    let bytes = terminal_trailer_codestream(4, false);
    let limited = DecodeOptions::new(
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(1)
            .unwrap(),
    );
    assert!(matches!(
        crate::decode_codestream_recover_trailer_selected(&bytes, &limited, &selection),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            ..
        })
    ));
    let expected =
        crate::decode_codestream_recover_trailer_selected(&bytes, &options, &selection).unwrap();
    let refused = crate::allocation::with_refusal(0, || {
        crate::decode_codestream_recover_trailer_selected(&bytes, &options, &selection)
    });
    assert_eq!(refused.unwrap_err(), DecodeError::AllocationFailed);
    assert_eq!(
        crate::decode_codestream_recover_trailer_selected(&bytes, &options, &selection).unwrap(),
        expected
    );
    assert!(matches!(
        decode_codestream(&bytes, &options),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::TrailingData,
            ..
        })
    ));
}

#[test]
fn selected_jp2_reconstruction_preserves_headroom_geometry_and_strict_coverage() {
    let options = DecodeOptions::default();
    let mut fractional = prepared_codestream(1, 1, 0, &[0x42, 0x44, 0], &[0xcf, 0xb4, 0x04, 0x09]);
    let cod = fractional
        .windows(2)
        .position(|pair| pair == [255, 82])
        .unwrap();
    fractional[cod + 9] = 0;
    let container = jp2_for_codestream(&fractional, 1, 1);
    let selected = DecodeSelection::tile(0);
    let image = crate::decode_jp2_reconstructed_selected(&container, &options, &selected).unwrap();
    assert_eq!(
        image,
        decode_codestream_reconstructed_selected(&fractional, &options, &selected).unwrap()
    );
    assert_eq!(image.component(0).unwrap().samples(), &[-765 * (1 << 14)]);
    assert_eq!(image.component(0).unwrap().fraction_bits(), 16);
    assert_eq!(
        image.typed(options.limits()).unwrap(),
        crate::decode_jp2_selected(&container, &options, &selected).unwrap()
    );

    let bytes = prepared_codestream(
        8,
        8,
        1,
        &[0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50],
        &[0, 0, 0],
    );
    let container = jp2_for_codestream(&bytes, 8, 8);
    for selection in [
        DecodeSelection::full_image().with_region(crate::ImageRegion::new(1, 1, 5, 5)),
        DecodeSelection::tile(0).with_discard_levels(1),
        DecodeSelection::tile(0).with_discard_levels(2),
    ] {
        assert_eq!(
            crate::decode_jp2_reconstructed_selected(&container, &options, &selection).unwrap(),
            decode_codestream_reconstructed_selected(&bytes, &options, &selection).unwrap(),
        );
    }
    let sole = sole_present_tile_codestream();
    let container = jp2_for_codestream(&sole, 2, 1);
    assert!(
        crate::decode_jp2_reconstructed_selected(
            &container,
            &options,
            &DecodeSelection::full_image()
        )
        .is_err()
    );
    assert!(
        crate::decode_jp2_reconstructed_selected(&container, &options, &DecodeSelection::tile(1))
            .is_err()
    );
    assert_eq!(
        crate::decode_jp2_reconstructed_selected(&container, &options, &selected).unwrap(),
        decode_codestream_reconstructed_selected(&sole, &options, &selected).unwrap(),
    );
}

#[test]
fn selected_jp2_reconstruction_retains_metadata_errors_limits_and_refusal_recovery() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::tile(0);
    let bytes = dimension_recovery_codestream();
    let good = jp2_for_codestream(&bytes, 1, 1);
    let mapping = box32(*b"cmap", &[0, 0, 0, 0]);
    let mapped = jp2_reconstruction_with_metadata(&bytes, &mapping);
    assert!(matches!(
        crate::decode_jp2_reconstructed_selected(&mapped, &options, &selection),
        Err(DecodeError::UnsupportedFeature {
            feature: "JP2 output transforms on reconstruction samples"
        })
    ));
    let mismatch = jp2_for_codestream(&bytes, 2, 1);
    assert!(matches!(
        crate::decode_jp2_reconstructed_selected(&mismatch, &options, &selection),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::ContainerCodestreamMismatch,
            ..
        })
    ));
    let bad_selection = DecodeSelection::tile(1);
    assert_eq!(
        crate::decode_jp2_reconstructed_selected(&mapped, &options, &bad_selection).unwrap_err(),
        decode_codestream_reconstructed_selected(&bytes, &options, &bad_selection).unwrap_err(),
    );
    let limited = DecodeOptions::new(
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(1)
            .unwrap(),
    );
    assert!(matches!(
        crate::decode_jp2_reconstructed_selected(&good, &limited, &selection),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            ..
        })
    ));
    let refused = crate::allocation::with_refusal(0, || {
        crate::decode_jp2_reconstructed_selected(&good, &options, &selection)
    });
    assert_eq!(refused.unwrap_err(), DecodeError::AllocationFailed);
    assert!(crate::decode_jp2_reconstructed_selected(&good, &options, &selection).is_ok());
}

fn sole_present_tile_codestream() -> Vec<u8> {
    let mut bytes = dimension_recovery_codestream();
    bytes[8..12].copy_from_slice(&2_u32.to_be_bytes());
    bytes
}

#[test]
fn pdf_present_tile_keeps_actual_extent_canvas_and_explicit_selection() {
    let options = DecodeOptions::default();
    let bytes = sole_present_tile_codestream();
    let full = DecodeSelection::full_image();
    assert!(decode_codestream(&bytes, &options).is_err());
    let info = codestream::parse(&bytes, options.limits()).unwrap();
    assert_eq!((info.image_size.width, info.image_size.height), (2, 1));
    let recovered =
        crate::decode_codestream_recover_present_tile_selected(&bytes, &options, &full).unwrap();
    assert_eq!(recovered.report.selected_present_tile, Some(0));
    assert_eq!(recovered.report.canvas_width, 2);
    assert_eq!(recovered.report.full_canvas_sample_bytes, Some(16));
    assert_eq!(
        (
            recovered.image.width(),
            recovered.image.height(),
            recovered.image.x_origin()
        ),
        (1, 1, 0)
    );
    assert_eq!(
        recovered.image.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(vec![1])
    );
    let requested = DecodeSelection::tile(1);
    let expected = decode_codestream_selected(&bytes, &options, &requested).unwrap_err();
    assert_eq!(
        crate::decode_codestream_recover_present_tile_selected(&bytes, &options, &requested).err(),
        Some(expected)
    );
    let region = full
        .clone()
        .with_region(crate::ImageRegion::new(0, 0, 1, 1));
    let explicit =
        crate::decode_codestream_recover_present_tile_selected(&bytes, &options, &region).unwrap();
    assert_eq!(explicit.report.selected_present_tile, None);
    assert_eq!(explicit.image, recovered.image);
    assert!(decode_codestream(&bytes, &options).is_err());

    let container = jp2_for_codestream(&bytes, 2, 1);
    let jp2 = crate::decode_jp2_recover_present_tile_selected(&container, &options, &full).unwrap();
    assert_eq!(jp2.image, recovered.image);
    assert_eq!(jp2.report, recovered.report);
    let contradictory = jp2_for_codestream(&bytes, 99, 1);
    assert!(matches!(
        crate::decode_jp2_recover_present_tile_selected(&contradictory, &options, &full),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::ContainerCodestreamMismatch,
            ..
        })
    ));
}

#[test]
fn pdf_present_tile_preserves_nonzero_placement_reduction_and_fractional_headroom() {
    let options = DecodeOptions::default();
    let full = DecodeSelection::full_image();
    let mut tile_one = sole_present_tile_codestream();
    let sot = tile_one
        .windows(2)
        .position(|pair| pair == [255, 144])
        .unwrap();
    tile_one[sot + 4..sot + 6].copy_from_slice(&1_u16.to_be_bytes());
    let recovered =
        crate::decode_codestream_recover_present_tile_selected(&tile_one, &options, &full).unwrap();
    assert_eq!(recovered.report.selected_present_tile, Some(1));
    assert_eq!(
        (recovered.image.width(), recovered.image.x_origin()),
        (1, 1)
    );
    let mut shifted = sole_present_tile_codestream();
    shifted[8..12].copy_from_slice(&3_u32.to_be_bytes());
    shifted[16..20].copy_from_slice(&1_u32.to_be_bytes());
    shifted[32..36].copy_from_slice(&1_u32.to_be_bytes());
    let recovered =
        crate::decode_codestream_recover_present_tile_selected(&shifted, &options, &full).unwrap();
    assert_eq!(
        (
            recovered.report.canvas_width,
            recovered.report.canvas_x_origin
        ),
        (2, 1)
    );
    assert_eq!(
        (recovered.image.width(), recovered.image.x_origin()),
        (1, 1)
    );

    let mut reduced = prepared_codestream(
        8,
        8,
        1,
        &[0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50],
        &[0, 0, 0],
    );
    reduced[8..12].copy_from_slice(&16_u32.to_be_bytes());
    for (discard, actual, full_bytes) in [(1, 4, 256), (2, 2, 64)] {
        let selection = DecodeSelection::full_image().with_discard_levels(discard);
        let result =
            crate::decode_codestream_recover_present_tile_selected(&reduced, &options, &selection)
                .unwrap();
        assert_eq!(
            (result.image.width(), result.image.height()),
            (actual, actual)
        );
        assert_eq!(result.report.discard_levels, discard);
        assert_eq!(result.report.full_canvas_sample_bytes, Some(full_bytes));
    }

    let mut fractional = prepared_codestream(1, 1, 0, &[0x42, 0x44, 0], &[0xcf, 0xb4, 0x04, 0x09]);
    let cod = fractional
        .windows(2)
        .position(|pair| pair == [255, 82])
        .unwrap();
    fractional[cod + 9] = 0;
    fractional[8..12].copy_from_slice(&2_u32.to_be_bytes());
    let container = jp2_for_codestream(&fractional, 2, 1);
    let result =
        crate::decode_jp2_reconstructed_recover_present_tile_selected(&container, &options, &full)
            .unwrap();
    assert_eq!(result.report.selected_present_tile, Some(0));
    assert_eq!(result.image.component(0).unwrap().fraction_bits(), 16);
    assert_eq!(
        result.image.component(0).unwrap().samples(),
        &[-765 * (1 << 14)]
    );
}

#[test]
fn pdf_present_tile_retains_full_intended_canvas_limit_and_real_errors() {
    let options = DecodeOptions::default();
    let bytes = sole_present_tile_codestream();
    let selection = DecodeSelection::full_image();
    let limited = DecodeOptions::new(
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(15)
            .unwrap(),
    );
    assert!(decode_codestream_selected(&bytes, &limited, &DecodeSelection::tile(0)).is_ok());
    assert_eq!(
        crate::decode_codestream_recover_present_tile_selected(&bytes, &limited, &selection).err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: 15,
            actual: 16
        })
    );
    let mut damaged = bytes.clone();
    let sod = damaged
        .windows(2)
        .position(|pair| pair == [255, 147])
        .unwrap();
    damaged[sod + 2] = 0xff;
    assert!(codestream::parse(&damaged, options.limits()).is_ok());
    let expected =
        decode_codestream_selected(&damaged, &options, &DecodeSelection::tile(0)).unwrap_err();
    assert_eq!(
        crate::decode_codestream_recover_present_tile_selected(&damaged, &options, &selection)
            .err(),
        Some(expected)
    );
    let expected =
        crate::decode_codestream_recover_present_tile_selected(&bytes, &options, &selection)
            .unwrap();
    let mut completed = false;
    for after in 0..512 {
        match crate::allocation::with_refusal(after, || {
            crate::decode_codestream_recover_present_tile_selected(&bytes, &options, &selection)
        }) {
            Err(DecodeError::AllocationFailed) => assert_eq!(
                crate::decode_codestream_recover_present_tile_selected(
                    &bytes, &options, &selection
                )
                .unwrap(),
                expected
            ),
            Ok(actual) => {
                assert_eq!(actual, expected);
                completed = true;
                break;
            }
            Err(error) => panic!("unexpected present-tile refusal at {after}: {error:?}"),
        }
    }
    assert!(completed);

    let mut palette = jp2_with_palette(&bytes, 256, true);
    let ihdr = palette.windows(4).position(|part| part == b"ihdr").unwrap() + 4;
    palette[ihdr + 4..ihdr + 8].copy_from_slice(&2_u32.to_be_bytes());
    let mapped =
        crate::decode_jp2_recover_present_tile_selected(&palette, &options, &selection).unwrap();
    assert_eq!(mapped.image.components().len(), 3);
    assert_eq!(mapped.report.full_canvas_sample_bytes, Some(48));
    let limited = DecodeOptions::new(
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(47)
            .unwrap(),
    );
    assert_eq!(
        crate::decode_jp2_recover_present_tile_selected(&palette, &limited, &selection).err(),
        Some(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: 47,
            actual: 48
        })
    );
    assert_eq!(
        crate::decode_jp2_reconstructed_recover_present_tile_selected(
            &palette, &options, &selection
        )
        .err(),
        Some(DecodeError::UnsupportedFeature {
            feature: "JP2 output transforms on reconstruction samples",
        })
    );
    let mut nlt = bytes.clone();
    let sot = nlt.windows(2).position(|part| part == [255, 144]).unwrap();
    nlt.splice(sot..sot, segment(0xff76, &[255, 255, 7, 0]));
    assert!(
        crate::decode_codestream_recover_present_tile_selected(&nlt, &options, &selection).is_ok()
    );
    assert_eq!(
        crate::decode_codestream_reconstructed_recover_present_tile_selected(
            &nlt, &options, &selection
        )
        .err(),
        Some(DecodeError::UnsupportedFeature {
            feature: "nonlinear transforms on reconstruction samples",
        })
    );
}

#[test]
fn selected_reconstruction_preserves_fractional_headroom_tile_region_and_reduction() {
    let options = DecodeOptions::default();
    for (packet, numerator) in [
        (&[0xcf, 0xb4, 0x04, 0x09][..], -765_i64),
        (&[0xc0, 0x21, 0x03][..], 9),
    ] {
        let mut bytes = prepared_codestream(1, 1, 0, &[0x42, 0x44, 0], packet);
        let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
        bytes[cod + 9] = 0;
        let selection = DecodeSelection::tile(0).with_region(crate::ImageRegion::new(0, 0, 1, 1));
        let image =
            crate::decode_codestream_reconstructed_selected(&bytes, &options, &selection).unwrap();
        assert_eq!(image.component(0).unwrap().fraction_bits(), 16);
        assert_eq!(
            image.component(0).unwrap().samples(),
            &[numerator * (1 << 14)]
        );
        assert_eq!(
            image.typed(options.limits()),
            decode_codestream_selected(&bytes, &options, &selection)
        );
    }
    let bytes = two_tile_codestream();
    for tile in [0, 1] {
        let selection = DecodeSelection::tile(tile);
        let image =
            crate::decode_codestream_reconstructed_selected(&bytes, &options, &selection).unwrap();
        assert_eq!(
            image.typed(options.limits()),
            decode_codestream_selected(&bytes, &options, &selection)
        );
    }
    let bytes = prepared_codestream(
        8,
        8,
        1,
        &[0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50],
        &[0, 0, 0],
    );
    for discard in [0, 1, 2] {
        let selection = DecodeSelection::full_image().with_discard_levels(discard);
        let image =
            crate::decode_codestream_reconstructed_selected(&bytes, &options, &selection).unwrap();
        assert_eq!(
            (image.width(), image.height()),
            (8 >> discard, 8 >> discard)
        );
        assert_eq!(
            image.typed(options.limits()),
            decode_codestream_selected(&bytes, &options, &selection)
        );
    }
}

#[test]
fn selected_reconstruction_keeps_invalid_selection_nlt_limits_and_refusal_errors() {
    let options = DecodeOptions::default();
    let bytes = dimension_recovery_codestream();
    for selection in [
        DecodeSelection::tile(99),
        DecodeSelection::full_image().with_discard_levels(1),
        DecodeSelection::full_image().with_region(crate::ImageRegion::new(99, 99, 1, 1)),
    ] {
        let error = decode_codestream_selected(&bytes, &options, &selection).unwrap_err();
        assert_eq!(
            crate::decode_codestream_reconstructed_selected(&bytes, &options, &selection),
            Err(error)
        );
    }
    let selection = DecodeSelection::tile(0);
    for limits in [
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
    ] {
        let limited = DecodeOptions::new(limits);
        let error = decode_codestream_selected(&bytes, &limited, &selection).unwrap_err();
        assert_eq!(
            crate::decode_codestream_reconstructed_selected(&bytes, &limited, &selection),
            Err(error)
        );
    }
    let expected =
        crate::decode_codestream_reconstructed_selected(&bytes, &options, &selection).unwrap();
    let mut completed = false;
    for after in 0..256 {
        match crate::allocation::with_refusal(after, || {
            crate::decode_codestream_reconstructed_selected(&bytes, &options, &selection)
        }) {
            Err(DecodeError::AllocationFailed) => assert_eq!(
                crate::decode_codestream_reconstructed_selected(&bytes, &options, &selection)
                    .unwrap(),
                expected
            ),
            Ok(image) => {
                assert_eq!(image, expected);
                completed = true;
                break;
            }
            Err(error) => {
                panic!("unexpected selected reconstruction refusal at {after}: {error:?}")
            }
        }
    }
    assert!(completed);
    let mut nlt = bytes.clone();
    let sot = nlt.windows(2).position(|pair| pair == [255, 144]).unwrap();
    nlt.splice(sot..sot, segment(0xff76, &[255, 255, 7, 0]));
    assert!(decode_codestream_selected(&nlt, &options, &selection).is_ok());
    assert_eq!(
        crate::decode_codestream_reconstructed_selected(&nlt, &options, &selection),
        Err(DecodeError::UnsupportedFeature {
            feature: "nonlinear transforms on reconstruction samples",
        })
    );
}

fn dimension_recovery_codestream() -> Vec<u8> {
    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0xcf, 0xb4, 0x04, 0x09]);
    let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
    bytes[cod + 9] = 0;
    bytes
}

#[test]
fn pdf_dimensions_recover_only_declared_sizes_and_preserve_strict_defaults() {
    let bytes = dimension_recovery_codestream();
    let options = DecodeOptions::default();
    let expected = decode_codestream(&bytes, &options).unwrap();
    for width in [1, 2] {
        let container = jp2_for_codestream(&bytes, width, 1);
        let inspected = crate::inspect_jp2_recover_dimensions(&container, &options).unwrap();
        assert_eq!(inspected.report.header_width, width);
        assert_eq!(inspected.report.ignored_container_dimensions, width != 1);
        assert_eq!((inspected.report.width, inspected.report.height), (1, 1));
        let recovered = crate::decode_jp2_recover_dimensions(&container, &options).unwrap();
        assert_eq!(recovered.report, inspected.report);
        assert_eq!(recovered.image, expected);
        assert_eq!(
            recovered.image.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![1])
        );
        let centered =
            crate::decode_jp2_reconstructed_recover_dimensions(&container, &options).unwrap();
        assert_eq!(centered.report, inspected.report);
        assert_eq!(centered.image.component(0).unwrap().samples(), &[-127]);
        assert_eq!(centered.image.typed(options.limits()).unwrap(), expected);
        if width == 2 {
            assert!(matches!(
                decode_jp2(&container, &options),
                Err(DecodeError::MalformedInput {
                    kind: MalformedKind::ContainerCodestreamMismatch,
                    ..
                })
            ));
        }
    }
}

#[test]
fn pdf_dimensions_preserve_component_and_uniform_or_variable_precision_checks() {
    let bytes = dimension_recovery_codestream();
    let options = DecodeOptions::default();
    for (count, depth) in [(2_u16, 7_u8), (1, 6), (1, 0x87)] {
        let mut container = jp2_for_codestream(&bytes, 2, 1);
        let ihdr = container
            .windows(4)
            .position(|part| part == b"ihdr")
            .unwrap()
            + 4;
        container[ihdr + 8..ihdr + 10].copy_from_slice(&count.to_be_bytes());
        container[ihdr + 10] = depth;
        assert!(matches!(
            crate::decode_jp2_recover_dimensions(&container, &options),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::ContainerCodestreamMismatch,
                ..
            })
        ));
    }
    let mut two = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0, 0]);
    two[4..6].copy_from_slice(&44_u16.to_be_bytes());
    two[40..42].copy_from_slice(&2_u16.to_be_bytes());
    two.splice(45..45, [11, 1, 1]);
    let cod = two.windows(2).position(|pair| pair == [255, 82]).unwrap();
    two[cod + 9] = 0;
    let sot = two.windows(2).position(|pair| pair == [255, 144]).unwrap();
    two.splice(sot..sot, segment(0xff5d, &[1, 0x40, 0x60]));
    let expected = decode_codestream(&two, &options).unwrap();
    assert_eq!(expected.components().len(), 2);
    for depths in [[7_u8, 11], [7, 10], [7, 0x8b]] {
        let mut container = jp2_reconstruction_with_metadata(&two, &box32(*b"bpcc", &depths));
        let ihdr = container
            .windows(4)
            .position(|part| part == b"ihdr")
            .unwrap()
            + 4;
        container[ihdr + 4..ihdr + 8].copy_from_slice(&2_u32.to_be_bytes());
        container[ihdr + 8..ihdr + 10].copy_from_slice(&2_u16.to_be_bytes());
        container[ihdr + 10] = 255;
        if depths == [7, 11] {
            assert_eq!(
                crate::decode_jp2_recover_dimensions(&container, &options)
                    .unwrap()
                    .image,
                expected
            );
            for override_depths in [None, Some([7_u8, 11]), Some([7, 10])] {
                let mut associated = container.clone();
                associated.splice(12..32, box32(*b"ftyp", b"jpx \0\0\0\0jp2 jpx "));
                let mut header = box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]);
                if let Some(depths) = override_depths {
                    header.extend(box32(*b"bpcc", &depths));
                }
                let stream = associated
                    .windows(4)
                    .position(|part| part == b"jp2c")
                    .unwrap()
                    - 4;
                associated.splice(stream..stream, box32(*b"jpch", &header));
                let result = crate::decode_jp2_recover_dimensions(&associated, &options);
                if override_depths == Some([7, 10]) {
                    assert!(matches!(
                        result,
                        Err(DecodeError::MalformedInput {
                            kind: MalformedKind::ContainerCodestreamMismatch,
                            ..
                        })
                    ));
                } else {
                    assert_eq!(result.unwrap().image, expected);
                }
            }
        } else {
            assert!(matches!(
                crate::decode_jp2_recover_dimensions(&container, &options),
                Err(DecodeError::MalformedInput {
                    kind: MalformedKind::ContainerCodestreamMismatch,
                    ..
                })
            ));
        }
    }
}

#[test]
fn pdf_dimensions_keep_real_nonzero_origin_and_never_promote_inspection_to_pixels() {
    let options = DecodeOptions::default();
    let bytes = two_tile_codestream();
    let container = jp2_for_codestream(&bytes, 99, 1);
    let recovered = crate::decode_jp2_recover_dimensions(&container, &options).unwrap();
    assert_eq!(
        (
            recovered.image.width(),
            recovered.image.height(),
            recovered.image.x_origin()
        ),
        (5, 1, 1)
    );
    assert_eq!(
        (
            recovered.report.width,
            recovered.report.height,
            recovered.report.x_origin
        ),
        (5, 1, 1)
    );
    assert_eq!(recovered.report.header_width, 99);
    assert_eq!(
        recovered.image,
        decode_codestream(&bytes, &options).unwrap()
    );

    let mut damaged = dimension_recovery_codestream();
    let sod = damaged
        .windows(2)
        .position(|pair| pair == [255, 147])
        .unwrap();
    damaged[sod + 2] = 0xff;
    let container = jp2_for_codestream(&damaged, 2, 1);
    assert!(crate::inspect_jp2_recover_dimensions(&container, &options).is_ok());
    let expected = decode_codestream(&damaged, &options).unwrap_err();
    assert_eq!(
        crate::decode_jp2_recover_dimensions(&container, &options).err(),
        Some(expected)
    );
}

#[test]
fn pdf_dimensions_keep_limits_metadata_processing_and_refusal_restoration() {
    let options = DecodeOptions::default();
    let bytes = dimension_recovery_codestream();
    let container = jp2_for_codestream(&bytes, 2, 1);
    let expected = crate::decode_jp2_recover_dimensions(&container, &options).unwrap();
    for limits in [
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
    ] {
        assert!(matches!(
            crate::decode_jp2_recover_dimensions(&container, &DecodeOptions::new(limits)),
            Err(DecodeError::LimitExceeded { .. })
        ));
    }
    let mut oversized = container.clone();
    let ihdr = oversized
        .windows(4)
        .position(|part| part == b"ihdr")
        .unwrap()
        + 4;
    oversized[ihdr + 4..ihdr + 8]
        .copy_from_slice(&(ResourceLimits::HARDENED.maximum_width() + 1).to_be_bytes());
    assert!(matches!(
        crate::decode_jp2_recover_dimensions(&oversized, &options),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Width,
            ..
        })
    ));
    let mut completed = false;
    for after in 0..256 {
        match crate::allocation::with_refusal(after, || {
            crate::decode_jp2_recover_dimensions(&container, &options)
        }) {
            Err(DecodeError::AllocationFailed) => assert_eq!(
                crate::decode_jp2_recover_dimensions(&container, &options).unwrap(),
                expected
            ),
            Ok(actual) => {
                assert_eq!(actual, expected);
                completed = true;
                break;
            }
            Err(error) => panic!("unexpected dimension recovery refusal at {after}: {error:?}"),
        }
    }
    assert!(completed);
    let mut mapped = jp2_reconstruction_with_metadata(&bytes, &box32(*b"cmap", &[0, 0, 0, 0]));
    let ihdr = mapped.windows(4).position(|part| part == b"ihdr").unwrap() + 4;
    mapped[ihdr + 4..ihdr + 8].copy_from_slice(&2_u32.to_be_bytes());
    assert!(crate::decode_jp2_recover_dimensions(&mapped, &options).is_ok());
    assert_eq!(
        crate::decode_jp2_reconstructed_recover_dimensions(&mapped, &options).err(),
        Some(DecodeError::UnsupportedFeature {
            feature: "JP2 output transforms on reconstruction samples",
        })
    );
    assert!(decode_jp2(&container, &options).is_err());
}

#[test]
fn jp2_reconstructed_output_retains_fractional_headroom_and_coded_geometry() {
    let options = DecodeOptions::default();
    for (packet, numerator) in [
        (&[0xcf, 0xb4, 0x04, 0x09][..], -765_i64),
        (&[0xc0, 0x21, 0x03][..], 9),
    ] {
        let mut bytes = prepared_codestream(1, 1, 0, &[0x42, 0x44, 0], packet);
        let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
        bytes[cod + 9] = 0;
        let container = jp2_for_codestream(&bytes, 1, 1);
        let image = crate::decode_jp2_reconstructed(&container, &options).unwrap();
        let component = image.component(0).unwrap();
        assert_eq!(component.fraction_bits(), 16);
        assert_eq!(component.samples(), &[numerator * (1 << 14)]);
        assert_eq!(
            image,
            crate::decode_codestream_reconstructed(&bytes, &options).unwrap()
        );
        assert_eq!(
            image.typed(options.limits()),
            decode_jp2(&container, &options)
        );
    }

    let bytes = two_tile_codestream();
    let info = codestream::parse(&bytes, options.limits()).unwrap();
    let container = jp2_for_codestream(&bytes, info.image_size.width, info.image_size.height);
    let image = crate::decode_jp2_reconstructed(&container, &options).unwrap();
    assert_eq!(
        (
            image.width(),
            image.height(),
            image.x_origin(),
            image.y_origin()
        ),
        (5, 1, 1, 0)
    );
    assert_eq!(
        image,
        crate::decode_codestream_reconstructed(&bytes, &options).unwrap()
    );
    assert_eq!(
        image.typed(options.limits()),
        decode_jp2(&container, &options)
    );
}

fn jp2_reconstruction_with_metadata(bytes: &[u8], metadata: &[u8]) -> Vec<u8> {
    let mut container = jp2_for_codestream(bytes, 1, 1);
    let start = container
        .windows(4)
        .position(|part| part == b"jp2h")
        .unwrap()
        - 4;
    let length = u32::from_be_bytes(container[start..start + 4].try_into().unwrap());
    let end = start + length as usize;
    container.splice(end..end, metadata.iter().copied());
    container[start..start + 4].copy_from_slice(&(length + metadata.len() as u32).to_be_bytes());
    container
}

#[test]
fn jp2_reconstructed_output_rejects_typed_mappings_without_masking_decode_errors() {
    let options = DecodeOptions::default();
    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0]);
    let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
    bytes[cod + 9] = 0;
    let mapped = jp2_reconstruction_with_metadata(&bytes, &box32(*b"cmap", &[0, 0, 0, 0]));
    let start = mapped.windows(4).position(|part| part == b"jp2h").unwrap() - 4;
    let length = u32::from_be_bytes(mapped[start..start + 4].try_into().unwrap()) as usize;
    let mut associated = jp2_for_codestream(&bytes, 1, 1);
    associated.splice(12..32, box32(*b"ftyp", b"jpx \0\0\0\0jp2 jpx "));
    let codestream = associated
        .windows(4)
        .position(|part| part == b"jp2c")
        .unwrap()
        - 4;
    associated.splice(
        codestream..codestream,
        box32(*b"jpch", &mapped[start + 8..start + length]),
    );
    for container in [
        jp2_reconstruction_with_metadata(&bytes, &box32(*b"cmap", &[0, 0, 0, 0])),
        jp2_reconstruction_with_metadata(&bytes, &box32(*b"cdef", &[0, 1, 0, 0, 0, 0, 0, 1])),
        jp2_with_palette(&bytes, 256, true),
        associated,
    ] {
        assert!(decode_jp2(&container, &options).is_ok());
        assert_eq!(
            crate::decode_jp2_reconstructed(&container, &options),
            Err(DecodeError::UnsupportedFeature {
                feature: "JP2 output transforms on reconstruction samples",
            })
        );
        assert_eq!(
            crate::decode_jp2_reconstructed_selected(
                &container,
                &options,
                &DecodeSelection::tile(0)
            ),
            crate::decode_jp2_reconstructed(&container, &options)
        );
        let limited = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(0).unwrap());
        let expected = decode_jp2(&container, &limited).unwrap_err();
        assert!(matches!(expected, DecodeError::LimitExceeded { .. }));
        assert_eq!(
            crate::decode_jp2_reconstructed(&container, &limited),
            Err(expected)
        );
        assert_eq!(
            crate::decode_jp2_reconstructed_selected(
                &container,
                &limited,
                &DecodeSelection::tile(0)
            ),
            crate::decode_jp2_reconstructed(&container, &limited)
        );
        let mut damaged = container;
        let sod = damaged
            .windows(2)
            .position(|pair| pair == [255, 147])
            .unwrap();
        damaged[sod + 2] = 0xff;
        let expected = decode_jp2(&damaged, &options).unwrap_err();
        assert_eq!(
            crate::decode_jp2_reconstructed(&damaged, &options),
            Err(expected)
        );
        assert_eq!(
            crate::decode_jp2_reconstructed_selected(&damaged, &options, &DecodeSelection::tile(0)),
            crate::decode_jp2_reconstructed(&damaged, &options)
        );
    }
}

#[test]
fn jp2_reconstructed_output_keeps_header_profile_and_nlt_validation() {
    let options = DecodeOptions::default();
    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0]);
    let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
    bytes[cod + 9] = 0;
    let good = jp2_for_codestream(&bytes, 1, 1);
    for end in 0..good.len() {
        let expected = decode_jp2(&good[..end], &options).unwrap_err();
        assert_eq!(
            crate::decode_jp2_reconstructed(&good[..end], &options),
            Err(expected)
        );
    }
    let mut precision = good.clone();
    let ihdr = precision
        .windows(4)
        .position(|part| part == b"ihdr")
        .unwrap()
        + 4;
    precision[ihdr + 10] = 6;
    let mut components = good.clone();
    components[ihdr + 8..ihdr + 10].copy_from_slice(&2_u16.to_be_bytes());
    for bad in [jp2_for_codestream(&bytes, 2, 1), precision, components] {
        let expected = decode_jp2(&bad, &options).unwrap_err();
        assert_eq!(
            crate::decode_jp2_reconstructed(&bad, &options),
            Err(expected)
        );
    }
    let start = good.windows(4).position(|part| part == b"jp2h").unwrap() - 4;
    let length = u32::from_be_bytes(good[start..start + 4].try_into().unwrap()) as usize;
    let mut associated = good.clone();
    associated.splice(12..32, box32(*b"ftyp", b"jpx \0\0\0\0jp2 jpx "));
    let stream = associated
        .windows(4)
        .position(|part| part == b"jp2c")
        .unwrap()
        - 4;
    associated.splice(
        stream..stream,
        box32(*b"jpch", &good[start + 8..start + length]),
    );
    assert_eq!(
        crate::decode_jp2_reconstructed(&associated, &options),
        crate::decode_codestream_reconstructed(&bytes, &options)
    );
    let jpch = associated
        .windows(4)
        .position(|part| part == b"jpch")
        .unwrap()
        + 4;
    let local_ihdr = associated[jpch..]
        .windows(4)
        .position(|part| part == b"ihdr")
        .unwrap()
        + jpch;
    associated[local_ihdr..local_ihdr + 4].copy_from_slice(b"skip");
    assert!(decode_jp2(&associated, &options).is_ok());
    assert_eq!(
        crate::decode_jp2_reconstructed(&associated, &options),
        crate::decode_codestream_reconstructed(&bytes, &options)
    );
    let sot = bytes
        .windows(2)
        .position(|pair| pair == [255, 144])
        .unwrap();
    bytes.splice(sot..sot, segment(0xff76, &[255, 255, 7, 0]));
    let container = jp2_for_codestream(&bytes, 1, 1);
    assert!(decode_jp2(&container, &options).is_ok());
    assert_eq!(
        crate::decode_jp2_reconstructed(&container, &options),
        Err(DecodeError::UnsupportedFeature {
            feature: "nonlinear transforms on reconstruction samples",
        })
    );
}

#[test]
fn jp2_reconstructed_output_propagates_refused_storage_and_limits_then_recovers() {
    let options = DecodeOptions::default();
    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0xcf, 0xb4, 0x04, 0x09]);
    let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
    bytes[cod + 9] = 0;
    let container = jp2_for_codestream(&bytes, 1, 1);
    let expected = crate::decode_jp2_reconstructed(&container, &options).unwrap();
    let mut completed = false;
    for after in 0..256 {
        let result = crate::allocation::with_refusal(after, || {
            crate::decode_jp2_reconstructed(&container, &options)
        });
        match result {
            Err(DecodeError::AllocationFailed) => assert_eq!(
                crate::decode_jp2_reconstructed(&container, &options).unwrap(),
                expected
            ),
            Ok(image) => {
                assert_eq!(image, expected);
                completed = true;
                break;
            }
            Err(error) => panic!("unexpected managed refusal result at {after}: {error:?}"),
        }
    }
    assert!(completed);
    for limits in [
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
    ] {
        let limited = DecodeOptions::new(limits);
        let error = decode_jp2(&container, &limited).unwrap_err();
        assert!(matches!(error, DecodeError::LimitExceeded { .. }));
        assert_eq!(
            crate::decode_jp2_reconstructed(&container, &limited),
            Err(error)
        );
    }
    assert_eq!(
        crate::decode_jp2_reconstructed(&container, &options).unwrap(),
        expected
    );
}

#[test]
fn reconstructed_output_roundtrips_independent_packets_and_retains_coded_geometry() {
    let options = DecodeOptions::default();
    for (sample, packet) in [
        (1_i64, &[0xcf, 0xb4, 0x04, 0x09][..]),
        (129, &[0xc0, 0x21, 0x03][..]),
        (200, &[0xcf, 0xb4, 0x08, 0x04, 0x4f][..]),
    ] {
        let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], packet);
        let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
        bytes[cod + 9] = 0;
        for signed in [false, true] {
            bytes[42] = if signed { 0x87 } else { 7 };
            let image = crate::decode_codestream_reconstructed(&bytes, &options).unwrap();
            let component = image.component(0).unwrap();
            assert_eq!(component.fraction_bits(), 0);
            assert_eq!(component.samples(), &[sample - 128]);
            assert_eq!(component.info().signed, signed);
            assert_eq!(
                image.typed(options.limits()),
                decode_codestream(&bytes, &options)
            );
        }
    }

    let mut registered = prepared_codestream(7, 5, 1, &[0x40, 0x40], &[0]);
    let cod = registered
        .windows(2)
        .position(|pair| pair == [255, 82])
        .unwrap();
    registered[cod + 9] = 0;
    registered[16..20].copy_from_slice(&1_u32.to_be_bytes());
    registered[20..24].copy_from_slice(&1_u32.to_be_bytes());
    registered[43] = 2;
    registered[44] = 3;
    let sot = registered.windows(2).position(|p| p == [255, 144]).unwrap();
    registered.splice(sot..sot, segment(0xff63, &[0x40, 0, 0x80, 0]));
    for (bytes, geometry, dimensions, sampling) in [
        (two_tile_codestream(), (5, 1, 1, 0), (5, 1), (1, 1, 0, 0)),
        (registered, (6, 4, 1, 1), (3, 1), (2, 3, 0x4000, 0x8000)),
    ] {
        let image = crate::decode_codestream_reconstructed(&bytes, &options).unwrap();
        assert_eq!(
            (
                image.width(),
                image.height(),
                image.x_origin(),
                image.y_origin()
            ),
            geometry
        );
        let component = image.component(0).unwrap();
        let info = component.info();
        assert_eq!(
            (
                info.x_subsampling,
                info.y_subsampling,
                info.x_registration,
                info.y_registration
            ),
            sampling
        );
        assert_eq!((component.width(), component.height()), dimensions);
        assert_eq!(
            component.samples(),
            vec![0; (dimensions.0 * dimensions.1) as usize]
        );
        assert_eq!(
            image.typed(options.limits()),
            decode_codestream(&bytes, &options)
        );
    }
}

#[test]
fn reconstructed_output_retains_fractional_overshoot_before_typed_rounding_and_clipping() {
    let options = DecodeOptions::default();
    // Independent OpenJPEG entropy bytes for centered -127 and +1. With no
    // DWT levels and step 3/2, midpoint reconstruction is -765/4 and +9/4.
    for (packet, numerator, typed) in [
        (&[0xcf, 0xb4, 0x04, 0x09][..], -765_i64, 0_u64),
        (&[0xc0, 0x21, 0x03][..], 9, 130),
    ] {
        let mut bytes = prepared_codestream(1, 1, 0, &[0x42, 0x44, 0], packet);
        let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
        bytes[cod + 9] = 0;
        let image = crate::decode_codestream_reconstructed(&bytes, &options).unwrap();
        let component = image.component(0).unwrap();
        assert_eq!(component.fraction_bits(), 16);
        assert_eq!(component.samples(), &[numerator * (1 << 14)]);
        let converted = image.typed(options.limits()).unwrap();
        assert_eq!(
            converted.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![typed])
        );
        assert_eq!(Ok(converted), decode_codestream(&bytes, &options));
        if numerator < 0 {
            // Average with centered zero before final conversion: 259/8,
            // rather than the early-clipped typed average of 64.
            let late_numerator = i128::from(component.samples()[0]) + (256_i128 << 16);
            assert_eq!(late_numerator * 8, 259 * (2_i128 << 16));
            assert_ne!(
                late_numerator / (2_i128 << 16),
                i128::from((typed + 128) / 2)
            );
        }
    }
    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0]);
    let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
    bytes[cod + 9] = 0;
    let bytes = add_single_component_mct(bytes, 1, 300);
    let image = crate::decode_codestream_reconstructed(&bytes, &options).unwrap();
    assert_eq!(image.component(0).unwrap().samples(), &[300]);
    assert_eq!(
        image.typed(options.limits()),
        decode_codestream(&bytes, &options)
    );
    assert_eq!(
        image
            .typed(options.limits())
            .unwrap()
            .component(0)
            .unwrap()
            .samples(),
        &TypedSamples::Unsigned(vec![255])
    );
}

#[test]
fn reconstructed_recovery_preserves_fractional_overshoot_before_typed_conversion() {
    let options = DecodeOptions::default();
    for (packet, numerator) in [
        (&[0xcf, 0xb4, 0x04, 0x09][..], -765_i64),
        (&[0xc0, 0x21, 0x03][..], 9),
    ] {
        let mut original = prepared_codestream(1, 1, 0, &[0x42, 0x44, 0], packet);
        let cod = original
            .windows(2)
            .position(|pair| pair == [255, 82])
            .unwrap();
        original[cod + 9] = 0;
        let sot = original
            .windows(2)
            .position(|pair| pair == [255, 144])
            .unwrap();
        assert!(original.ends_with(&[0xff, 0xd9]));
        let mut bytes = original[..original.len() - 2].to_vec();
        bytes[sot + 6..sot + 10].fill(0);
        let recovered =
            crate::decode_codestream_reconstructed_recover_missing_eoc(&bytes, &options).unwrap();
        let component = recovered.image.component(0).unwrap();
        assert_eq!(component.fraction_bits(), 16);
        assert_eq!(component.samples(), &[numerator * (1 << 14)]);
        assert_eq!(
            recovered.image,
            crate::decode_codestream_reconstructed(&original, &options).unwrap()
        );
        assert_eq!(
            recovered.image.typed(options.limits()),
            decode_codestream(&original, &options)
        );
        assert!(recovered.report.appended_eoc);
        assert_eq!(recovered.report.original_bytes, bytes.len() as u64);
        assert_eq!(recovered.report.effective_bytes, original.len() as u64);
    }
}

#[test]
fn reconstructed_output_rejects_main_and_tile_typed_domain_nlt_without_masking_decode_errors() {
    let options = DecodeOptions::default();
    for tile in [false, true] {
        for kind in [0_u8, 3] {
            let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0xcf, 0xb4, 0x04, 0x09]);
            let cod = bytes.windows(2).position(|pair| pair == [255, 82]).unwrap();
            bytes[cod + 9] = 0;
            bytes[42] = 0x87;
            let sot = bytes
                .windows(2)
                .position(|pair| pair == [255, 144])
                .unwrap();
            let nlt = segment(0xff76, &[255, 255, 0x87, kind]);
            if tile {
                let length = u32::from_be_bytes(bytes[sot + 6..sot + 10].try_into().unwrap());
                bytes[sot + 6..sot + 10]
                    .copy_from_slice(&(length + nlt.len() as u32).to_be_bytes());
                bytes.splice(sot + 12..sot + 12, nlt);
            } else {
                bytes.splice(sot..sot, nlt);
            }
            assert_eq!(
                decode_codestream(&bytes, &options)
                    .unwrap()
                    .component(0)
                    .unwrap()
                    .samples(),
                &TypedSamples::Signed(vec![if kind == 0 { -127 } else { -2 }])
            );
            assert_eq!(
                crate::decode_codestream_reconstructed(&bytes, &options),
                Err(DecodeError::UnsupportedFeature {
                    feature: "nonlinear transforms on reconstruction samples"
                })
            );
            let limited =
                DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(0).unwrap());
            let expected = decode_codestream(&bytes, &limited).unwrap_err();
            assert!(matches!(
                expected,
                DecodeError::LimitExceeded {
                    resource: Resource::Packets,
                    ..
                }
            ));
            assert_eq!(
                crate::decode_codestream_reconstructed(&bytes, &limited),
                Err(expected)
            );
            let sod = bytes
                .windows(2)
                .position(|pair| pair == [255, 147])
                .unwrap();
            bytes[sod + 2] = 0xff;
            let expected = decode_codestream(&bytes, &options).unwrap_err();
            assert_eq!(
                crate::decode_codestream_reconstructed(&bytes, &options),
                Err(expected)
            );
        }
    }
}

#[test]
fn reconstructed_output_keeps_strict_errors_limits_and_success_after_failure() {
    let bytes = two_tile_codestream();
    let options = DecodeOptions::default();
    let expected = crate::decode_codestream_reconstructed(&bytes, &options).unwrap();
    for end in 0..bytes.len() {
        let error = decode_codestream(&bytes[..end], &options).unwrap_err();
        assert_eq!(
            crate::decode_codestream_reconstructed(&bytes[..end], &options),
            Err(error)
        );
    }
    for limits in [
        ResourceLimits::HARDENED
            .with_maximum_input_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
    ] {
        let limited = DecodeOptions::new(limits);
        let error = decode_codestream(&bytes, &limited).unwrap_err();
        assert!(matches!(error, DecodeError::LimitExceeded { .. }));
        assert_eq!(
            crate::decode_codestream_reconstructed(&bytes, &limited),
            Err(error)
        );
        assert_eq!(
            crate::decode_codestream_reconstructed(&bytes, &options).unwrap(),
            expected
        );
    }
    let container = jp2_for_codestream(&bytes, 5, 1);
    let error = decode_codestream(&container, &options).unwrap_err();
    assert_eq!(
        crate::decode_codestream_reconstructed(&container, &options),
        Err(error)
    );
}

#[test]
fn actual_raw_typed_result_derives_full_and_reduced_signed_unsigned_planes_from_bytes() {
    let options = DecodeOptions::default();
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let mut cases = 0;
    for width in [1_u32, 2, 5, 9] {
        for height in [1_u32, 3, 7] {
            for signed in [false, true] {
                let mut bytes = prepared_codestream(width, height, 1, &qcd, &[0, 0, 0]);
                bytes[42] = if signed { 0x87 } else { 7 };
                let full = decode_codestream(&bytes, &options).unwrap();
                assert_eq!((full.width(), full.height()), (width, height));
                assert_eq!((full.x_origin(), full.y_origin()), (0, 0));
                for levels in 0..=2 {
                    let request = DecodeSelection::full_image().with_discard_levels(levels);
                    let image = decode_codestream_selected(&bytes, &options, &request).unwrap();
                    let scale = 1_u32 << levels;
                    let expected_width = width.div_ceil(scale);
                    let expected_height = height.div_ceil(scale);
                    assert_eq!(
                        (image.width(), image.height()),
                        (expected_width, expected_height)
                    );
                    assert_eq!(image.components().len(), 1);
                    let component = image.component(0).unwrap();
                    assert_eq!(component.info().precision, 8);
                    assert_eq!(component.info().signed, signed);
                    let count = usize::try_from(expected_width * expected_height).unwrap();
                    let expected = if signed {
                        TypedSamples::Signed(vec![0; count])
                    } else {
                        TypedSamples::Unsigned(vec![128; count])
                    };
                    assert_eq!(component.samples(), &expected);
                    cases += 1;
                }
                let expected = if signed {
                    TypedSamples::Signed(vec![0; (width * height) as usize])
                } else {
                    TypedSamples::Unsigned(vec![128; (width * height) as usize])
                };
                assert_eq!(full.component(0).unwrap().samples(), &expected);
            }
        }
    }
    assert_eq!(cases, 72);
}

#[test]
fn actual_raw_typed_result_preserves_parser_selection_and_backend_budget_first_errors() {
    let bytes = two_tile_codestream();
    let invalid = DecodeSelection::tile(u16::MAX);
    for (limits, expected) in [
        (
            ResourceLimits::HARDENED
                .with_maximum_input_bytes(0)
                .unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::InputBytes,
                limit: 0,
                actual: bytes.len() as u64,
            },
        ),
        (
            ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
            DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: 0,
                actual: 1,
            },
        ),
    ] {
        let options = DecodeOptions::new(limits);
        assert_eq!(decode_codestream(&bytes, &options), Err(expected));
        assert_eq!(
            decode_codestream_selected(&bytes, &options, &invalid),
            Err(expected)
        );
    }
    let options = DecodeOptions::new(ResourceLimits::HARDENED.with_maximum_packets(0).unwrap());
    assert_eq!(
        decode_codestream(&bytes, &options),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: 0,
            actual: 1
        }),
    );
    assert_eq!(
        decode_codestream_selected(&bytes, &options, &invalid),
        Err(DecodeError::InvalidSelection {
            reason: SelectionError::TileOutOfRange
        }),
    );
    for (request, reason) in [
        (
            DecodeSelection::tiles(Vec::new()),
            SelectionError::EmptyTileSet,
        ),
        (
            DecodeSelection::tiles(vec![0, 0]),
            SelectionError::DuplicateTile,
        ),
        (
            DecodeSelection::full_image().with_discard_levels(u8::MAX),
            SelectionError::ReductionTooLarge,
        ),
    ] {
        assert_eq!(
            decode_codestream_selected(&bytes, &DecodeOptions::default(), &request),
            Err(DecodeError::InvalidSelection { reason }),
        );
    }
    for end in 0..bytes.len() {
        let full = decode_codestream(&bytes[..end], &DecodeOptions::default());
        assert!(full.is_err(), "truncated source at {end}");
        assert_eq!(
            decode_codestream_selected(&bytes[..end], &DecodeOptions::default(), &invalid),
            full
        );
    }
}

#[test]
fn actual_raw_typed_result_joins_real_packed_packets_mct_and_nonlinear_regions() {
    let mut basic = prepared_codestream(1, 1, 1, &[0, 0x40], &[0]);
    let cod = basic
        .windows(2)
        .position(|pair| pair == [0xff, 0x52])
        .unwrap();
    basic[cod + 9] = 0;
    let transformed = add_second_component_mct_stage(add_single_component_mct(basic, 2, 3), -4, 5);
    for packed in [None, Some(false), Some(true)] {
        let bytes = match packed {
            None => transformed.clone(),
            Some(ppm) => pack_packet_header(transformed.clone(), ppm, &[0]),
        };
        for selected in [false, true] {
            let image = if selected {
                decode_codestream_selected(
                    &bytes,
                    &DecodeOptions::default(),
                    &DecodeSelection::full_image(),
                )
            } else {
                decode_codestream(&bytes, &DecodeOptions::default())
            }
            .unwrap();
            assert_eq!(
                image.component(0).unwrap().samples(),
                &TypedSamples::Unsigned(vec![136])
            );
        }
    }
    let mut nonlinear = prepared_codestream(1, 1, 1, &[0x40, 0x40], &[0xcf, 0xb4, 0x04, 0x09]);
    let cod = nonlinear
        .windows(2)
        .position(|pair| pair == [0xff, 0x52])
        .unwrap();
    nonlinear[cod + 9] = 0;
    nonlinear[42] = 0x87;
    let plain = decode_codestream(&nonlinear, &DecodeOptions::default()).unwrap();
    assert_eq!(
        plain.component(0).unwrap().samples(),
        &TypedSamples::Signed(vec![-127])
    );
    let sot = nonlinear
        .windows(2)
        .position(|pair| pair == [0xff, 0x90])
        .unwrap();
    nonlinear.splice(sot..sot, segment(0xff76, &[0xff, 0xff, 0x87, 3]));
    let expected = TypedSamples::Signed(vec![-2]);
    assert_eq!(
        decode_codestream(&nonlinear, &DecodeOptions::default())
            .unwrap()
            .component(0)
            .unwrap()
            .samples(),
        &expected
    );
    assert_eq!(
        decode_codestream_selected(
            &nonlinear,
            &DecodeOptions::default(),
            &DecodeSelection::full_image()
        )
        .unwrap()
        .component(0)
        .unwrap()
        .samples(),
        &expected,
    );
}

#[test]
fn actual_raw_typed_result_keeps_independently_encoded_nonzero_samples_and_selected_geometry() {
    for (sample, packet) in [
        (1, &[0xcf, 0xb4, 0x04, 0x09][..]),
        (129, &[0xc0, 0x21, 0x03][..]),
        (200, &[0xcf, 0xb4, 0x08, 0x04, 0x4f][..]),
    ] {
        let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], packet);
        let cod = bytes
            .windows(2)
            .position(|pair| pair == [0xff, 0x52])
            .unwrap();
        bytes[cod + 9] = 0;
        let full = decode_codestream(&bytes, &DecodeOptions::default()).unwrap();
        let selected = decode_codestream_selected(
            &bytes,
            &DecodeOptions::default(),
            &DecodeSelection::tile(0),
        )
        .unwrap();
        assert_eq!(full, selected);
        assert_eq!(
            full.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![sample])
        );
    }
    let bytes = two_tile_codestream();
    let request = DecodeSelection::full_image().with_region(crate::ImageRegion::new(2, 0, 3, 1));
    let selected = decode_codestream_selected(&bytes, &DecodeOptions::default(), &request).unwrap();
    assert_eq!((selected.width(), selected.height()), (3, 1));
    assert_eq!(
        selected.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(vec![128; 3])
    );
}
