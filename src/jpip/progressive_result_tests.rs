use super::super::cache_layout_result_tests::{bin, frame, id, storage};
use super::super::response_result_tests::data;
use super::super::tests::decodable_codestream_with_layers;
use super::*;

fn plan() -> JpipPrecinctCodestreamPlan {
    let packets = (0..3)
        .map(|layer| {
            super::super::JpipPrecinctPacket::new(id(0, 3, 7), layer, u64::from(layer), 1).unwrap()
        })
        .collect();
    JpipPrecinctCodestreamPlan::new(
        id(6, 3, 0),
        id(2, 3, 0),
        packets,
        3,
        &ResourceLimits::HARDENED,
    )
    .unwrap()
}

fn owners(decoder: &JpipProgressiveDecoder) -> ((usize, usize, usize), (usize, usize, usize)) {
    (
        storage(&decoder.plan.packets),
        storage(&decoder.plan.layer_ends),
    )
}

fn complete_cache() -> DatabinCache {
    let bytes = decodable_codestream_with_layers(3);
    let start = bytes
        .windows(2)
        .position(|bytes| bytes == [0xff, 0x90])
        .unwrap();
    let mut input = data(3, true, 0, 6, 3, 0, &bytes[..start]);
    input.extend(data(3, true, 0, 2, 3, 0, &bytes[start..start + 14]));
    input.extend(data(3, false, 7, 0, 3, 0, &[0, 0, 0]));
    let mut cache = DatabinCache::new(ResourceLimits::HARDENED);
    super::super::ingest_jpip_response(&input, &mut cache).unwrap();
    cache
}

#[test]
fn actual_jpip_progressive_constructor_waiting_protocol_errors_and_plan_owner_are_exact() {
    let plan = plan();
    let incoming = (storage(&plan.packets), storage(&plan.layer_ends));
    let mut decoder = JpipProgressiveDecoder::new(plan);
    assert_eq!(owners(&decoder), incoming);
    assert!(std::ptr::eq(decoder.plan(), &decoder.plan));
    assert_eq!(decoder.decoded_layers(), 0);
    let empty = DatabinCache::new(ResourceLimits::HARDENED);
    for previous in [0, 1, 2, 3, u16::MAX] {
        decoder.decoded_layers = previous;
        let before = frame(&empty);
        let result = decoder.update_selected(
            &empty,
            &crate::DecodeOptions::default(),
            &crate::DecodeSelection::tile(99),
        );
        if previous == 0 {
            let update = result.unwrap();
            assert_eq!(update.status(), JpipProgressiveStatus::WaitingForData);
            assert_eq!(
                (update.previous_layers(), update.available_layers()),
                (0, 0)
            );
            assert_eq!(
                update.missing_ranges(),
                &[
                    JpipMissingRange {
                        databin: id(6, 3, 0),
                        offset: 0,
                        length: None
                    },
                    JpipMissingRange {
                        databin: id(2, 3, 0),
                        offset: 0,
                        length: None
                    },
                ]
            );
            assert!(update.image().is_none());
            assert!(update.into_image().is_none());
        } else {
            assert_eq!(
                result.err(),
                Some(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout))
            );
        }
        assert_eq!(decoder.decoded_layers(), previous);
        assert_eq!(owners(&decoder), incoming);
        assert_eq!(frame(&empty), before);
    }
    let cache = DatabinCache {
        limits: ResourceLimits::HARDENED,
        databins: vec![
            bin(id(6, 3, 0), &[], Some(0)),
            bin(id(2, 3, 0), &[], Some(0)),
        ],
        stored_bytes: u64::MAX,
        accepted_fragments: u64::MAX,
    };
    decoder.plan.packets.clear();
    decoder.plan.layer_ends = vec![0, 0, 0];
    for previous in [0, 2, 3, 4] {
        decoder.decoded_layers = previous;
        let owner = owners(&decoder);
        let result = decoder.update(&cache, &crate::DecodeOptions::default());
        if previous == 3 {
            let update = result.unwrap();
            assert_eq!(update.status(), JpipProgressiveStatus::Complete);
            assert_eq!(
                (update.previous_layers(), update.available_layers()),
                (3, 3)
            );
            assert!(update.image().is_none());
        } else {
            let kind = if previous > 3 {
                MalformedKind::InvalidJpipLayout
            } else {
                MalformedKind::MissingRequiredStructure
            };
            assert_eq!(result.err(), Some(DecodeError::malformed(0, kind)));
        }
        assert_eq!(decoder.decoded_layers(), previous);
        assert_eq!(owners(&decoder), owner);
    }
}

#[test]
fn actual_jpip_progressive_raw_updates_return_complete_images_and_original_optional_image_owners() {
    let mut cache = complete_cache();
    cache
        .databins
        .retain(|bin| bin.id.class() != super::super::DatabinClass::Precinct);
    let mut decoder = JpipProgressiveDecoder::new(plan());
    let owner = owners(&decoder);
    for available in 1..=3 {
        let response = data(3, false, 7, 0, 3, available - 1, &[0]);
        super::super::ingest_jpip_response(&response, &mut cache).unwrap();
        let before = frame(&cache);
        let update = decoder
            .update(&cache, &crate::DecodeOptions::default())
            .unwrap();
        assert_eq!(update.previous_layers(), u16::from(available - 1));
        assert_eq!(update.available_layers(), u16::from(available));
        assert_eq!(
            update.status(),
            if available == 3 {
                JpipProgressiveStatus::Complete
            } else {
                JpipProgressiveStatus::QualityAdvanced
            }
        );
        if available < 3 {
            assert_eq!(
                update.missing_ranges(),
                &[JpipMissingRange {
                    databin: id(0, 3, 7),
                    offset: u64::from(available),
                    length: Some(1),
                }]
            );
        } else {
            assert!(update.missing_ranges().is_empty());
        }
        let bytes = decodable_codestream_with_layers(u16::from(available));
        let expected = crate::decode_codestream(&bytes, &crate::DecodeOptions::default()).unwrap();
        let borrowed = update.image().unwrap();
        assert_eq!(borrowed, &expected);
        assert!(std::ptr::eq(borrowed, update.image.as_ref().unwrap()));
        assert_eq!((borrowed.width(), borrowed.height()), (1, 1));
        assert_eq!(
            borrowed.components()[0].samples(),
            &crate::image::TypedSamples::Unsigned(vec![128])
        );
        let components = borrowed.components().as_ptr() as usize;
        let samples = match borrowed.components()[0].samples() {
            crate::image::TypedSamples::Unsigned(values) => storage(values),
            crate::image::TypedSamples::Signed(_) => panic!("unsigned emitted fixture"),
        };
        let image = update.into_image().unwrap();
        assert_eq!(image.components().as_ptr() as usize, components);
        match image.components()[0].samples() {
            crate::image::TypedSamples::Unsigned(values) => assert_eq!(storage(values), samples),
            crate::image::TypedSamples::Signed(_) => panic!("unsigned emitted fixture"),
        }
        assert_eq!(decoder.decoded_layers(), u16::from(available));
        let repeated = decoder
            .update(&cache, &crate::DecodeOptions::default())
            .unwrap();
        assert_eq!(
            repeated.status(),
            if available == 3 {
                JpipProgressiveStatus::Complete
            } else {
                JpipProgressiveStatus::WaitingForData
            }
        );
        assert_eq!(
            (repeated.previous_layers(), repeated.available_layers()),
            (u16::from(available), u16::from(available))
        );
        assert!(repeated.image().is_none());
        assert_eq!(owners(&decoder), owner);
        assert_eq!(frame(&cache), before);
    }
}

#[test]
fn actual_jpip_progressive_full_selected_decode_errors_preserve_prior_state_and_skip_unneeded_decoding()
 {
    let cache = complete_cache();
    let before = frame(&cache);
    let bytes = decodable_codestream_with_layers(3);
    let selections = [
        None,
        Some(crate::DecodeSelection::full_image()),
        Some(crate::DecodeSelection::tile(0)),
        Some(crate::DecodeSelection::tile(1)),
        Some(crate::DecodeSelection::full_image().with_discard_levels(1)),
        Some(crate::DecodeSelection::full_image().with_region(crate::ImageRegion::new(0, 0, 1, 1))),
        Some(crate::DecodeSelection::full_image().with_region(crate::ImageRegion::new(2, 0, 1, 1))),
    ];
    for input in [1, bytes.len() as u64 - 1, bytes.len() as u64, 1 << 31] {
        let options = crate::DecodeOptions::new(
            ResourceLimits::HARDENED
                .with_maximum_input_bytes(input)
                .unwrap(),
        );
        for selection in &selections {
            for previous in [0, 1, 2, 3, 4, u16::MAX] {
                let mut decoder = JpipProgressiveDecoder {
                    plan: plan(),
                    decoded_layers: previous,
                };
                let owner = owners(&decoder);
                let actual = match selection {
                    None => decoder.update(&cache, &options),
                    Some(selection) => decoder.update_selected(&cache, &options, selection),
                };
                if previous > 3 {
                    assert_eq!(
                        actual.err(),
                        Some(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout))
                    );
                    assert_eq!(decoder.decoded_layers(), previous);
                } else if previous == 3 {
                    let update = actual.unwrap();
                    assert_eq!(update.status(), JpipProgressiveStatus::Complete);
                    assert_eq!(
                        (update.previous_layers(), update.available_layers()),
                        (3, 3)
                    );
                    assert!(update.image().is_none());
                    assert_eq!(decoder.decoded_layers(), 3);
                } else {
                    let expected = match selection {
                        None => crate::decode_codestream(&bytes, &options),
                        Some(selection) => {
                            crate::decode_codestream_selected(&bytes, &options, selection)
                        }
                    };
                    match expected {
                        Err(error) => {
                            assert_eq!(actual.err(), Some(error));
                            assert_eq!(decoder.decoded_layers(), previous);
                        }
                        Ok(image) => {
                            let update = actual.unwrap();
                            assert_eq!(update.status(), JpipProgressiveStatus::Complete);
                            assert_eq!(
                                (update.previous_layers(), update.available_layers()),
                                (previous, 3)
                            );
                            assert!(update.missing_ranges().is_empty());
                            assert_eq!(update.image(), Some(&image));
                            assert_eq!(decoder.decoded_layers(), 3);
                        }
                    }
                }
                assert_eq!(owners(&decoder), owner);
                assert_eq!(frame(&cache), before);
            }
        }
    }
}
