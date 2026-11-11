use super::super::JpipAvailability;
use super::super::cache_layout_result_tests::{bin, frame, id, storage};
use super::super::response_result_tests::data;
use super::super::tests::decodable_codestream_with_layers;
use super::*;

fn malformed(offset: usize, kind: MalformedKind) -> DecodeError {
    DecodeError::malformed(offset as u64, kind)
}

fn cod(extra: usize) -> Vec<u8> {
    let mut bytes = vec![
        0xff,
        0x52,
        0,
        u8::try_from(7 + extra).unwrap(),
        0,
        0,
        0x12,
        0x34,
        0,
    ];
    bytes.resize(9 + extra, 0x7e);
    bytes
}

#[test]
fn actual_jpip_cod_header_scans_preserve_exact_patches_and_partial_mutations_at_every_cut() {
    let segments = [cod(0), vec![0xff, 0x64, 0, 4, 9, 8], cod(4)];
    let mut cases = 0;
    for start in [0, 2, 7] {
        for layers in [0, 1, 255, 256, 257, u16::MAX] {
            for stop in [false, true] {
                for terminator in [false, true] {
                    let mut source = vec![0xa5; start];
                    let mut spans = Vec::new();
                    for (index, segment) in segments.iter().enumerate() {
                        let begin = source.len();
                        source.extend(segment);
                        spans.push((begin, source.len(), index != 1));
                    }
                    let end = source.len();
                    if terminator {
                        source.extend_from_slice(&[0xff, 0x93]);
                    }
                    for cut in 0..=source.len() {
                        let mut actual = source[..cut].to_vec();
                        let owner = storage(&actual);
                        let mut expected = actual.clone();
                        for &(begin, finish, is_cod) in &spans {
                            if finish <= cut && is_cod {
                                expected[begin + 6..begin + 8]
                                    .copy_from_slice(&layers.to_be_bytes());
                            }
                        }
                        let result = if cut < start {
                            Err(malformed(start, MalformedKind::Truncated))
                        } else if let Some(&(begin, _, _)) = spans
                            .iter()
                            .find(|&&(begin, finish, _)| begin < cut && cut < finish)
                        {
                            Err(malformed(begin, MalformedKind::Truncated))
                        } else if cut == end + 1 {
                            Err(malformed(end, MalformedKind::Truncated))
                        } else if terminator && cut == end + 2 {
                            if stop {
                                Ok(())
                            } else {
                                Err(malformed(end, MalformedKind::InvalidMarkerOrder))
                            }
                        } else if stop {
                            Err(malformed(cut, MalformedKind::MissingRequiredStructure))
                        } else {
                            Ok(())
                        };
                        assert_eq!(patch_cod_layers(&mut actual, start, layers, stop), result);
                        assert_eq!(actual, expected);
                        assert_eq!(storage(&actual), owner);
                        cases += 1;
                    }
                }
            }
        }
    }
    for (tail, kind) in [
        (vec![0xff, 0x4f], MalformedKind::InvalidMarkerOrder),
        (vec![0xff, 0xd9], MalformedKind::InvalidMarkerOrder),
        (vec![0xff, 0x90], MalformedKind::InvalidMarkerOrder),
        (vec![0xff, 0x64, 0, 1], MalformedKind::InvalidMarkerLength),
        (
            vec![0xff, 0x52, 0, 6, 0, 0, 0, 0],
            MalformedKind::InvalidCodingStyle,
        ),
    ] {
        let mut bytes = cod(0);
        bytes.extend(tail);
        let mut expected = bytes.clone();
        expected[6..8].copy_from_slice(&257_u16.to_be_bytes());
        assert_eq!(
            patch_cod_layers(&mut bytes, 0, 257, false),
            Err(malformed(9, kind))
        );
        assert_eq!(bytes, expected);
    }
    assert!(cases > 2000);
}

fn plan() -> JpipPrecinctCodestreamPlan {
    JpipPrecinctCodestreamPlan {
        main_header: id(6, 3, 0),
        tile_header: id(2, 3, 0),
        packets: (0..3)
            .map(|layer| JpipPrecinctPacket {
                range: JpipDatabinRange {
                    databin: id(0, 3, 7),
                    offset: u64::from(layer),
                    length: 1,
                },
                layer,
            })
            .collect(),
        layer_ends: vec![1, 2, 3],
    }
}

#[test]
fn actual_jpip_transcode_composes_raw_responses_to_exact_owned_codestreams_and_public_images() {
    let original = decodable_codestream_with_layers(3);
    let start = original
        .windows(2)
        .position(|bytes| bytes == [0xff, 0x90])
        .unwrap();
    let packet_start = start + 14;
    let plan = plan();
    let packet_owner = storage(&plan.packets);
    let ends_owner = storage(&plan.layer_ends);
    for requested in 1..=3 {
        let mut cache = DatabinCache::new(ResourceLimits::HARDENED);
        let mut response = data(3, true, 0, 6, 3, 0, &original[..start]);
        response.extend(data(3, true, 0, 2, 3, 0, &original[start..packet_start]));
        assert_eq!(
            super::super::ingest_jpip_response(&response, &mut cache)
                .unwrap()
                .messages(),
            2
        );
        let unavailable = cache
            .transcode_precinct_codestream(&plan, requested)
            .unwrap();
        assert_eq!(unavailable.layers(), requested);
        assert_eq!(
            unavailable.availability().status(),
            JpipAvailability::Partial
        );
        assert!(unavailable.codestream().is_none());
        let response = data(3, false, 7, 0, 3, 0, &[0, 0, 0]);
        super::super::ingest_jpip_response(&response, &mut cache).unwrap();
        let before = frame(&cache);
        let output = cache
            .transcode_precinct_codestream(&plan, requested)
            .unwrap();
        assert_eq!(output.layers(), requested);
        assert!(std::ptr::eq(output.availability(), &output.availability));
        assert_eq!(output.availability().status(), JpipAvailability::Available);
        assert_eq!(
            output.availability().required_bytes(),
            (packet_start + usize::from(requested)) as u64
        );
        assert_eq!(
            output.availability().available_bytes(),
            output.availability().required_bytes()
        );
        assert!(output.availability().missing_ranges().is_empty());
        let expected = decodable_codestream_with_layers(requested);
        assert_eq!(output.codestream().unwrap().as_bytes(), expected);
        let owner = storage(&output.codestream.as_ref().unwrap().bytes);
        let bytes = output.into_codestream().unwrap();
        assert_eq!(storage(&bytes.bytes), owner);
        let image =
            crate::decode_codestream(bytes.as_bytes(), &crate::DecodeOptions::default()).unwrap();
        assert_eq!((image.width(), image.height()), (1, 1));
        assert_eq!(frame(&cache), before);
        assert_eq!(storage(&plan.packets), packet_owner);
        assert_eq!(storage(&plan.layer_ends), ends_owner);
    }
}

type Observed<'a> = Result<(u16, &'a JpipAvailabilityReport, Option<&'a [u8]>), DecodeError>;

fn observed(value: &Result<JpipPrecinctTranscode, DecodeError>) -> Observed<'_> {
    match value {
        Err(error) => Err(*error),
        Ok(value) => Ok((
            value.layers,
            &value.availability,
            value
                .codestream
                .as_ref()
                .map(|bytes| bytes.bytes.as_slice()),
        )),
    }
}

#[test]
fn actual_jpip_transcode_preserves_physical_header_layer_limit_and_raw_validation_error_frontiers()
{
    let original = decodable_codestream_with_layers(3);
    let start = original
        .windows(2)
        .position(|bytes| bytes == [0xff, 0x90])
        .unwrap();
    let plan = plan();
    for requested in [0, 1, 2, 3, 4, u16::MAX] {
        for limit in [
            1,
            14,
            64,
            original.len() as u64 - 2,
            original.len() as u64 - 1,
            original.len() as u64,
            1 << 31,
        ] {
            let cache = DatabinCache {
                limits: ResourceLimits::HARDENED
                    .with_maximum_input_bytes(limit)
                    .unwrap(),
                databins: vec![
                    bin(id(6, 3, 0), &[(0, &original[..start])], Some(start as u64)),
                    bin(id(2, 3, 0), &[(0, &original[start..start + 14])], Some(14)),
                    bin(id(0, 3, 7), &[(0, &[0, 0, 0])], None),
                ],
                stored_bytes: u64::MAX,
                accepted_fragments: u64::MAX,
            };
            let before = frame(&cache);
            let result = cache.transcode_precinct_codestream(&plan, requested);
            if requested == 0 || requested > 3 {
                assert_eq!(
                    observed(&result),
                    Err(malformed(
                        usize::from(requested),
                        MalformedKind::InvalidJpipLayout
                    ))
                );
            } else if limit < u64::from(requested) {
                assert_eq!(
                    observed(&result),
                    Err(DecodeError::limit(Resource::InputBytes, limit, limit + 1))
                );
            } else if limit < start as u64 {
                assert_eq!(
                    observed(&result),
                    Err(DecodeError::limit(
                        Resource::InputBytes,
                        limit,
                        start as u64
                    ))
                );
            } else {
                let expected = decodable_codestream_with_layers(requested);
                if limit < expected.len() as u64 {
                    assert_eq!(
                        observed(&result),
                        Err(DecodeError::limit(
                            Resource::InputBytes,
                            limit,
                            expected.len() as u64
                        ))
                    );
                } else {
                    assert_eq!(result.unwrap().codestream().unwrap().as_bytes(), expected);
                }
            }
            assert_eq!(frame(&cache), before);
        }
    }
    for (main, tile, error) in [
        (
            vec![0, 0],
            original[start..start + 14].to_vec(),
            malformed(0, MalformedKind::MissingRequiredStructure),
        ),
        (
            original[..start].to_vec(),
            vec![],
            malformed(0, MalformedKind::InvalidJpipLayout),
        ),
        (
            [original[..start].to_vec(), vec![0xff, 0x93]].concat(),
            original[start..start + 14].to_vec(),
            malformed(start, MalformedKind::InvalidMarkerOrder),
        ),
    ] {
        let cache = DatabinCache {
            limits: ResourceLimits::HARDENED,
            databins: vec![
                bin(plan.main_header, &[(0, &main)], Some(main.len() as u64)),
                bin(plan.tile_header, &[(0, &tile)], Some(tile.len() as u64)),
                bin(id(0, 3, 7), &[(0, &[0, 0, 0])], None),
            ],
            stored_bytes: 0,
            accepted_fragments: 0,
        };
        assert_eq!(
            observed(&cache.transcode_precinct_codestream(&plan, 1)),
            Err(error)
        );
    }
    assert_eq!(
        validate_precinct_codestream(&original, 2, &ResourceLimits::HARDENED),
        Err(malformed(0, MalformedKind::InvalidJpipLayout))
    );
    assert_eq!(
        validate_precinct_codestream(&original, 3, &ResourceLimits::HARDENED),
        Ok(())
    );
    for cut in 0..original.len() {
        let Err(expected) =
            crate::codestream::parse_layout(&original[..cut], &ResourceLimits::HARDENED)
        else {
            panic!("an incomplete emitted codestream must fail its raw parser");
        };
        assert_eq!(
            validate_precinct_codestream(&original[..cut], 3, &ResourceLimits::HARDENED),
            Err(expected)
        );
    }
    let mut reordered_main = original[..start].to_vec();
    let cod = reordered_main
        .windows(2)
        .position(|bytes| bytes == [0xff, 0x52])
        .unwrap();
    reordered_main[cod + 5] = 1;
    let cache = DatabinCache {
        limits: ResourceLimits::HARDENED,
        databins: vec![
            bin(
                plan.main_header,
                &[(0, &reordered_main)],
                Some(start as u64),
            ),
            bin(
                plan.tile_header,
                &[(0, &original[start..start + 14])],
                Some(14),
            ),
            bin(id(0, 3, 7), &[(0, &[0, 0, 0])], None),
        ],
        stored_bytes: 0,
        accepted_fragments: 0,
    };
    assert_eq!(
        observed(&cache.transcode_precinct_codestream(&plan, 1)),
        Err(malformed(0, MalformedKind::InvalidJpipLayout))
    );
}
