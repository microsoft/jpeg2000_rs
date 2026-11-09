use super::super::JpipAvailability;
use super::super::cache_layout_result_tests::{bin, frame, id, storage};
use super::super::range_result_tests::{expected_availability, expected_packets};
use super::*;

fn packet(layer: u16, stream: u64, offset: u64, length: u64) -> JpipPrecinctPacket {
    JpipPrecinctPacket {
        range: JpipDatabinRange {
            databin: id(0, stream, 7),
            offset,
            length,
        },
        layer,
    }
}

fn limits(packets: u64, input: u64) -> ResourceLimits {
    ResourceLimits::HARDENED
        .with_maximum_packets(packets)
        .unwrap()
        .with_maximum_input_bytes(input)
        .unwrap()
}

fn invalid(offset: u64) -> DecodeError {
    DecodeError::malformed(offset, MalformedKind::InvalidJpipLayout)
}

fn overflow() -> DecodeError {
    DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
}

type Observed<'a> = Result<(u16, &'a JpipAvailabilityReport, Option<&'a [u8]>), DecodeError>;

fn observed(value: &Result<JpipPrecinctPackets, DecodeError>) -> Observed<'_> {
    match value {
        Err(error) => Err(*error),
        Ok(value) => Ok((
            value.layers,
            &value.availability,
            value.packets.as_ref().map(|bytes| bytes.bytes.as_slice()),
        )),
    }
}

fn expected_plan(
    main: DatabinId,
    tile: DatabinId,
    packets: &[JpipPrecinctPacket],
    layers: u16,
    limits: &ResourceLimits,
) -> Result<Vec<usize>, DecodeError> {
    if layers == 0 || layers > limits.maximum_layers() {
        return Err(DecodeError::limit(
            Resource::Layers,
            u64::from(limits.maximum_layers()),
            u64::from(layers),
        ));
    }
    if main.class != DatabinClass::MainHeader
        || main.in_class != 0
        || tile.class != DatabinClass::TileHeader
        || main.codestream != tile.codestream
    {
        return Err(invalid(0));
    }
    if packets.is_empty() || packets.len() as u64 > limits.maximum_packets() {
        return Err(DecodeError::limit(
            Resource::Packets,
            limits.maximum_packets(),
            packets.len() as u64,
        ));
    }
    let mut ends = Vec::new();
    let mut next = 0;
    let mut total = 0_u128;
    for layer in 0..layers {
        let start = next;
        for value in &packets[start..] {
            if value.layer != layer {
                break;
            }
            if value.range.databin.codestream != main.codestream {
                return Err(invalid(value.range.offset));
            }
            total += u128::from(value.range.length);
            if total > u128::from(u64::MAX) {
                return Err(DecodeError::malformed(
                    value.range.offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
            if total > u128::from(limits.maximum_input_bytes()) {
                return Err(DecodeError::limit(
                    Resource::InputBytes,
                    limits.maximum_input_bytes(),
                    u64::try_from(total).unwrap(),
                ));
            }
            next += 1;
        }
        if next == start {
            return Err(invalid(u64::from(layer)));
        }
        ends.push(next);
    }
    if next != packets.len() {
        return Err(invalid(next as u64));
    }
    Ok(ends)
}

fn expected_reconstruction(
    cache: &DatabinCache,
    plan: &JpipPrecinctCodestreamPlan,
    layers: u16,
) -> Result<JpipPrecinctPackets, DecodeError> {
    let count = u16::try_from(plan.layer_ends.len() % 65536).unwrap();
    if layers == 0 || layers > count {
        return Err(invalid(u64::from(layers)));
    }
    let end = *plan
        .layer_ends
        .get(usize::from(layers - 1))
        .ok_or_else(overflow)?;
    let selected = plan.packets.get(..end).ok_or_else(overflow)?;
    let ranges: Vec<_> = selected.iter().map(|packet| packet.range).collect();
    let availability = expected_availability(cache, &ranges)?;
    let packets = if matches!(availability.status, JpipAvailability::Available) {
        Some(JpipByteView {
            bytes: expected_packets(cache, selected)?,
        })
    } else {
        None
    };
    Ok(JpipPrecinctPackets {
        layers,
        availability,
        packets,
    })
}

#[test]
fn actual_jpip_owned_packet_plans_preserve_full_fields_owner_and_first_admission_errors() {
    for class in [0, 1, 2, 6, 8] {
        for offset in [0, u64::MAX] {
            for length in [0, 1, 2] {
                let databin = id(class, 4, 7);
                let expected = if class > 1 {
                    Err(invalid(offset))
                } else if length == 0 {
                    Err(DecodeError::malformed(
                        offset,
                        MalformedKind::InvalidJpipFragment,
                    ))
                } else if u128::from(offset) + u128::from(length) > u128::from(u64::MAX) {
                    Err(DecodeError::malformed(
                        offset,
                        MalformedKind::ArithmeticOverflow,
                    ))
                } else {
                    Ok(JpipPrecinctPacket {
                        range: JpipDatabinRange {
                            databin,
                            offset,
                            length,
                        },
                        layer: u16::MAX,
                    })
                };
                let result = JpipPrecinctPacket::new(databin, u16::MAX, offset, length);
                assert_eq!(result, expected);
                if let Ok(value) = result {
                    assert_eq!(value.range(), value.range);
                    assert_eq!(value.layer(), u16::MAX);
                }
            }
        }
    }
    let values = [
        packet(0, 4, 0, 1),
        packet(1, 4, 1, 2),
        packet(0, 9, 9, u64::MAX),
        packet(2, 4, u64::MAX, u64::MAX),
    ];
    let headers = [
        (id(6, 4, 0), id(2, 4, 3)),
        (id(6, 4, 1), id(2, 4, 3)),
        (id(8, 4, 0), id(2, 4, 3)),
        (id(6, 4, 0), id(2, 5, 3)),
    ];
    let mut cases = 0;
    for code in 0..65 {
        let entries = if code == 64 {
            Vec::new()
        } else {
            vec![
                values[code % 4],
                values[code / 4 % 4],
                values[code / 16 % 4],
            ]
        };
        for packet_cap in [0, 1, 3] {
            for input in [0, 2, 8] {
                let limits = limits(packet_cap, input);
                for layers in [0, 1, 2, 3, 256, 257, u16::MAX] {
                    for (main, tile) in headers {
                        let owned = entries.clone();
                        let owner = storage(&owned);
                        let expected = expected_plan(main, tile, &entries, layers, &limits);
                        match (
                            expected,
                            JpipPrecinctCodestreamPlan::new(main, tile, owned, layers, &limits),
                        ) {
                            (Err(expected), Err(actual)) => assert_eq!(actual, expected),
                            (Ok(ends), Ok(plan)) => {
                                assert_eq!(plan.main_header(), main);
                                assert_eq!(plan.tile_header(), tile);
                                assert_eq!(plan.packets(), entries);
                                assert_eq!(plan.layer_ends, ends);
                                assert_eq!(plan.layers(), layers);
                                assert_eq!(storage(&plan.packets), owner);
                                assert_eq!(plan.packets().as_ptr(), plan.packets.as_ptr());
                                for requested in 0..=layers + 1 {
                                    let expected = if requested == 0 || requested > layers {
                                        Err(invalid(u64::from(requested)))
                                    } else {
                                        Ok(ends[usize::from(requested - 1)])
                                    };
                                    assert_eq!(plan.packet_end_for_layers(requested), expected);
                                }
                            }
                            (expected, actual) => {
                                panic!("plan mismatch: expected {expected:?}, actual {actual:?}")
                            }
                        }
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 16380);
}

#[test]
fn actual_jpip_planned_packet_results_derive_arbitrary_physical_selection_availability_and_bytes() {
    let fragments: [(u64, &[u8]); 4] = [(0, b"ab"), (2, b"cd"), (1, b"x"), (u64::MAX - 1, b"qr")];
    let plans: &[&[usize]] = &[
        &[],
        &[0],
        &[1],
        &[2],
        &[3],
        &[usize::MAX],
        &[1, 2],
        &[2, 1],
        &[0, 2],
    ];
    let entries = vec![packet(7, 4, 0, 2), packet(0, 4, 2, 2)];
    let mut cases = 0;
    for code in 0..65 {
        let parts = if code == 64 {
            Vec::new()
        } else {
            vec![
                fragments[code % 4],
                fragments[code / 4 % 4],
                fragments[code / 16 % 4],
            ]
        };
        for input in [0, 2, 4, 8] {
            for packet_cap in [0, 1, 4] {
                for work in [0, 2, 8] {
                    let cache = DatabinCache {
                        limits: limits(packet_cap, input)
                            .with_maximum_work_units(work)
                            .unwrap(),
                        databins: vec![
                            bin(id(0, 4, 7), &parts, Some(u64::MAX)),
                            bin(id(1, 4, 7), &[(0, b"later")], Some(5)),
                        ],
                        stored_bytes: u64::MAX,
                        accepted_fragments: u64::MAX,
                    };
                    let before = frame(&cache);
                    for ends in plans {
                        let plan = JpipPrecinctCodestreamPlan {
                            main_header: id(8, 9, 9),
                            tile_header: id(8, 9, 9),
                            packets: entries.clone(),
                            layer_ends: ends.to_vec(),
                        };
                        let packet_owner = storage(&plan.packets);
                        let end_owner = storage(&plan.layer_ends);
                        for layers in 0..4 {
                            let expected = expected_reconstruction(&cache, &plan, layers);
                            let actual = cache.reconstruct_precinct_packets(&plan, layers);
                            assert_eq!(
                                observed(&actual),
                                observed(&expected),
                                "physical case {code}, input {input}, cap {packet_cap}, work {work}, ends {ends:?}, layers {layers}"
                            );
                            if let Ok(value) = actual {
                                assert_eq!(value.layers(), layers);
                                assert!(std::ptr::eq(value.availability(), &value.availability));
                                assert_eq!(value.availability(), &value.availability);
                                let owner = value.packets().map(|bytes| storage(&bytes.bytes));
                                let expected_bytes =
                                    value.packets().map(|bytes| bytes.bytes.clone());
                                let moved = value.into_packets();
                                assert_eq!(
                                    moved.as_ref().map(|bytes| storage(&bytes.bytes)),
                                    owner
                                );
                                assert_eq!(moved.map(|bytes| bytes.bytes), expected_bytes);
                            }
                            assert_eq!(frame(&cache), before);
                            assert_eq!(storage(&plan.packets), packet_owner);
                            assert_eq!(storage(&plan.layer_ends), end_owner);
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 84240);
    for length in [65536, 65537] {
        let plan = JpipPrecinctCodestreamPlan {
            main_header: id(6, 4, 0),
            tile_header: id(2, 4, 0),
            packets: entries.clone(),
            layer_ends: vec![1; length],
        };
        assert_eq!(usize::from(plan.layers()), length % 65536);
        assert_eq!(
            plan.packet_end_for_layers(1),
            if length == 65536 {
                Err(invalid(1))
            } else {
                Ok(1)
            }
        );
    }
}

#[test]
fn actual_jpip_planned_packets_compose_raw_ingestion_and_preserve_missing_partial_and_owned_outputs()
 {
    let limits = limits(8, 128);
    let databin = id(0, 4, 7);
    let packet = JpipPrecinctPacket::new(databin, 0, 0, 2).unwrap();
    let plan = JpipPrecinctCodestreamPlan::new(id(6, 4, 0), id(2, 4, 3), vec![packet], 1, &limits)
        .unwrap();
    let mut cache = DatabinCache::new(limits);
    let missing = cache.reconstruct_precinct_packets(&plan, 1).unwrap();
    assert_eq!(missing.availability().status(), JpipAvailability::Missing);
    assert_eq!(missing.availability().required_bytes(), 2);
    assert_eq!(missing.availability().available_bytes(), 0);
    assert!(missing.packets().is_none());
    super::super::ingest_jpip_response(&[0x67, 0, 4, 0, 1, b'A'], &mut cache).unwrap();
    let partial = cache.reconstruct_precinct_packets(&plan, 1).unwrap();
    assert_eq!(partial.availability().status(), JpipAvailability::Partial);
    assert_eq!(partial.availability().available_bytes(), 1);
    assert!(partial.into_packets().is_none());
    super::super::ingest_jpip_response(&[0x77, 0, 4, 1, 1, b'B'], &mut cache).unwrap();
    let before = frame(&cache);
    let complete = cache.reconstruct_precinct_packets(&plan, 1).unwrap();
    assert!(complete.availability().is_available());
    let bytes = complete.packets().unwrap();
    assert_eq!(bytes.as_bytes(), b"AB");
    assert_ne!(
        bytes.as_bytes().as_ptr(),
        cache.databins[0].fragments[0].bytes.as_ptr()
    );
    let owner = storage(&bytes.bytes);
    let mut moved = complete.into_packets().unwrap().into_bytes();
    assert_eq!(storage(&moved), owner);
    moved[0] = 0;
    assert_eq!(frame(&cache), before);
    assert!(cache.status(id(6, 4, 0)).is_none());
    assert!(cache.status(id(2, 4, 3)).is_none());
}
