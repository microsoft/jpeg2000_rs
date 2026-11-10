use super::super::cache_layout_result_tests::{bin, frame, id, storage};
use super::super::range_result_tests::expected_availability;
use super::transcode_result_tests::expected_append;
use super::*;

fn expected(
    cache: &DatabinCache,
    plan: &JpipPrecinctCodestreamPlan,
) -> Result<(u16, Vec<JpipMissingRange>), DecodeError> {
    let overflow = || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow);
    let mut headers = JpipAvailabilityReport {
        status: JpipAvailability::Available,
        required_bytes: 0,
        available_bytes: 0,
        missing: Vec::new(),
    };
    expected_append(cache, plan.main_header, &mut headers)?;
    expected_append(cache, plan.tile_header, &mut headers)?;
    if !headers.missing.is_empty() {
        return Ok((0, headers.missing));
    }
    let mut start = 0;
    for (layer, &end) in plan.layer_ends.iter().enumerate() {
        if start > end || end > plan.packets.len() {
            return Err(overflow());
        }
        let ranges: Vec<_> = plan.packets[start..end]
            .iter()
            .map(|packet| packet.range)
            .collect();
        let report = expected_availability(cache, &ranges)?;
        if report.status != JpipAvailability::Available {
            return Ok((
                u16::try_from(layer).map_err(|_| overflow())?,
                report.missing,
            ));
        }
        start = end;
    }
    Ok((
        u16::try_from(plan.layer_ends.len()).map_err(|_| overflow())?,
        Vec::new(),
    ))
}

#[test]
fn actual_jpip_progressive_availability_derives_physical_headers_layers_missing_and_narrowing_errors()
 {
    let main = id(6, 3, 0);
    let tile = id(2, 3, 0);
    let precinct = id(0, 3, 7);
    let packet_states = [
        vec![],
        vec![bin(precinct, &[(0, b"a")], None)],
        vec![bin(precinct, &[(0, b"ab")], None)],
        vec![bin(precinct, &[(1, b"x"), (0, b"abc")], None)],
        vec![
            bin(id(1, 3, 7), &[(0, b"a")], Some(1)),
            bin(precinct, &[(0, b"abc")], Some(3)),
        ],
    ];
    let ends = [
        vec![],
        vec![0],
        vec![1],
        vec![2],
        vec![3],
        vec![4],
        vec![usize::MAX],
        vec![1, 2, 3],
        vec![2, 1],
        vec![0, 0, 0],
        vec![0, 1, 3],
        vec![1, 3, 2],
    ];
    let mut cases = 0;
    for headers in [
        vec![],
        vec![bin(main, &[], Some(0)), bin(tile, &[], Some(0))],
        vec![bin(main, &[(0, b"M")], None), bin(tile, &[], Some(0))],
        vec![
            bin(main, &[(0, b"M")], Some(1)),
            bin(tile, &[(0, b"T")], Some(1)),
        ],
    ] {
        for state in &packet_states {
            for input in [1, 2, 4, 1 << 31] {
                for work in [1, 2, 8] {
                    let mut bins = headers.clone();
                    bins.extend(state.iter().cloned());
                    let cache = DatabinCache {
                        limits: crate::ResourceLimits::HARDENED
                            .with_maximum_input_bytes(input)
                            .unwrap()
                            .with_maximum_work_units(work)
                            .unwrap(),
                        databins: bins,
                        stored_bytes: u64::MAX,
                        accepted_fragments: u64::MAX,
                    };
                    let before = frame(&cache);
                    for ends in &ends {
                        let plan = JpipPrecinctCodestreamPlan {
                            main_header: main,
                            tile_header: tile,
                            packets: (0..3)
                                .map(|offset| JpipPrecinctPacket {
                                    range: JpipDatabinRange {
                                        databin: precinct,
                                        offset,
                                        length: 1,
                                    },
                                    layer: u16::MAX,
                                })
                                .collect(),
                            layer_ends: ends.clone(),
                        };
                        let owners = (storage(&plan.packets), storage(&plan.layer_ends));
                        assert_eq!(
                            cache.progressive_availability(&plan),
                            expected(&cache, &plan)
                        );
                        assert_eq!(frame(&cache), before);
                        assert_eq!((storage(&plan.packets), storage(&plan.layer_ends)), owners);
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 2880);
    let cache = DatabinCache {
        limits: crate::ResourceLimits::HARDENED,
        databins: vec![bin(main, &[], Some(0)), bin(tile, &[], Some(0))],
        stored_bytes: 0,
        accepted_fragments: 0,
    };
    for length in [65535, 65536, 65537] {
        let plan = JpipPrecinctCodestreamPlan {
            main_header: main,
            tile_header: tile,
            packets: Vec::new(),
            layer_ends: vec![0; length],
        };
        assert_eq!(
            cache.progressive_availability(&plan),
            expected(&cache, &plan)
        );
    }
}
