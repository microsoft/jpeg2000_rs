use super::super::cache_layout_result_tests::{bin, class_key, frame, id};
use super::super::range_result_tests::expected_availability;
use super::*;

fn overflow() -> DecodeError {
    DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
}

pub(super) fn expected_append(
    cache: &DatabinCache,
    requested: DatabinId,
    output: &mut JpipAvailabilityReport,
) -> Result<(), DecodeError> {
    let selected = cache.databins.iter().find(|value| {
        class_key(value.id.class_identifier) == class_key(requested.class_identifier)
            && value.id.codestream == requested.codestream
            && value.id.in_class == requested.in_class
    });
    let Some(selected) = selected else {
        output.missing.push(JpipMissingRange {
            databin: requested,
            offset: 0,
            length: None,
        });
        return Ok(());
    };
    let mut prefix = 0_u128;
    for fragment in &selected.fragments {
        if u128::from(fragment.offset) == prefix {
            prefix = (prefix + fragment.bytes.len() as u128).min(u128::from(u64::MAX));
        }
    }
    let Some(length) = selected.final_length else {
        let next = u128::from(output.available_bytes) + prefix;
        if next > u128::from(u64::MAX) {
            return Err(overflow());
        }
        output.available_bytes = u64::try_from(next).unwrap();
        output.missing.push(JpipMissingRange {
            databin: requested,
            offset: u64::try_from(prefix).unwrap(),
            length: None,
        });
        return Ok(());
    };
    let header = if length == 0 {
        JpipAvailabilityReport {
            status: JpipAvailability::Available,
            required_bytes: 0,
            available_bytes: 0,
            missing: Vec::new(),
        }
    } else {
        expected_availability(
            cache,
            &[JpipDatabinRange {
                databin: requested,
                offset: 0,
                length,
            }],
        )?
    };
    let required = u128::from(output.required_bytes) + u128::from(header.required_bytes);
    if required > u128::from(u64::MAX) {
        return Err(overflow());
    }
    output.required_bytes = u64::try_from(required).unwrap();
    let available = u128::from(output.available_bytes) + u128::from(header.available_bytes);
    if available > u128::from(u64::MAX) {
        return Err(overflow());
    }
    output.available_bytes = u64::try_from(available).unwrap();
    output.missing.extend(header.missing);
    Ok(())
}

#[test]
fn actual_jpip_complete_header_requirements_preserve_partial_reports_and_physical_cache_priorities()
{
    let main = id(6, 3, 0);
    let tile = id(2, 3, 4);
    let precinct = id(0, 3, 7);
    let states = [
        vec![],
        vec![bin(main, &[], None)],
        vec![bin(main, &[], Some(0))],
        vec![bin(main, &[(0, b"ab")], None)],
        vec![bin(main, &[(0, b"ab")], Some(2))],
        vec![bin(main, &[(1, b"x"), (0, b"ab")], Some(4))],
        vec![bin(main, &[(0, b"ab"), (0, b"cd")], Some(2))],
        vec![
            bin(id(7, 3, 0), &[(0, b"a")], Some(1)),
            bin(main, &[(0, b"abcd")], Some(4)),
        ],
        vec![bin(main, &[(0, b"a")], Some(u64::MAX))],
    ];
    let mut cases = 0;
    for state in states {
        for input in [1, 2, 4, 1 << 31] {
            for work in [1, 2, 8] {
                let cache = DatabinCache {
                    limits: crate::ResourceLimits::HARDENED
                        .with_maximum_input_bytes(input)
                        .unwrap()
                        .with_maximum_work_units(work)
                        .unwrap(),
                    databins: state.clone(),
                    stored_bytes: u64::MAX,
                    accepted_fragments: u64::MAX,
                };
                let before = frame(&cache);
                for status in [
                    JpipAvailability::Available,
                    JpipAvailability::Missing,
                    JpipAvailability::Partial,
                ] {
                    for required_bytes in [0, 1, u64::MAX - 1, u64::MAX] {
                        for available_bytes in [0, 1, u64::MAX - 1, u64::MAX] {
                            let mut report = JpipAvailabilityReport {
                                status,
                                required_bytes,
                                available_bytes,
                                missing: vec![JpipMissingRange {
                                    databin: tile,
                                    offset: 99,
                                    length: None,
                                }],
                            };
                            let mut expected = report.clone();
                            let outcome = expected_append(&cache, main, &mut expected);
                            assert_eq!(
                                cache.append_complete_databin_requirement(main, &mut report),
                                outcome
                            );
                            assert_eq!(report, expected);
                            assert_eq!(frame(&cache), before);
                            cases += 1;
                        }
                    }
                }
                for end in [0, 1, 2] {
                    let plan = JpipPrecinctCodestreamPlan {
                        main_header: main,
                        tile_header: tile,
                        packets: vec![JpipPrecinctPacket {
                            range: JpipDatabinRange {
                                databin: precinct,
                                offset: 0,
                                length: 1,
                            },
                            layer: u16::MAX,
                        }],
                        layer_ends: vec![usize::MAX, 0],
                    };
                    let expected = if end > 1 {
                        Err(overflow())
                    } else {
                        let ranges = if end == 0 {
                            Vec::new()
                        } else {
                            vec![plan.packets[0].range]
                        };
                        expected_availability(&cache, &ranges).and_then(|mut report| {
                            expected_append(&cache, main, &mut report)?;
                            expected_append(&cache, tile, &mut report)?;
                            report.status = if report.missing.is_empty() {
                                JpipAvailability::Available
                            } else if report.available_bytes == 0 {
                                JpipAvailability::Missing
                            } else {
                                JpipAvailability::Partial
                            };
                            Ok(report)
                        })
                    };
                    assert_eq!(cache.precinct_availability(&plan, end), expected);
                    assert_eq!(frame(&cache), before);
                }
            }
        }
    }
    assert_eq!(cases, 5184);
}
