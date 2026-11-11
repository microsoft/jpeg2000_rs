use super::*;

#[test]
fn sarah_reserved_classes_have_no_registered_header_semantics() {
    let assigned = [
        Some(DatabinClass::Precinct),
        Some(DatabinClass::Precinct),
        Some(DatabinClass::TileHeader),
        None,
        Some(DatabinClass::TileData),
        Some(DatabinClass::TileData),
        Some(DatabinClass::MainHeader),
        None,
        Some(DatabinClass::Metadata),
    ];
    let mut failures = Vec::new();
    for identifier in (0..=256).chain([u64::MAX - 1, u64::MAX]) {
        assert_eq!(DatabinClass::has_auxiliary(identifier), identifier % 2 == 1);
        let expected = usize::try_from(identifier)
            .ok()
            .and_then(|index| assigned.get(index))
            .copied()
            .flatten();
        if DatabinClass::from_identifier(identifier) != expected {
            failures.push(identifier);
        }
        for stream in [0, 37, u64::MAX] {
            for bin in [0, 1, 128, u64::MAX] {
                match (expected, DatabinId::new(identifier, stream, bin)) {
                    (Some(class), Ok(value)) => {
                        assert_eq!(value.class(), class);
                        assert_eq!(value.class_identifier(), identifier);
                        assert_eq!((value.codestream(), value.in_class()), (stream, bin));
                    }
                    (None, Err(error)) => assert_eq!(
                        error,
                        DecodeError::MalformedInput {
                            offset: 0,
                            kind: MalformedKind::InvalidJpipHeader,
                        }
                    ),
                    (None, Ok(_)) => failures.push(identifier),
                    other => panic!("identifier={identifier}: {other:?}"),
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "Unassigned semantic header classes: {failures:?}"
    );
}

#[test]
fn semantic_identity_aliases_only_assigned_auxiliary_classes() {
    let classes = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 17, u64::MAX];
    let canonical = [0, 0, 2, 3, 4, 4, 6, 7, 8, 9, 17, u64::MAX];
    for (a, first) in classes.into_iter().enumerate() {
        for (b, second) in classes.into_iter().enumerate() {
            let raw = |class_identifier| DatabinId {
                class_identifier,
                class: DatabinClass::Metadata,
                codestream: 37,
                in_class: 129,
            };
            assert_eq!(
                raw(first).same_as(raw(second)),
                canonical[a] == canonical[b],
                "raw identity {first}/{second} must not acquire undeclared standard semantics"
            );
        }
    }
}

fn vbas(mut value: u64) -> Vec<u8> {
    let mut groups = vec![u8::try_from(value & 0x7f).unwrap()];
    value >>= 7;
    while value != 0 {
        groups.push(u8::try_from(value & 0x7f).unwrap() | 0x80);
        value >>= 7;
    }
    groups.reverse();
    groups
}

fn data(
    form: u8,
    identity: (u64, u64, u64),
    offset: u64,
    body: &[u8],
    last: bool,
    auxiliary: u64,
) -> Vec<u8> {
    let (class, stream, bin) = identity;
    let mut bytes = vbas(bin);
    if bytes[0] & 0x7f > 0x0f {
        bytes.insert(0, 0x80);
    }
    bytes[0] |= form << 5;
    if last {
        bytes[0] |= 0x10;
    }
    if form >= 2 {
        bytes.extend(vbas(class));
    }
    if form == 3 {
        bytes.extend(vbas(stream));
    }
    bytes.extend(vbas(offset));
    bytes.extend(vbas(body.len() as u64));
    if class % 2 == 1 {
        bytes.extend(vbas(auxiliary));
    }
    bytes.extend_from_slice(body);
    bytes
}

fn eor(reason: u8, body: &[u8]) -> Vec<u8> {
    let mut bytes = vec![0, reason];
    bytes.extend(vbas(body.len() as u64));
    bytes.extend_from_slice(body);
    bytes
}

fn reference_vbas(
    input: &[u8],
    start: usize,
    mask: Option<u8>,
) -> (Result<u64, DecodeError>, usize) {
    let invalid = DecodeError::malformed(start as u64, MalformedKind::InvalidJpipVbas);
    let Some(first) = input.get(start) else {
        return (
            Err(DecodeError::malformed(
                start as u64,
                MalformedKind::Truncated,
            )),
            start,
        );
    };
    let mut position = start + 1;
    let mut value = u128::from(first & mask.unwrap_or(0x7f));
    let mut more = first & 0x80 != 0;
    for count in 1..=10 {
        if !more {
            return (Ok(u64::try_from(value).unwrap()), position);
        }
        if count == 10 {
            return (Err(invalid), position);
        }
        let Some(byte) = input.get(position) else {
            return (
                Err(DecodeError::malformed(
                    position as u64,
                    MalformedKind::Truncated,
                )),
                position,
            );
        };
        let next = value * 128 + u128::from(byte & 0x7f);
        if next > u128::from(u64::MAX) {
            return (Err(invalid), position);
        }
        value = next;
        more = byte & 0x80 != 0;
        position += 1;
    }
    unreachable!()
}

#[test]
fn sarah_dev_9a1abe441f_bounded_vbas_padding_preserves_values_and_delimiters() {
    let mut values: Vec<u64> = (0..256).collect();
    for bit in 1..64 {
        let boundary = 1_u64 << bit;
        values.extend([boundary - 1, boundary, boundary + 1]);
    }
    values.extend([u64::MAX - 1, u64::MAX]);
    let mut seed = 0x6a09_e667_f3bc_c909_u64;
    for _ in 0..256 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        values.push(seed);
    }
    assert_eq!(values.len(), 703);
    let mut cases = 0;
    for value in values {
        for mask in [None, Some(0x0f)] {
            let mut field = vbas(value);
            if mask.is_some() && field[0] & 0x7f > 0x0f {
                field.insert(0, 0x80);
            }
            for padding in 0..=10 - field.len() {
                for flags in if mask.is_some() {
                    &[0x20_u8, 0x30, 0x40, 0x50, 0x60, 0x70][..]
                } else {
                    &[0_u8][..]
                } {
                    for prefix in [0, 3] {
                        let mut input = vec![0x55; prefix];
                        input.extend(std::iter::repeat_n(0x80, padding));
                        input.extend_from_slice(&field);
                        input[prefix] |= flags;
                        let end = input.len();
                        input.extend_from_slice(&[0x81, 0x02, 0x5a]);
                        let snapshot = input.clone();
                        let mut position = prefix;
                        assert_eq!(
                            (read_vbas(&input, &mut position, mask), position),
                            (Ok(value), end),
                            "value={value} mask={mask:?} padding={padding} flags={flags}"
                        );
                        assert_eq!(read_vbas(&input, &mut position, None), Ok(130));
                        assert_eq!(position, end + 2);
                        assert_eq!(input[position], 0x5a);
                        assert_eq!(input, snapshot);
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 51_458);
}

#[test]
fn sarah_dev_9a1abe441f_padded_message_fields_preserve_context_and_body() {
    let limits = ResourceLimits::HARDENED;
    for selected in 0..5 {
        for padding in 0..10 {
            let mut input = vec![0x70];
            for (field, value) in [1_u8, 3, 2, 1, 5].into_iter().enumerate() {
                if field == selected {
                    input.extend(std::iter::repeat_n(0x80, padding));
                }
                input.push(value);
            }
            let header_length = input.len();
            input.extend_from_slice(&[0xab, 0x5a]);
            let snapshot = input.clone();
            let mut context = JpipHeaderContext::new();
            let (message, consumed) = parse_jpip_message(&input, &mut context, &limits).unwrap();
            let JpipMessage::Data { header, body } = message else {
                panic!("expected data");
            };
            assert_eq!(header.databin(), DatabinId::new(1, 3, 0).unwrap());
            assert_eq!(
                (header.offset(), header.length(), header.auxiliary()),
                (2, 1, Some(5))
            );
            assert!(header.is_last_byte());
            assert_eq!(header.header_length(), header_length);
            assert_eq!(body, &[0xab]);
            assert_eq!(body.as_ptr(), input[header_length..].as_ptr());
            assert_eq!(consumed, header_length + 1);
            assert_eq!(context.previous_class(), Some(1));
            assert_eq!(context.previous_codestream(), Some(3));
            assert_eq!(input[consumed], 0x5a);
            assert_eq!(input, snapshot);

            let mut eor = vec![0, 2];
            eor.extend(std::iter::repeat_n(0x80, padding));
            eor.extend_from_slice(&[1, 0xab, 0x5a]);
            let before = context;
            let (message, consumed) = parse_jpip_message(&eor, &mut context, &limits).unwrap();
            let JpipMessage::EndOfResponse(message) = message else {
                panic!("expected end of response");
            };
            assert_eq!(message.reason_code(), 2);
            assert_eq!(message.body(), &[0xab]);
            assert_eq!(message.header_length(), 3 + padding);
            assert_eq!(consumed, 4 + padding);
            assert_eq!(context, before);
            assert_eq!(eor[consumed], 0x5a);
        }
    }
}

#[test]
fn actual_raw_jpip_vbas_matches_independent_values_and_partial_cursor_on_every_error() {
    let masks = [None, Some(0), Some(0x0f), Some(0x7f), Some(0xff)];
    let tails = [
        vec![],
        vec![0],
        vec![1],
        vec![0x7f],
        vec![0x80],
        vec![0xff],
        vec![0xff; 9],
        vec![0x80; 10],
        vec![0xff; 10],
    ];
    let mut cases = 0;
    for first in 0..=u8::MAX {
        for tail in &tails {
            let mut bytes = vec![0x55, first];
            bytes.extend_from_slice(tail);
            for mask in masks {
                let expected = reference_vbas(&bytes, 1, mask);
                let mut position = 1;
                let result = read_vbas(&bytes, &mut position, mask);
                assert_eq!(
                    (result, position),
                    expected,
                    "first={first}, tail={tail:?}, mask={mask:?}"
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 11_520);
    for value in [
        0,
        1,
        15,
        127,
        128,
        16_383,
        16_384,
        u32::MAX as u64,
        u64::MAX,
    ] {
        let bytes = vbas(value);
        let mut position = 0;
        assert_eq!(read_vbas(&bytes, &mut position, None), Ok(value));
        assert_eq!(position, bytes.len());
    }
    let mut position = usize::MAX;
    assert_eq!(
        read_vbas(&[], &mut position, None),
        Err(DecodeError::malformed(u64::MAX, MalformedKind::Truncated))
    );
    assert_eq!(position, usize::MAX);
}

#[test]
fn actual_raw_jpip_data_derives_all_header_fields_body_borrow_and_consumed_extent() {
    let limits = ResourceLimits::HARDENED;
    let mut cases = 0;
    for form in 1..=3 {
        for class in 0..=8 {
            for stream in [0, 1, 128] {
                for bin in [0, 15, 16, 127, 128, u32::MAX as u64, u64::MAX] {
                    for last in [false, true] {
                        let body = [0xff, 0x80, 1, 2];
                        let bytes = data(form, (class, stream, bin), 3, &body, last, 129);
                        let mut context = JpipHeaderContext {
                            previous_class: Some(class),
                            previous_codestream: Some(stream),
                        };
                        let (message, consumed) =
                            parse_jpip_message(&bytes, &mut context, &limits).unwrap();
                        let JpipMessage::Data {
                            header,
                            body: parsed,
                        } = message
                        else {
                            panic!("expected data");
                        };
                        let id = header.databin();
                        assert_eq!(
                            (id.class_identifier(), id.codestream(), id.in_class()),
                            (class, stream, bin)
                        );
                        let expected_class = match class {
                            0 | 1 => DatabinClass::Precinct,
                            2 => DatabinClass::TileHeader,
                            4 | 5 => DatabinClass::TileData,
                            6 => DatabinClass::MainHeader,
                            8 => DatabinClass::Metadata,
                            _ => DatabinClass::Unassigned,
                        };
                        assert_eq!(id.class(), expected_class);
                        assert_eq!(
                            (header.offset(), header.length(), header.is_last_byte()),
                            (3, 4, last)
                        );
                        assert_eq!(header.final_length(), if last { Some(7) } else { None });
                        assert_eq!(
                            header.auxiliary(),
                            if class % 2 == 1 { Some(129) } else { None }
                        );
                        assert_eq!(consumed, bytes.len());
                        assert_eq!(header.header_length(), bytes.len() - body.len());
                        assert_eq!(parsed, body);
                        assert!(std::ptr::eq(
                            parsed.as_ptr(),
                            bytes[header.header_length()..].as_ptr()
                        ));
                        assert!(std::ptr::eq(message.body().as_ptr(), parsed.as_ptr()));
                        assert_eq!(
                            (context.previous_class(), context.previous_codestream()),
                            (Some(class), Some(stream))
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 1_134);
}

#[test]
fn sarah_initial_history_defaults_preserve_absence_and_effective_identifiers() {
    let limits = ResourceLimits::HARDENED;
    let fresh = JpipHeaderContext::new();
    assert_eq!(fresh, JpipHeaderContext::default());
    assert_eq!(
        (fresh.previous_class(), fresh.previous_codestream()),
        (None, None)
    );
    let mut cases = 0;
    for previous_class in [None, Some(0), Some(1), Some(8)] {
        for previous_codestream in [None, Some(0), Some(129), Some(u64::MAX)] {
            for form in 1..=3 {
                for explicit_class in 0..=8 {
                    let class = if form == 1 {
                        previous_class.unwrap_or(0)
                    } else {
                        explicit_class
                    };
                    let stream = if form == 3 {
                        257
                    } else {
                        previous_codestream.unwrap_or(0)
                    };
                    for bin in [0, 1, 15, 16, 127, 128, 255, 16383] {
                        for offset in [0, 1, 127, 128] {
                            for length in [0, 1, 2, 127, 128] {
                                for last in [false, true] {
                                    let body = vec![0x5a; length];
                                    let mut bytes =
                                        data(form, (class, stream, bin), offset, &body, last, 129);
                                    let extent = bytes.len();
                                    bytes.push(0x55);
                                    let mut context = JpipHeaderContext {
                                        previous_class,
                                        previous_codestream,
                                    };
                                    let (message, consumed) =
                                        parse_jpip_message(&bytes, &mut context, &limits).unwrap();
                                    let JpipMessage::Data {
                                        header,
                                        body: actual,
                                    } = message
                                    else {
                                        panic!("expected data");
                                    };
                                    assert_eq!(
                                        (
                                            header.databin().class_identifier(),
                                            header.databin().codestream(),
                                            header.databin().in_class(),
                                        ),
                                        (class, stream, bin)
                                    );
                                    assert_eq!(
                                        (header.offset(), header.length()),
                                        (offset, length as u64)
                                    );
                                    assert_eq!(header.is_last_byte(), last);
                                    assert_eq!(
                                        header.auxiliary(),
                                        if class % 2 == 1 { Some(129) } else { None }
                                    );
                                    assert_eq!(consumed, extent);
                                    assert_eq!(header.header_length(), extent - length);
                                    assert_eq!(actual, body);
                                    assert!(std::ptr::eq(
                                        actual.as_ptr(),
                                        bytes[header.header_length()..extent].as_ptr()
                                    ));
                                    assert_eq!(
                                        (context.previous_class(), context.previous_codestream()),
                                        (Some(class), Some(stream))
                                    );
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 138_240);
}

#[test]
fn sarah_initial_history_defaults_commit_only_after_complete_data() {
    let limits = ResourceLimits::HARDENED;
    for original in [
        JpipHeaderContext::new(),
        JpipHeaderContext {
            previous_class: Some(8),
            previous_codestream: None,
        },
        JpipHeaderContext {
            previous_class: None,
            previous_codestream: Some(129),
        },
    ] {
        let class = original.previous_class().unwrap_or(0);
        let stream = original.previous_codestream().unwrap_or(0);
        let bytes = data(1, (class, stream, 16), 0, &[1, 2], true, 0);
        for end in 0..bytes.len() {
            let mut context = original;
            assert!(parse_jpip_message(&bytes[..end], &mut context, &limits).is_err());
            assert_eq!(context, original);
        }
        let mut context = original;
        let end = eor(1, &[]);
        assert!(parse_jpip_message(&end, &mut context, &limits).is_ok());
        assert_eq!(context, original);
        let (message, extent) = parse_jpip_message(&bytes, &mut context, &limits).unwrap();
        assert_eq!((extent, message.body()), (bytes.len(), &[1, 2][..]));
        assert_eq!(
            (context.previous_class(), context.previous_codestream()),
            (Some(class), Some(stream))
        );
        let committed = context;
        let limited = limits.with_maximum_input_bytes(1).unwrap();
        assert!(matches!(
            parse_jpip_message(&bytes, &mut context, &limited),
            Err(DecodeError::LimitExceeded {
                resource: Resource::InputBytes,
                ..
            })
        ));
        assert_eq!(context, committed);
    }
}

#[test]
fn sarah_initial_history_defaults_are_response_local_not_cache_history() {
    let limits = ResourceLimits::HARDENED;
    let mut cache = DatabinCache::new(limits);
    let explicit = data(3, (8, 129, 2), 0, &[7], true, 0);
    assert_eq!(
        ingest_jpip_response(&explicit, &mut cache)
            .unwrap()
            .messages(),
        1
    );
    for bin in [0, 1, 16, 129] {
        let mut bytes = data(1, (0, 0, bin), 0, &[1, 2], true, 0);
        bytes.extend(eor(1, &[]));
        let summary = ingest_jpip_response(&bytes, &mut cache).unwrap();
        assert_eq!(
            (summary.messages(), summary.end_of_response_reason()),
            (1, Some(1))
        );
        assert_eq!(
            cache
                .databin_view(DatabinId::new(0, 0, bin).unwrap())
                .unwrap()
                .as_bytes(),
            &[1, 2]
        );
    }
    assert_eq!(
        cache
            .databin_view(DatabinId::new(8, 129, 2).unwrap())
            .unwrap()
            .as_bytes(),
        &[7]
    );
    let mut parser = JpipMessageParser::new(limits);
    parser.parse(&explicit).unwrap();
    let inherited = data(1, (8, 129, 3), 0, &[9], true, 0);
    let (message, _) = parser.parse(&inherited).unwrap();
    let JpipMessage::Data { header, .. } = message else {
        panic!("expected data");
    };
    assert_eq!(
        (
            header.databin().class_identifier(),
            header.databin().codestream()
        ),
        (8, 129)
    );
}

#[test]
fn actual_raw_jpip_inherited_context_commits_only_complete_data_messages() {
    let limits = ResourceLimits::HARDENED;
    let mut parser = JpipMessageParser::new(limits);
    assert_eq!(parser.context(), JpipHeaderContext::new());
    let explicit = data(3, (7, 129, 16), 0, &[1], true, 3);
    let (first, first_consumed) = parser.parse(&explicit).unwrap();
    assert_eq!(first_consumed, explicit.len());
    assert_eq!(first.body(), &[1]);
    assert_eq!(
        (
            parser.context().previous_class(),
            parser.context().previous_codestream()
        ),
        (Some(7), Some(129))
    );
    let inherited = data(1, (7, 129, 2), 1, &[2, 3], false, 5);
    let (second, _) = parser.parse(&inherited).unwrap();
    let JpipMessage::Data { header, .. } = second else {
        panic!("expected data");
    };
    assert_eq!(
        (
            header.databin().class_identifier(),
            header.databin().codestream()
        ),
        (7, 129)
    );
    assert_eq!(header.auxiliary(), Some(5));
    let context = parser.context();
    for end in 0..inherited.len() {
        assert!(parser.parse(&inherited[..end]).is_err());
        assert_eq!(parser.context(), context);
    }
    let class_only = data(2, (4, 0, 3), 0, &[], false, 0);
    let mut fresh = JpipHeaderContext::new();
    let (message, _) = parse_jpip_message(&class_only, &mut fresh, &limits).unwrap();
    let JpipMessage::Data { header, .. } = message else {
        panic!("expected data");
    };
    assert_eq!(
        (
            header.databin().class_identifier(),
            header.databin().codestream()
        ),
        (4, 0)
    );
    let old = JpipHeaderContext {
        previous_class: Some(8),
        previous_codestream: None,
    };
    let mut context = old;
    let bytes = data(1, (8, 0, 0), 0, &[], false, 0);
    let (message, consumed) = parse_jpip_message(&bytes, &mut context, &limits).unwrap();
    assert_eq!((consumed, message.body()), (bytes.len(), &[][..]));
    assert_eq!(
        (context.previous_class(), context.previous_codestream()),
        (Some(8), Some(0))
    );
}

#[test]
fn actual_raw_jpip_eor_and_prefix_bodies_preserve_context_and_original_borrowed_slices() {
    let limits = ResourceLimits::HARDENED;
    for reason in [0, 1, 7, u8::MAX] {
        for body in [vec![], vec![0], vec![0xff, 0, 0x80], vec![4; 129]] {
            let mut bytes = eor(reason, &body);
            let consumed = bytes.len();
            bytes.extend_from_slice(&[0x55, 0x66]);
            let old = JpipHeaderContext {
                previous_class: Some(7),
                previous_codestream: Some(44),
            };
            let mut context = old;
            let (message, extent) = parse_jpip_message(&bytes, &mut context, &limits).unwrap();
            let JpipMessage::EndOfResponse(end) = message else {
                panic!("expected EOR");
            };
            assert_eq!((end.reason_code(), extent), (reason, consumed));
            assert_eq!(end.body(), body);
            assert_eq!(end.header_length(), consumed - body.len());
            assert!(std::ptr::eq(
                end.body().as_ptr(),
                bytes[end.header_length()..consumed].as_ptr()
            ));
            assert!(std::ptr::eq(message.body().as_ptr(), end.body().as_ptr()));
            assert_eq!(context, old);
        }
    }
    let mut bytes = data(3, (0, 0, 0), 0, &[1, 2], false, 0);
    let consumed = bytes.len();
    bytes.extend_from_slice(&[0x55, 0x66]);
    let mut context = JpipHeaderContext::new();
    let (message, extent) = parse_jpip_message(&bytes, &mut context, &limits).unwrap();
    assert_eq!(extent, consumed);
    assert_eq!(message.body(), &[1, 2]);
}

#[test]
fn actual_raw_jpip_rejects_overflow_extent_and_limit_frontiers_in_native_order() {
    let limits = ResourceLimits::HARDENED;
    let original = JpipHeaderContext {
        previous_class: Some(8),
        previous_codestream: Some(0),
    };
    for (bytes, expected) in [
        (vec![], DecodeError::malformed(0, MalformedKind::Truncated)),
        (vec![0], DecodeError::malformed(1, MalformedKind::Truncated)),
        (
            vec![0, 1],
            DecodeError::malformed(2, MalformedKind::Truncated),
        ),
        (
            vec![1],
            DecodeError::malformed(0, MalformedKind::InvalidJpipHeader),
        ),
        (
            vec![0x40, 9, 0, 0],
            DecodeError::malformed(0, MalformedKind::InvalidJpipHeader),
        ),
        (
            vec![0x40, 0x80, 0],
            DecodeError::malformed(3, MalformedKind::Truncated),
        ),
        (
            vec![0x40, 0, 0, 2, 1],
            DecodeError::malformed(4, MalformedKind::Truncated),
        ),
    ] {
        let mut context = original;
        assert_eq!(
            parse_jpip_message(&bytes, &mut context, &limits),
            Err(expected)
        );
        assert_eq!(context, original);
    }
    let empty_budget = limits.with_maximum_input_bytes(0).unwrap();
    let mut context = original;
    assert_eq!(
        parse_jpip_message(&[], &mut context, &empty_budget),
        Err(DecodeError::malformed(0, MalformedKind::Truncated))
    );
    assert_eq!(
        parse_jpip_message(&[1], &mut context, &empty_budget),
        Err(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: 0,
            actual: 1
        })
    );
    assert_eq!(context, original);
    let mut bytes = vec![0x40, 0];
    bytes.extend(vbas(u64::MAX));
    bytes.extend(vbas(1));
    let mut context = original;
    assert_eq!(
        parse_jpip_message(&bytes, &mut context, &limits),
        Err(DecodeError::malformed(
            bytes.len() as u64,
            MalformedKind::ArithmeticOverflow
        ))
    );
    assert_eq!(context, original);
    let bytes = data(2, (0, 0, 0), 12, &[1], false, 0);
    let limited = limits.with_maximum_input_bytes(12).unwrap();
    assert_eq!(
        parse_jpip_message(&bytes, &mut context, &limited),
        Err(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: 12,
            actual: 13
        })
    );
    assert_eq!(context, original);
}

#[test]
fn actual_raw_jpip_databin_and_header_getters_preserve_normalized_identity_and_saturating_final_length()
 {
    for class in 0..=8 {
        let id = DatabinId::from_wire(class, u64::MAX, 129).unwrap();
        assert_eq!(
            (id.class_identifier(), id.codestream(), id.in_class()),
            (class, u64::MAX, 129)
        );
        let pair = if matches!(class, 0 | 1 | 4 | 5) {
            class ^ 1
        } else {
            class
        };
        assert!(id.same_as(DatabinId::from_wire(pair, u64::MAX, 129).unwrap()));
        assert!(!id.same_as(DatabinId::from_wire(pair, 0, 129).unwrap()));
        assert!(!id.same_as(DatabinId::from_wire(pair, u64::MAX, 128).unwrap()));
        assert_eq!(DatabinClass::has_auxiliary(class), class % 2 == 1);
        for last in [false, true] {
            let header = JpipMessageHeader {
                databin: id,
                offset: u64::MAX,
                length: 1,
                last_byte: last,
                auxiliary: Some(u64::MAX),
                header_length: usize::MAX,
            };
            assert_eq!(header.databin(), id);
            assert_eq!(
                (header.offset(), header.length(), header.is_last_byte()),
                (u64::MAX, 1, last)
            );
            assert_eq!(
                header.final_length(),
                if last { Some(u64::MAX) } else { None }
            );
            assert_eq!(header.auxiliary(), Some(u64::MAX));
            assert_eq!(header.header_length(), usize::MAX);
        }
    }
    assert_eq!(
        DatabinId::new(9, 0, 0),
        Err(DecodeError::malformed(0, MalformedKind::InvalidJpipHeader))
    );
    assert_eq!(
        DatabinId::new(u64::MAX, 0, 0),
        Err(DecodeError::malformed(0, MalformedKind::InvalidJpipHeader))
    );
}
