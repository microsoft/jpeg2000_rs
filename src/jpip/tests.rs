use super::*;

fn id(class: u64, in_class: u64) -> DatabinId {
    DatabinId::new(class, 0, in_class).unwrap()
}

fn fragment(databin: DatabinId, offset: u64, bytes: &[u8], final_byte: bool) -> JpipFragment {
    JpipFragment::new(
        databin,
        offset,
        bytes.to_vec(),
        final_byte,
        None,
        &ResourceLimits::default(),
    )
    .unwrap()
}

fn segment(marker: u16, payload: &[u8]) -> Vec<u8> {
    let mut bytes = marker.to_be_bytes().to_vec();
    bytes.extend_from_slice(&u16::try_from(payload.len() + 2).unwrap().to_be_bytes());
    bytes.extend_from_slice(payload);
    bytes
}

fn box32(box_type: [u8; 4], payload: &[u8]) -> Vec<u8> {
    let mut bytes = u32::try_from(payload.len() + 8)
        .unwrap()
        .to_be_bytes()
        .to_vec();
    bytes.extend_from_slice(&box_type);
    bytes.extend_from_slice(payload);
    bytes
}

fn metadata_placeholder(
    box_type: [u8; 4],
    original_length: u32,
    flags: u32,
    bin: u64,
    stream: Option<u64>,
) -> Vec<u8> {
    let mut payload = flags.to_be_bytes().to_vec();
    payload.extend_from_slice(&(bin >> 32).to_be_bytes()[4..]);
    payload.extend_from_slice(&(bin as u32).to_be_bytes());
    payload.extend_from_slice(&original_length.to_be_bytes());
    payload.extend_from_slice(&box_type);
    if let Some(stream) = stream {
        payload.extend_from_slice(&0_u64.to_be_bytes());
        payload.extend_from_slice(&original_length.to_be_bytes());
        payload.extend_from_slice(&box_type);
        payload.extend_from_slice(&stream.to_be_bytes());
    }
    box32(*b"phld", &payload)
}

#[test]
fn sarah_engineering_single_stream_optional_ncs_is_consumed_but_not_applied() {
    for flags in [4, 5, 6, 7] {
        let framed = metadata_placeholder(*b"jp2c", 8, flags, 17, Some(u64::MAX));
        let base = &framed[8..];
        assert_eq!(parse_jpip_placeholder(base).unwrap().stream_count, 1);
        for count in [0_u32, 1, 2, u32::MAX] {
            let mut payload = base.to_vec();
            payload.extend_from_slice(&count.to_be_bytes());
            let parsed = parse_jpip_placeholder(&payload).unwrap();
            assert_eq!(parsed.stream, Some(u64::MAX));
            assert_eq!(parsed.stream_count, 1);
            assert!(parse_jpip_placeholder(&payload[..payload.len() - 1]).is_err());
            payload.push(0);
            assert!(parse_jpip_placeholder(&payload).is_err());
        }
    }
}

#[test]
fn placeholder_parser_accepts_standard_bit_flags_and_types_extensions() {
    let original = [0, 0, 0, 8, b'j', b'p', b'2', b'c'];
    let equivalent = [0, 0, 0, 8, b'j', b'p', b'2', b'c'];
    let mut payload = 6_u32.to_be_bytes().to_vec();
    payload.extend_from_slice(&3_u64.to_be_bytes());
    payload.extend_from_slice(&original);
    payload.extend_from_slice(&4_u64.to_be_bytes());
    payload.extend_from_slice(&equivalent);
    payload.extend_from_slice(&9_u64.to_be_bytes());
    let placeholder = parse_jpip_placeholder(&payload).unwrap();
    assert_eq!(placeholder.flags, 6);
    assert_eq!(placeholder.equivalent_bin, Some(4));
    assert_eq!(placeholder.stream, Some(9));
    assert_eq!(placeholder.stream_count, 1);

    let mut range = 12_u32.to_be_bytes().to_vec();
    range.extend_from_slice(&0_u64.to_be_bytes());
    range.extend_from_slice(&original);
    range.extend_from_slice(&0_u64.to_be_bytes());
    range.extend_from_slice(&equivalent);
    range.extend_from_slice(&11_u64.to_be_bytes());
    range.extend_from_slice(&2_u32.to_be_bytes());
    assert_eq!(parse_jpip_placeholder(&range).unwrap().stream_count, 2);

    let mut extension = 0x10_u32.to_be_bytes().to_vec();
    extension.extend_from_slice(&0_u64.to_be_bytes());
    extension.extend_from_slice(&original);
    assert!(matches!(
        parse_jpip_placeholder(&extension),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidBoxContents,
            ..
        })
    ));
}

#[test]
fn placeholder_raw_results_preserve_every_field_and_first_error() {
    let original = [0, 0, 0, 1, b'a', b's', b'o', b'c', 0, 0, 0, 0, 0, 0, 0, 32];
    let equivalent = [0, 0, 0, 8, b'j', b'p', b'2', b'c'];
    let mut payload = 14_u32.to_be_bytes().to_vec();
    payload.extend_from_slice(&0x1122_3344_5566_7788_u64.to_be_bytes());
    payload.extend_from_slice(&original);
    payload.extend_from_slice(&0x9988_7766_5544_3322_u64.to_be_bytes());
    payload.extend_from_slice(&equivalent);
    payload.extend_from_slice(&0x0102_0304_0506_0708_u64.to_be_bytes());
    payload.extend_from_slice(&3_u32.to_be_bytes());
    let parsed = parse_jpip_placeholder(&payload).unwrap();
    assert_eq!(parsed.flags, 14);
    assert_eq!(parsed.bin, 0x1122_3344_5566_7788);
    assert_eq!(parsed.original_header, original);
    assert_eq!(parsed.original_type, crate::jp2::BoxType::ASSOCIATION);
    assert_eq!(parsed.equivalent_bin, Some(0x9988_7766_5544_3322));
    assert_eq!(
        parsed.equivalent_header.as_deref(),
        Some(equivalent.as_slice())
    );
    assert_eq!(
        parsed.equivalent_type,
        Some(crate::jp2::BoxType::CONTIGUOUS_CODESTREAM)
    );
    assert_eq!(parsed.stream, Some(0x0102_0304_0506_0708));
    assert_eq!(parsed.stream_count, 3);

    let reject = |bytes: &[u8]| match parse_jpip_placeholder(bytes) {
        Err(error) => error,
        Ok(_) => panic!("accepted malformed placeholder with {} bytes", bytes.len()),
    };
    for (length, offset, kind) in [
        (0, 0, MalformedKind::InvalidBoxContents),
        (19, 0, MalformedKind::InvalidBoxContents),
        (20, 0, MalformedKind::InvalidBoxContents),
        (28, 28, MalformedKind::Truncated),
        (32, 32, MalformedKind::Truncated),
        (36, 36, MalformedKind::Truncated),
        (40, 0, MalformedKind::InvalidBoxContents),
        (44, 44, MalformedKind::Truncated),
        (48, 48, MalformedKind::Truncated),
        (52, 52, MalformedKind::Truncated),
        (55, 52, MalformedKind::Truncated),
    ] {
        assert_eq!(
            reject(&payload[..length]),
            DecodeError::MalformedInput { offset, kind },
            "prefix {length}",
        );
    }
    let invalid = DecodeError::malformed(0, MalformedKind::InvalidBoxContents);
    let mut bad_flags = payload[..28].to_vec();
    bad_flags[..4].copy_from_slice(&0x10_u32.to_be_bytes());
    assert_eq!(reject(&bad_flags), invalid);
    let mut zero_count = payload.clone();
    zero_count[52..56].copy_from_slice(&0_u32.to_be_bytes());
    assert_eq!(reject(&zero_count), invalid);
    let mut trailer = payload.clone();
    trailer.push(0);
    assert_eq!(reject(&trailer), invalid);

    let mut ignored_count = payload.clone();
    ignored_count[..4].copy_from_slice(&6_u32.to_be_bytes());
    ignored_count[52..56].copy_from_slice(&0xdead_beef_u32.to_be_bytes());
    assert_eq!(
        parse_jpip_placeholder(&ignored_count).unwrap().stream_count,
        1
    );
    let mut original_only = payload[..28].to_vec();
    original_only[..4].copy_from_slice(&1_u32.to_be_bytes());
    let parsed = parse_jpip_placeholder(&original_only).unwrap();
    assert_eq!(parsed.original_header, original);
    assert_eq!(parsed.equivalent_bin, None);
    assert_eq!(parsed.equivalent_header, None);
    assert_eq!(parsed.equivalent_type, None);
    assert_eq!(parsed.stream, None);
    assert_eq!(parsed.stream_count, 0);
}

fn decodable_codestream() -> Vec<u8> {
    decodable_codestream_with_layers(1)
}

pub(super) fn decodable_codestream_with_layers(layers: u16) -> Vec<u8> {
    let mut siz = Vec::new();
    siz.extend_from_slice(&0_u16.to_be_bytes());
    siz.extend_from_slice(&1_u32.to_be_bytes());
    siz.extend_from_slice(&1_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&1_u32.to_be_bytes());
    siz.extend_from_slice(&1_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&1_u16.to_be_bytes());
    siz.extend_from_slice(&[7, 1, 1]);
    let mut bytes = SOC.to_vec();
    bytes.extend(segment(0xff51, &siz));
    let layer_bytes = layers.to_be_bytes();
    bytes.extend(segment(
        0xff52,
        &[0, 0, layer_bytes[0], layer_bytes[1], 0, 0, 0, 0, 0, 1],
    ));
    bytes.extend(segment(0xff5c, &[0, 0x40]));
    let tile_start = bytes.len();
    let mut sot = Vec::new();
    sot.extend_from_slice(&0_u16.to_be_bytes());
    sot.extend_from_slice(&(14_u32 + u32::from(layers)).to_be_bytes());
    sot.extend_from_slice(&[0, 1]);
    bytes.extend(segment(0xff90, &sot));
    bytes.extend_from_slice(&0xff93_u16.to_be_bytes());
    bytes.extend(vec![0; usize::from(layers)]);
    assert_eq!(bytes.len() - tile_start, 14 + usize::from(layers));
    bytes.extend_from_slice(&EOC);
    bytes
}

fn two_tile_codestream() -> Vec<u8> {
    let mut siz = Vec::new();
    siz.extend_from_slice(&0_u16.to_be_bytes());
    siz.extend_from_slice(&2_u32.to_be_bytes());
    siz.extend_from_slice(&1_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&1_u32.to_be_bytes());
    siz.extend_from_slice(&1_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&1_u16.to_be_bytes());
    siz.extend_from_slice(&[7, 1, 1]);
    let mut bytes = SOC.to_vec();
    bytes.extend(segment(0xff51, &siz));
    bytes.extend(segment(0xff52, &[0, 0, 0, 1, 0, 0, 0, 0, 0, 1]));
    bytes.extend(segment(0xff5c, &[0, 0x40]));
    let mut tile = 0_u16;
    while tile < 2 {
        let mut sot = Vec::new();
        sot.extend_from_slice(&tile.to_be_bytes());
        sot.extend_from_slice(&15_u32.to_be_bytes());
        sot.extend_from_slice(&[0, 1]);
        bytes.extend(segment(0xff90, &sot));
        bytes.extend_from_slice(&[0xff, 0x93, 0]);
        tile += 1;
    }
    bytes.extend_from_slice(&EOC);
    bytes
}

#[test]
fn parses_all_three_standard_header_forms_and_auxiliary() {
    let limits = ResourceLimits::default();
    let mut context = JpipHeaderContext::new();
    let explicit = [0x72, 0x01, 0x01, 0x00, 0x03, 0x07, 1, 2, 3];
    let (message, consumed) = parse_jpip_message(&explicit, &mut context, &limits).unwrap();
    assert_eq!(consumed, explicit.len());
    let JpipMessage::Data { header, body } = message else {
        panic!("data message expected");
    };
    assert_eq!(header.databin().class(), DatabinClass::Precinct);
    assert_eq!(header.databin().in_class(), 2);
    assert_eq!(header.auxiliary(), Some(7));
    assert!(header.is_last_byte());
    assert_eq!(body, [1, 2, 3]);

    let inherited = [0x31, 0x03, 0x01, 0, 9];
    let (message, _) = parse_jpip_message(&inherited, &mut context, &limits).unwrap();
    let JpipMessage::Data { header, .. } = message else {
        panic!("data message expected");
    };
    assert_eq!(header.databin().class_identifier(), 1);
    assert_eq!(header.databin().codestream(), 1);

    let class_only = [0x50, 0x08, 0x00, 0x00];
    let (message, _) = parse_jpip_message(&class_only, &mut context, &limits).unwrap();
    let JpipMessage::Data { header, .. } = message else {
        panic!("data message expected");
    };
    assert_eq!(header.databin().class(), DatabinClass::Metadata);
    assert_eq!(header.databin().codestream(), 1);
}

#[test]
fn parses_end_of_response() {
    let mut context = JpipHeaderContext::new();
    let input = [0, 2, 3, b'e', b'o', b'r'];
    let (message, consumed) =
        parse_jpip_message(&input, &mut context, &ResourceLimits::default()).unwrap();
    let JpipMessage::EndOfResponse(end) = message else {
        panic!("end-of-response expected");
    };
    assert_eq!(end.reason_code(), 2);
    assert_eq!(end.body(), b"eor");
    assert_eq!(consumed, input.len());
}

#[test]
fn rejects_malformed_prefixes_and_vbas() {
    let limits = ResourceLimits::default();
    for input in [
        &[0x01, 0, 0][..],
        &[0x21, 0][..],
        &[0x40, 0x80, 0, 0][..],
        &[0x40, 0x80][..],
        &[0xc0, 8, 0, 0x80][..],
    ] {
        assert!(parse_jpip_message(input, &mut JpipHeaderContext::new(), &limits).is_err());
    }
    let overflow = [
        0xc0, 8, 0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
    ];
    assert!(parse_jpip_message(&overflow, &mut JpipHeaderContext::new(), &limits).is_err());
}

#[test]
fn reassembles_out_of_order_fragments() {
    let target = id(8, 4);
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache.insert(fragment(target, 3, b"def", true)).unwrap();
    assert!(!cache.is_complete(target));
    cache.insert(fragment(target, 0, b"abc", false)).unwrap();
    assert!(cache.is_complete(target));
    assert_eq!(cache.databin_view(target).unwrap().as_bytes(), b"abcdef");
}

#[test]
fn accepts_identical_duplicates_and_overlaps() {
    let target = id(8, 0);
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache.insert(fragment(target, 0, b"abcd", false)).unwrap();
    cache.insert(fragment(target, 0, b"abcd", false)).unwrap();
    cache.insert(fragment(target, 2, b"cdef", true)).unwrap();
    let status = cache.status(target).unwrap();
    assert_eq!(status.interval_count(), 1);
    assert_eq!(status.stored_bytes(), 6);
    assert_eq!(cache.databin_view(target).unwrap().as_bytes(), b"abcdef");
}

#[test]
fn rejects_conflicting_overlap_without_mutation() {
    let target = id(8, 0);
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache.insert(fragment(target, 0, b"abcd", true)).unwrap();
    let before = cache.databin_view(target).unwrap();
    assert!(cache.insert(fragment(target, 2, b"XX", false)).is_err());
    assert_eq!(cache.databin_view(target).unwrap(), before);
    assert_eq!(cache.accepted_fragments(), 1);
}

#[test]
fn rejects_conflicting_final_lengths_and_bytes_past_final() {
    let target = id(8, 0);
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache.insert(fragment(target, 4, b"", true)).unwrap();
    assert!(cache.insert(fragment(target, 3, b"xy", false)).is_err());
    assert!(cache.insert(fragment(target, 5, b"", true)).is_err());
}

#[test]
fn enforces_fragment_limit() {
    let limits = ResourceLimits::default()
        .with_maximum_jpip_fragments(1)
        .unwrap();
    let target = id(8, 0);
    let mut cache = DatabinCache::new(limits);
    cache.insert(fragment(target, 0, b"a", false)).unwrap();
    assert!(matches!(
        cache.insert(fragment(target, 1, b"b", true)),
        Err(DecodeError::LimitExceeded {
            resource: Resource::JpipFragments,
            ..
        })
    ));
}

#[test]
fn reconstructs_codestream_and_container_views() {
    let main = id(6, 0);
    let tile_header = id(2, 0);
    let tile_data = id(4, 0);
    let metadata = id(8, 0);
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache
        .insert(fragment(main, 0, &[0xff, 0x4f], true))
        .unwrap();
    cache
        .insert(fragment(tile_header, 0, &[0xff, 0x90], true))
        .unwrap();
    cache
        .insert(fragment(tile_data, 0, &[0xff, 0xd9], true))
        .unwrap();
    cache.insert(fragment(metadata, 0, b"jp2", true)).unwrap();
    assert_eq!(
        cache
            .reconstruct_codestream(&[main, tile_header, tile_data])
            .unwrap()
            .as_bytes(),
        [0xff, 0x4f, 0xff, 0x90, 0xff, 0xd9]
    );
    assert_eq!(
        cache.reconstruct_container(&[metadata]).unwrap().as_bytes(),
        b"jp2"
    );
}

#[test]
fn reconstructed_codestream_is_consumed_by_decode_api() {
    let bytes = decodable_codestream();
    let tile_start = bytes
        .windows(2)
        .position(|window| window == 0xff90_u16.to_be_bytes())
        .unwrap();
    let tile_data_start = tile_start + 14;
    let main = id(6, 0);
    let tile_header = id(2, 0);
    let tile_data = id(4, 0);
    let limits = ResourceLimits::default();
    let mut cache = DatabinCache::new(limits);
    cache
        .insert(fragment(main, 0, &bytes[..tile_start], true))
        .unwrap();
    cache
        .insert(fragment(
            tile_header,
            0,
            &bytes[tile_start..tile_data_start],
            true,
        ))
        .unwrap();
    cache
        .insert(fragment(tile_data, 0, &bytes[tile_data_start..], true))
        .unwrap();
    let view = cache
        .reconstruct_codestream(&[main, tile_header, tile_data])
        .unwrap();
    let image = crate::decode_codestream(view.as_ref(), &crate::DecodeOptions::default()).unwrap();
    assert_eq!(image.width(), 1);
    assert_eq!(image.height(), 1);
}

#[test]
fn ingests_response_with_inherited_context() {
    let input = [
        0x40, 8, 0, 2, b'a', b'b', // explicit metadata bin 0
        0x31, 0, 1, b'c', // inherited metadata bin 1, final
        0, 1, 0, // EOR
    ];
    let mut cache = DatabinCache::new(ResourceLimits::default());
    let summary = ingest_jpip_response(&input, &mut cache).unwrap();
    assert_eq!(summary.messages(), 2);
    assert_eq!(summary.end_of_response_reason(), Some(1));
    assert_eq!(cache.databin_view(id(8, 1)).unwrap().as_bytes(), b"c");
}

#[test]
fn reports_exact_missing_ranges_for_incomplete_databins() {
    let target = id(0, 9);
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache.insert(fragment(target, 0, b"a", false)).unwrap();
    cache.insert(fragment(target, 3, b"d", false)).unwrap();
    let report = cache
        .availability(&[JpipDatabinRange::new(target, 0, 4).unwrap()])
        .unwrap();
    assert_eq!(report.status(), JpipAvailability::Partial);
    assert_eq!(report.required_bytes(), 4);
    assert_eq!(report.available_bytes(), 2);
    assert_eq!(
        report.missing_ranges(),
        &[JpipMissingRange {
            databin: target,
            offset: 1,
            length: Some(2),
        }]
    );
}

#[test]
fn transcodes_precinct_ranges_into_a_decodable_codestream() {
    let bytes = decodable_codestream_with_layers(2);
    let tile_start = bytes
        .windows(2)
        .position(|window| window == 0xff90_u16.to_be_bytes())
        .unwrap();
    let packet_start = tile_start + 14;
    let main = id(6, 0);
    let tile_header = id(2, 0);
    let precinct = id(0, 0);
    let limits = ResourceLimits::default();
    let mut cache = DatabinCache::new(limits);
    cache
        .insert(fragment(main, 0, &bytes[..tile_start], true))
        .unwrap();
    cache
        .insert(fragment(
            tile_header,
            0,
            &bytes[tile_start..packet_start],
            true,
        ))
        .unwrap();
    cache
        .insert(fragment(
            precinct,
            0,
            &bytes[packet_start..packet_start + 2],
            false,
        ))
        .unwrap();
    let plan = JpipPrecinctCodestreamPlan::new(
        main,
        tile_header,
        vec![
            JpipPrecinctPacket::new(precinct, 0, 0, 1).unwrap(),
            JpipPrecinctPacket::new(precinct, 1, 1, 1).unwrap(),
        ],
        2,
        &limits,
    )
    .unwrap();
    let packets = cache.reconstruct_precinct_packets(&plan, 2).unwrap();
    assert!(packets.availability().is_available());
    assert_eq!(packets.packets().unwrap().as_bytes(), [0, 0]);
    let transcoded = cache.transcode_precinct_codestream(&plan, 1).unwrap();
    assert!(transcoded.availability().is_available());
    let image = crate::decode_codestream(
        transcoded.codestream().unwrap().as_ref(),
        &crate::DecodeOptions::default(),
    )
    .unwrap();
    assert_eq!(image.width(), 1);
    assert_eq!(image.height(), 1);
}

#[test]
fn explicit_precinct_transcodes_require_main_and_effective_tile_lrcp() {
    let limits = ResourceLimits::default();
    let mut cases = 0;
    for main_progression in 0..=4 {
        for tile_progression in [None, Some(0), Some(1), Some(2), Some(3), Some(4)] {
            let mut source = decodable_codestream_with_layers(2);
            let main_cod = source
                .windows(2)
                .position(|window| window == 0xff52_u16.to_be_bytes())
                .unwrap();
            source[main_cod + 5] = main_progression;
            let tile_start = source
                .windows(2)
                .position(|window| window == 0xff90_u16.to_be_bytes())
                .unwrap();
            let tile_cod = tile_progression.map_or_else(Vec::new, |progression| {
                segment(0xff52, &[0, progression, 0, 2, 0, 0, 0, 0, 0, 1])
            });
            source.splice(tile_start + 12..tile_start + 12, tile_cod.iter().copied());
            let packet_start = tile_start + 14 + tile_cod.len();
            let tile_length = u32::try_from(packet_start - tile_start + 2).unwrap();
            source[tile_start + 6..tile_start + 10].copy_from_slice(&tile_length.to_be_bytes());
            let parsed = crate::codestream::parse_layout(&source, &limits).unwrap();
            let effective = tile_progression.unwrap_or(main_progression);
            assert_eq!(
                matches!(
                    parsed.tile_parts[0].coding_style.progression_order,
                    crate::codestream::ProgressionOrder::Lrcp
                ),
                effective == 0
            );
            let main = id(6, 0);
            let tile_header = id(2, 0);
            let precinct = id(0, 0);
            let mut cache = DatabinCache::new(limits);
            cache
                .insert(fragment(main, 0, &source[..tile_start], true))
                .unwrap();
            cache
                .insert(fragment(
                    tile_header,
                    0,
                    &source[tile_start..packet_start],
                    true,
                ))
                .unwrap();
            cache.insert(fragment(precinct, 0, &[0, 0], true)).unwrap();
            let plan = JpipPrecinctCodestreamPlan::new(
                main,
                tile_header,
                vec![
                    JpipPrecinctPacket::new(precinct, 0, 0, 1).unwrap(),
                    JpipPrecinctPacket::new(precinct, 1, 1, 1).unwrap(),
                ],
                2,
                &limits,
            )
            .unwrap();
            for layers in [1, 2] {
                let result = cache.transcode_precinct_codestream(&plan, layers);
                if main_progression == 0 && effective == 0 {
                    let transcoded = result.unwrap();
                    assert!(transcoded.availability().is_available());
                    let bytes = transcoded.codestream().unwrap().as_ref();
                    let layout = crate::codestream::parse_layout(bytes, &limits).unwrap();
                    assert_eq!(layout.tile_parts.len(), 1);
                    assert_eq!(layout.tile_parts[0].coding_style.layers, layers);
                    assert_eq!(layout.tile_parts[0].data, vec![0; usize::from(layers)]);
                    let image =
                        crate::decode_codestream(bytes, &crate::DecodeOptions::default()).unwrap();
                    assert_eq!((image.width(), image.height()), (1, 1));
                } else {
                    assert_eq!(
                        result.err(),
                        Some(DecodeError::MalformedInput {
                            offset: 0,
                            kind: MalformedKind::InvalidJpipLayout,
                        }),
                        "main={main_progression}, tile={tile_progression:?}, layers={layers}"
                    );
                }
                assert_eq!(
                    cache.databin_view(main).unwrap().as_bytes(),
                    &source[..tile_start]
                );
                assert_eq!(
                    cache.databin_view(tile_header).unwrap().as_bytes(),
                    &source[tile_start..packet_start]
                );
                assert_eq!(cache.databin_view(precinct).unwrap().as_bytes(), &[0, 0]);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 60);
}

#[test]
fn progressive_decode_advances_only_after_a_complete_layer() {
    let bytes = decodable_codestream_with_layers(2);
    let tile_start = bytes
        .windows(2)
        .position(|window| window == 0xff90_u16.to_be_bytes())
        .unwrap();
    let packet_start = tile_start + 14;
    let main = id(6, 0);
    let tile_header = id(2, 0);
    let precinct = id(0, 0);
    let limits = ResourceLimits::default();
    let mut cache = DatabinCache::new(limits);
    cache
        .insert(fragment(main, 0, &bytes[..tile_start], true))
        .unwrap();
    cache
        .insert(fragment(
            tile_header,
            0,
            &bytes[tile_start..packet_start],
            true,
        ))
        .unwrap();
    let plan = JpipPrecinctCodestreamPlan::new(
        main,
        tile_header,
        vec![
            JpipPrecinctPacket::new(precinct, 0, 0, 1).unwrap(),
            JpipPrecinctPacket::new(precinct, 1, 1, 1).unwrap(),
        ],
        2,
        &limits,
    )
    .unwrap();
    let mut decoder = JpipProgressiveDecoder::new(plan);
    let waiting = decoder
        .update(&cache, &crate::DecodeOptions::default())
        .unwrap();
    assert_eq!(waiting.status(), JpipProgressiveStatus::WaitingForData);
    assert_eq!(waiting.available_layers(), 0);
    assert_eq!(waiting.missing_ranges()[0].offset(), 0);

    cache
        .insert(fragment(
            precinct,
            0,
            &bytes[packet_start..packet_start + 1],
            false,
        ))
        .unwrap();
    let first = decoder
        .update(&cache, &crate::DecodeOptions::default())
        .unwrap();
    assert_eq!(first.status(), JpipProgressiveStatus::QualityAdvanced);
    assert_eq!(first.previous_layers(), 0);
    assert_eq!(first.available_layers(), 1);
    assert!(first.image().is_some());

    let unchanged = decoder
        .update(&cache, &crate::DecodeOptions::default())
        .unwrap();
    assert_eq!(unchanged.status(), JpipProgressiveStatus::WaitingForData);
    assert!(unchanged.image().is_none());
    assert_eq!(decoder.decoded_layers(), 1);

    cache
        .insert(fragment(
            precinct,
            1,
            &bytes[packet_start + 1..packet_start + 2],
            false,
        ))
        .unwrap();
    let complete = decoder
        .update(&cache, &crate::DecodeOptions::default())
        .unwrap();
    assert_eq!(complete.status(), JpipProgressiveStatus::Complete);
    assert_eq!(complete.available_layers(), 2);
    assert!(complete.missing_ranges().is_empty());
    assert!(complete.image().is_some());
    assert_eq!(decoder.decoded_layers(), 2);
}

#[test]
fn sarah_dev_76bf9f9717_empty_resolutions_do_not_shift_precinct_databin_ids() {
    for progression in 0..5 {
        let mut siz = 0_u16.to_be_bytes().to_vec();
        for value in [2_u32, 2, 1, 1, 2, 2, 0, 0] {
            siz.extend_from_slice(&value.to_be_bytes());
        }
        siz.extend_from_slice(&[0, 1, 7, 1, 1]);
        let mut main = SOC.to_vec();
        main.extend(segment(0xff51, &siz));
        main.extend(segment(0xff52, &[0, progression, 0, 1, 0, 3, 0, 0, 0, 1]));
        main.extend(segment(0xff5c, &[0x40; 11]));
        let mut sot = vec![0, 0];
        sot.extend_from_slice(&15_u32.to_be_bytes());
        sot.extend_from_slice(&[0, 1]);
        let mut header = segment(0xff90, &sot);
        header.extend_from_slice(&[0xff, 0x93]);
        let mut cache = DatabinCache::new(ResourceLimits::default());
        cache.insert(fragment(id(6, 0), 0, &main, true)).unwrap();
        cache.insert(fragment(id(2, 0), 0, &header, true)).unwrap();
        let map = cache.derive_precinct_map(0).unwrap();
        assert_eq!(map.mappings().len(), 1);
        assert_eq!(
            map.mappings()[0].coordinate(),
            JpipPrecinctCoordinate {
                tile: 0,
                component: 0,
                resolution: 3,
                precinct: 0,
            }
        );
        assert_eq!(map.mappings()[0].databin().in_class(), 0);
    }
}

#[test]
fn automatic_tile_partition_derives_packet_fields_missing_and_exact_boundary_errors() {
    let mut bytes = decodable_codestream();
    let cod = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x52])
        .unwrap();
    bytes[cod + 4] = 6;
    let limits = ResourceLimits::default();
    let layout = crate::codestream::parse_layout(&bytes, &limits).unwrap();
    let states = [&layout.tile_parts[0], &layout.tile_parts[0]];
    let headers = [vec![1, 2], vec![3, 4, 5]];
    let transition = |packet_count, data_length| JpipTilePartTransition {
        tile: 0,
        tile_part: 0,
        packet_count,
        data_length,
        functional: false,
        header: Vec::new(),
    };
    let mut transitions = [transition(Some(1), Some(999)), transition(None, None)];
    let packets = [
        AutomaticPacket {
            databin: id(0, 7),
            bytes: Some(vec![11, 22]),
            next_offset: 2,
            required: true,
            ordinal: 9,
            layer: 0,
        },
        AutomaticPacket {
            databin: id(0, 8),
            bytes: Some(vec![33]),
            next_offset: 1,
            required: false,
            ordinal: 10,
            layer: 1,
        },
        AutomaticPacket {
            databin: id(0, 9),
            bytes: None,
            next_offset: 4,
            required: true,
            ordinal: 11,
            layer: 2,
        },
    ];
    let projected = |packet: &AutomaticPacket| {
        (
            packet.databin,
            packet.bytes.clone(),
            packet.next_offset,
            packet.required,
            packet.ordinal,
            packet.layer,
        )
    };
    let parts = partition_automatic_tile_parts(&headers, &states, &transitions, &packets)
        .unwrap()
        .unwrap();
    assert_eq!(parts.len(), 2);
    for (index, part) in parts.iter().enumerate() {
        assert_eq!(part.header, headers[index]);
        assert_eq!((part.sop, part.eph), (true, true));
    }
    assert_eq!(
        parts[0].packets.iter().map(&projected).collect::<Vec<_>>(),
        packets[..1].iter().map(&projected).collect::<Vec<_>>()
    );
    assert_eq!(
        parts[1].packets.iter().map(&projected).collect::<Vec<_>>(),
        packets[1..].iter().map(&projected).collect::<Vec<_>>()
    );
    assert_ne!(parts[0].header.as_ptr(), headers[0].as_ptr());
    assert_ne!(
        parts[0].packets[0].bytes.as_ref().unwrap().as_ptr(),
        packets[0].bytes.as_ref().unwrap().as_ptr()
    );
    transitions[0].packet_count = None;
    transitions[0].data_length = Some(3);
    let by_length = partition_automatic_tile_parts(&headers, &states, &transitions, &packets)
        .unwrap()
        .unwrap();
    assert_eq!(by_length[0].packets.len(), 2);
    transitions[0].data_length = Some(4);
    assert!(
        partition_automatic_tile_parts(&headers, &states, &transitions, &packets)
            .unwrap()
            .is_none()
    );
    transitions[0].data_length = Some(1);
    assert_eq!(
        partition_automatic_tile_parts(&headers, &states, &transitions, &packets).err(),
        Some(DecodeError::malformed(
            2,
            MalformedKind::InvalidPacketLength
        ))
    );
    assert_eq!(
        partition_automatic_tile_parts(&headers[..1], &states, &transitions, &packets).err(),
        Some(DecodeError::malformed(0, MalformedKind::InvalidTilePart))
    );
}

#[test]
fn automatic_header_inputs_preserve_cache_siz_and_reservation_error_order() {
    let limits = ResourceLimits::default();
    let mut cache = DatabinCache::new(limits);
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            cache.automatic_headers(0).err(),
            Some(DecodeError::malformed(
                0,
                MalformedKind::MissingRequiredStructure
            ))
        );
        assert_eq!(
            crate::allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
    let bytes = decodable_codestream();
    let sot = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x90])
        .unwrap();
    cache
        .insert(fragment(id(6, 0), 0, &bytes[..sot], true))
        .unwrap();
    assert_eq!(
        crate::allocation::with_refusal(0, || cache.automatic_headers(0)).err(),
        Some(DecodeError::AllocationFailed)
    );
    crate::allocation::with_refusal(1, || {
        assert_eq!(
            cache.automatic_headers(0).err(),
            Some(DecodeError::malformed(
                0,
                MalformedKind::MissingRequiredStructure
            ))
        );
        assert_eq!(
            crate::allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
    let mut invalid = DatabinCache::new(limits);
    invalid
        .insert(fragment(id(6, 0), 0, &[0xff, 0x4f, 0xff], true))
        .unwrap();
    crate::allocation::with_refusal(0, || {
        assert_eq!(
            invalid.automatic_headers(0).err(),
            Some(DecodeError::malformed(2, MalformedKind::Truncated))
        );
        assert_eq!(
            crate::allocation::empty_with_capacity::<u8>(1),
            Err(DecodeError::AllocationFailed)
        );
    });
}

#[test]
fn automatic_header_inputs_derive_exact_fields_and_recover_after_managed_refusal() {
    let bytes = decodable_codestream();
    let sot = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x90])
        .unwrap();
    let end = sot + 14;
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache
        .insert(fragment(id(6, 0), 0, &bytes[..sot], true))
        .unwrap();
    cache
        .insert(fragment(id(2, 0), 0, &bytes[sot..end], true))
        .unwrap();
    let mut tile = bytes[sot..end].to_vec();
    tile[6..10].fill(0);
    let expected = (bytes[..sot].to_vec(), vec![tile], 1_u64, 1_u16);
    let collect = |cache: &DatabinCache| {
        cache.automatic_headers(0).map(|headers| {
            (
                headers.main,
                headers.tiles,
                headers.tile_count,
                headers.components,
            )
        })
    };
    let owner = (
        cache.databins.as_ptr(),
        cache.databins.len(),
        cache.stored_bytes,
        cache.accepted_fragments,
    );
    let mut refusals = 0;
    let mut complete = false;
    for ordinal in 0..32 {
        match crate::allocation::with_refusal(ordinal, || collect(&cache)) {
            Err(DecodeError::AllocationFailed) => {
                refusals += 1;
                assert_eq!(collect(&cache).unwrap(), expected);
            }
            Ok(actual) => {
                assert_eq!(actual, expected);
                complete = true;
            }
            Err(error) => panic!("unexpected automatic header error: {error}"),
        }
        assert_eq!(
            (
                cache.databins.as_ptr(),
                cache.databins.len(),
                cache.stored_bytes,
                cache.accepted_fragments
            ),
            owner
        );
        if complete {
            break;
        }
    }
    assert!(refusals > 0 && complete);
}

#[test]
fn automatic_managed_allocation_refusals_preserve_state_and_recover_exact_images() {
    let bytes = decodable_codestream_with_layers(2);
    let tile_start = bytes
        .windows(2)
        .position(|window| window == 0xff90_u16.to_be_bytes())
        .unwrap();
    let packet_start = tile_start + 14;
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache
        .insert(fragment(id(6, 0), 0, &bytes[..tile_start], true))
        .unwrap();
    cache
        .insert(fragment(
            id(2, 0),
            0,
            &bytes[tile_start..packet_start],
            true,
        ))
        .unwrap();
    cache
        .insert(fragment(
            id(0, 0),
            0,
            &bytes[packet_start..packet_start + 2],
            true,
        ))
        .unwrap();
    let options = crate::DecodeOptions::default();
    let expected = crate::decode_codestream(&bytes, &options).unwrap();
    let selection = crate::DecodeSelection::full_image();
    let packets = JpipPacketSelection::all_components();
    for selected in [false, true] {
        let mut refusals = 0;
        let mut reached_end = false;
        for ordinal in 0..32 {
            let mut decoder = JpipAutomaticProgressiveDecoder::new(0);
            let result = crate::allocation::with_refusal(ordinal, || {
                if selected {
                    decoder.update_selected(&cache, &options, &selection, &packets)
                } else {
                    decoder.update(&cache, &options)
                }
            });
            let update = match result {
                Err(DecodeError::AllocationFailed) => {
                    refusals += 1;
                    assert_eq!(decoder.decoded_layers(), 0);
                    if selected {
                        decoder.update_selected(&cache, &options, &selection, &packets)
                    } else {
                        decoder.update(&cache, &options)
                    }
                    .unwrap()
                }
                Ok(update) => {
                    reached_end = true;
                    update
                }
                Err(error) => panic!("unexpected managed-refusal error: {error}"),
            };
            assert_eq!(update.image(), Some(&expected));
            assert_eq!(update.status(), JpipProgressiveStatus::Complete);
            assert_eq!(decoder.decoded_layers(), 2);
            if reached_end {
                break;
            }
        }
        assert!(refusals > 0);
        assert!(
            reached_end,
            "managed request sweep exceeded its bounded fixture profile"
        );
    }
}

#[test]
fn automatic_mapping_decodes_incomplete_precinct_quality_prefixes() {
    let bytes = decodable_codestream_with_layers(2);
    let tile_start = bytes
        .windows(2)
        .position(|window| window == 0xff90_u16.to_be_bytes())
        .unwrap();
    let packet_start = tile_start + 14;
    let main = id(6, 0);
    let tile_header = id(2, 0);
    let precinct_with_auxiliary = id(1, 0);
    let limits = ResourceLimits::default();
    let mut cache = DatabinCache::new(limits);
    cache
        .insert(fragment(main, 0, &bytes[..tile_start], true))
        .unwrap();
    cache
        .insert(fragment(
            tile_header,
            0,
            &bytes[tile_start..packet_start],
            true,
        ))
        .unwrap();
    let mapping = cache.derive_precinct_map(0).unwrap();
    assert_eq!(mapping.mappings().len(), 1);
    assert_eq!(mapping.mappings()[0].databin().in_class(), 0);
    assert_eq!(
        mapping.mappings()[0].coordinate(),
        JpipPrecinctCoordinate {
            tile: 0,
            component: 0,
            resolution: 0,
            precinct: 0,
        }
    );

    let mut decoder = JpipAutomaticProgressiveDecoder::new(0);
    let waiting = decoder
        .update(&cache, &crate::DecodeOptions::default())
        .unwrap();
    assert_eq!(waiting.status(), JpipProgressiveStatus::WaitingForData);
    assert_eq!(waiting.available_layers(), 0);

    cache
        .insert(fragment(
            precinct_with_auxiliary,
            0,
            &bytes[packet_start..packet_start + 1],
            false,
        ))
        .unwrap();
    let first = decoder
        .update(&cache, &crate::DecodeOptions::default())
        .unwrap();
    assert_eq!(first.status(), JpipProgressiveStatus::QualityAdvanced);
    assert_eq!(first.available_layers(), 1);
    assert!(first.image().is_some());

    cache
        .insert(fragment(
            precinct_with_auxiliary,
            1,
            &bytes[packet_start + 1..packet_start + 2],
            false,
        ))
        .unwrap();
    let complete = decoder
        .update(&cache, &crate::DecodeOptions::default())
        .unwrap();
    assert_eq!(complete.status(), JpipProgressiveStatus::Complete);
    assert_eq!(complete.available_layers(), 2);
    assert!(complete.image().is_some());

    let selection = crate::DecodeSelection::full_image()
        .with_region(crate::ImageRegion::new(0, 0, 1, 1))
        .with_discard_levels(0);
    let components = JpipPacketSelection::components(vec![0]);
    let mut selected = JpipAutomaticProgressiveDecoder::new(0);
    let update = selected
        .update_selected(
            &cache,
            &crate::DecodeOptions::default(),
            &selection,
            &components,
        )
        .unwrap();
    assert_eq!(update.status(), JpipProgressiveStatus::Complete);
    assert_eq!(update.image().unwrap().width(), 1);
    let cache_counters = (cache.stored_bytes, cache.accepted_fragments);
    for rejected_components in [vec![1], vec![0, 0]] {
        crate::allocation::with_refusal(0, || {
            assert_eq!(
                selected
                    .update_selected(
                        &cache,
                        &crate::DecodeOptions::default(),
                        &selection,
                        &JpipPacketSelection::components(rejected_components),
                    )
                    .err(),
                Some(DecodeError::InvalidSelection {
                    reason: crate::SelectionError::EmptyComponentIntersection,
                })
            );
            assert_eq!(selected.decoded_layers(), 2);
            assert_eq!(selected.codestream(), 0);
            assert_eq!(
                (cache.stored_bytes, cache.accepted_fragments),
                cache_counters
            );
            assert_eq!(
                crate::allocation::empty_with_capacity::<u8>(1),
                Err(DecodeError::AllocationFailed)
            );
        });
    }
    let repeated = selected
        .update_selected(
            &cache,
            &crate::DecodeOptions::default(),
            &selection,
            &components,
        )
        .unwrap();
    assert_eq!(repeated.status(), JpipProgressiveStatus::Complete);
    assert_eq!(repeated.previous_layers(), 2);
    assert_eq!(repeated.available_layers(), 2);
    assert!(repeated.image().is_none());
}

#[test]
fn automatic_header_normalization_removes_reframed_markers() {
    let mut main = SOC.to_vec();
    main.extend(segment(0xff51, &[0; 36]));
    main.extend(segment(0xff55, &[0]));
    main.extend(segment(0xff57, &[0]));
    main.extend(segment(0xff60, &[0]));
    let normalized = normalize_main_header(&main).unwrap();
    assert!(!normalized.windows(2).any(|value| value == [0xff, 0x55]));
    assert!(!normalized.windows(2).any(|value| value == [0xff, 0x57]));
    assert!(!normalized.windows(2).any(|value| value == [0xff, 0x60]));

    let mut tile = vec![0xff, 0x90, 0, 10, 0, 0, 0, 0, 0, 14, 0, 1];
    tile.extend(segment(0xff58, &[0]));
    tile.extend(segment(0xff61, &[0]));
    tile.extend_from_slice(&[0xff, 0x93]);
    let declared_length = u32::try_from(tile.len()).unwrap();
    tile[6..10].copy_from_slice(&declared_length.to_be_bytes());
    let normalized_tile = normalize_automatic_tile_headers(&tile, 0)
        .unwrap()
        .remove(0);
    assert!(
        !normalized_tile
            .windows(2)
            .any(|value| value == [0xff, 0x58])
    );
    assert!(
        !normalized_tile
            .windows(2)
            .any(|value| value == [0xff, 0x61])
    );
    assert!(normalized_tile.ends_with(&[0xff, 0x93]));

    let mut ambiguous = tile;
    ambiguous[11] = 2;
    let mut second = vec![0xff, 0x90, 0, 10, 0, 0, 0, 0, 0, 14, 1, 2];
    second.extend(segment(0xff52, &[0, 0, 0, 1, 0, 0, 0, 0, 0, 1]));
    second.extend_from_slice(&[0xff, 0x93]);
    let declared_length = u32::try_from(second.len()).unwrap();
    second[6..10].copy_from_slice(&declared_length.to_be_bytes());
    ambiguous.extend(second);
    let normalized = normalize_automatic_tile_headers(&ambiguous, 0).unwrap();
    assert_eq!(normalized.len(), 2);
    assert!(normalized[1].windows(2).any(|value| value == [0xff, 0x52]));
}

#[test]
fn automatic_snapshot_template_parse_error_keeps_canonical_bytes_and_cache_inputs() {
    let mut bytes = decodable_codestream();
    let cod = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x52])
        .unwrap();
    bytes[cod + 9] = u8::MAX;
    let sot = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x90])
        .unwrap();
    let packet = sot + 14;
    let limits = ResourceLimits::default();
    let main = &bytes[..sot];
    let tile = &bytes[sot..packet];
    let normalized_main = normalize_main_header(main).unwrap();
    let normalized_tiles = vec![normalize_automatic_tile_headers(tile, 0).unwrap()];
    let template =
        build_automatic_transition_template(&normalized_main, &normalized_tiles, &limits).unwrap();
    assert_eq!(&template[..normalized_main.len()], &normalized_main);
    let expected = crate::codestream::parse_layout(&template, &limits)
        .err()
        .unwrap();
    assert_eq!(
        expected,
        DecodeError::malformed(cod as u64, MalformedKind::ArithmeticOverflow)
    );
    let mut cache = DatabinCache::new(limits);
    cache.insert(fragment(id(6, 0), 0, main, true)).unwrap();
    cache.insert(fragment(id(2, 0), 0, tile, true)).unwrap();
    let selected = JpipPacketSelection::all_components();
    for _ in 0..2 {
        assert_eq!(
            cache
                .build_automatic_snapshot(0, None, &selected, &limits)
                .err(),
            Some(expected)
        );
        assert_eq!(cache.databin_view(id(6, 0)).unwrap().as_ref(), main);
        assert_eq!(cache.databin_view(id(2, 0)).unwrap().as_ref(), tile);
    }
}

#[test]
fn automatic_precinct_phase_preserves_lookup_and_truncation_error_frames_then_recovers() {
    let bytes = decodable_codestream();
    let limits = ResourceLimits::default();
    let layout = crate::codestream::parse_layout(&bytes, &limits).unwrap();
    let part = &layout.tile_parts[0];
    let make_plan = || {
        crate::decode::plan_progression_tile_at_with_component_overrides(
            &layout.info.image_size,
            0,
            part.coding_style,
            &part.component_coding_styles,
            &part.component_quantizations,
            &part.roi_shifts,
            &limits,
        )
        .unwrap()
    };
    let mut plan = make_plan();
    let owner = plan.precincts().as_ptr();
    let coordinate = plan.precincts()[0].coordinate();
    let states = plan.precincts()[0].states().to_vec();
    let prefix = Vec::new();
    assert_eq!(
        decode_automatic_precinct(&mut plan, usize::MAX, part, &prefix, 0, 0, 0, &limits),
        Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))
    );
    assert_eq!(plan.precincts().as_ptr(), owner);
    assert_eq!(plan.precincts()[0].states(), states);
    assert_eq!(
        decode_automatic_precinct(&mut plan, 0, part, &prefix, 0, 0, 0, &limits),
        Err(DecodeError::malformed(0, MalformedKind::Truncated))
    );
    assert_eq!(plan.precincts().as_ptr(), owner);
    assert_eq!(plan.precincts()[0].coordinate(), coordinate);
    assert_eq!(plan.precincts()[0].states(), states);
    let mut fresh = make_plan();
    let prefix = vec![0];
    assert_eq!(
        decode_automatic_precinct(&mut plan, 0, part, &prefix, 0, 0, 0, &limits),
        Ok(1)
    );
    assert_eq!(
        decode_automatic_precinct(&mut fresh, 0, part, &prefix, 0, 0, 0, &limits),
        Ok(1)
    );
    assert_eq!(plan.precincts()[0].states(), fresh.precincts()[0].states());
}

#[test]
fn automatic_emission_phase_retains_partial_payload_errors_before_psot_and_exact_empty_framing() {
    let header = vec![0xff, 0x90, 0, 10, 0, 0, 9, 8, 7, 6, 0, 1, 0xff, 0x93];
    let mut part = AutomaticTilePart {
        header,
        packets: vec![
            AutomaticPacket {
                databin: id(0, 0),
                bytes: Some(vec![19, 20]),
                next_offset: 2,
                required: true,
                ordinal: 0,
                layer: 0,
            },
            AutomaticPacket {
                databin: id(0, 1),
                bytes: None,
                next_offset: 13,
                required: true,
                ordinal: 0x1234,
                layer: 1,
            },
        ],
        sop: true,
        eph: true,
    };
    let header_owner = (part.header.as_ptr(), part.header.capacity());
    let payload_owner = part.packets[0].bytes.as_ref().unwrap().as_ptr();
    let mut bytes = vec![31, 32];
    let mut partial = bytes.clone();
    partial.extend_from_slice(&part.header);
    partial.extend_from_slice(&[19, 20]);
    assert_eq!(
        emit_automatic_tile_part(&mut bytes, &part, 2),
        Err(DecodeError::malformed(
            13,
            MalformedKind::MissingRequiredStructure
        ))
    );
    assert_eq!(bytes, partial);
    assert_eq!(&bytes[8..12], &[9, 8, 7, 6]);
    assert_eq!((part.header.as_ptr(), part.header.capacity()), header_owner);
    assert_eq!(
        part.packets[0].bytes.as_ref().unwrap().as_ptr(),
        payload_owner
    );

    let mut bytes = vec![31, 32];
    let mut expected = partial;
    expected.extend_from_slice(&[0xff, 0x91, 0, 4, 0x12, 0x34, 0, 0xff, 0x92]);
    let length = u32::try_from(expected.len() - 2).unwrap();
    expected[8..12].copy_from_slice(&length.to_be_bytes());
    assert_eq!(emit_automatic_tile_part(&mut bytes, &part, 1), Ok(()));
    assert_eq!(bytes, expected);

    part.header = vec![7; 9];
    part.packets.clear();
    let mut bytes = vec![31, 32];
    assert_eq!(
        emit_automatic_tile_part(&mut bytes, &part, 1),
        Err(DecodeError::malformed(8, MalformedKind::Truncated))
    );
    assert_eq!(bytes, [vec![31, 32], vec![7; 9]].concat());
}

#[test]
fn automatic_order_phase_preserves_exact_partial_error_states_and_next_call_order() {
    let mut bytes = decodable_codestream();
    let cod = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x52])
        .unwrap();
    bytes[cod + 6..cod + 8].copy_from_slice(&2_u16.to_be_bytes());
    let limits = ResourceLimits::default();
    let layout = crate::codestream::parse_layout(&bytes, &limits).unwrap();
    let part = &layout.tile_parts[0];
    let plan = crate::decode::plan_progression_tile_at_with_component_overrides(
        &layout.info.image_size,
        0,
        part.coding_style,
        &part.component_coding_styles,
        &part.component_quantizations,
        &part.roi_shifts,
        &limits,
    )
    .unwrap();
    assert_eq!(plan.precincts().len(), 1);
    let make_iterator = || {
        crate::packet::ProgressionPacketIterator::new(
            plan.grid(),
            part.coding_style.progression_order,
            &part.progression_changes,
            &limits,
        )
        .unwrap()
    };
    let error = DecodeError::malformed(0, MalformedKind::InvalidProgressionOrderChange);
    let mut iterator = make_iterator();
    let mut ordinals = vec![vec![None, Some(91)]];
    let mut order = Vec::with_capacity(2);
    let owner = (
        order.as_ptr(),
        order.capacity(),
        ordinals.as_ptr(),
        ordinals[0].as_ptr(),
    );
    assert_eq!(
        build_automatic_order(&plan, &mut iterator, &mut ordinals, &mut order, &limits),
        Err(error)
    );
    assert_eq!(iterator.emitted(), 2);
    assert_eq!(ordinals, vec![vec![Some(0), Some(91)]]);
    assert_eq!(order.len(), 1);
    assert_eq!((order[0].0.layer, order[0].1), (0, 0));
    assert_eq!(
        (
            order.as_ptr(),
            order.capacity(),
            ordinals.as_ptr(),
            ordinals[0].as_ptr()
        ),
        owner
    );

    let mut iterator = make_iterator();
    let mut ordinals = vec![vec![None; 2]];
    let mut order = Vec::new();
    let small = limits.with_maximum_work_units(1).unwrap();
    assert_eq!(
        build_automatic_order(&plan, &mut iterator, &mut ordinals, &mut order, &small),
        Err(error)
    );
    assert_eq!(iterator.emitted(), 2);
    assert_eq!(ordinals, vec![vec![Some(0), None]]);
    assert_eq!(order.len(), 1);

    let mut iterator = make_iterator();
    let mut ordinals = Vec::new();
    let mut order = Vec::new();
    assert_eq!(
        build_automatic_order(&plan, &mut iterator, &mut ordinals, &mut order, &limits),
        Err(error)
    );
    assert_eq!(iterator.emitted(), 1);
    assert!(ordinals.is_empty() && order.is_empty());
}

#[test]
fn automatic_mapping_supports_progressions_poc_sop_eph_and_reframed_headers() {
    let limits = ResourceLimits::default();
    for progression in 0_u8..=4 {
        let mut bytes = decodable_codestream();
        let cod = bytes
            .windows(2)
            .position(|value| value == [0xff, 0x52])
            .unwrap();
        bytes[cod + 5] = progression;
        let sot = bytes
            .windows(2)
            .position(|value| value == [0xff, 0x90])
            .unwrap();
        if progression == 1 {
            bytes.splice(sot..sot, segment(0xff5f, &[0, 0, 0, 1, 1, 1, 1]));
        }
        let sot = bytes
            .windows(2)
            .position(|value| value == [0xff, 0x90])
            .unwrap();
        let packet = sot + 14;
        let mut cache = DatabinCache::new(limits);
        cache
            .insert(fragment(id(6, 0), 0, &bytes[..sot], true))
            .unwrap();
        cache
            .insert(fragment(id(2, 0), 0, &bytes[sot..packet], true))
            .unwrap();
        cache
            .insert(fragment(id(0, 0), 0, &bytes[packet..packet + 1], false))
            .unwrap();
        let mut decoder = JpipAutomaticProgressiveDecoder::new(0);
        let update = decoder
            .update(&cache, &crate::DecodeOptions::default())
            .unwrap();
        assert_eq!(update.status(), JpipProgressiveStatus::Complete);
        assert!(update.image().is_some());
    }

    let mut bytes = decodable_codestream();
    let cod = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x52])
        .unwrap();
    bytes[cod + 4] = 6;
    let sot = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x90])
        .unwrap();
    let packet = sot + 14;
    bytes.splice(packet..packet + 1, [0xff, 0x91, 0, 4, 0, 0, 0, 0xff, 0x92]);
    let psot = 23_u32.to_be_bytes();
    bytes[sot + 6..sot + 10].copy_from_slice(&psot);
    let mut cache = DatabinCache::new(limits);
    cache
        .insert(fragment(id(6, 0), 0, &bytes[..sot], true))
        .unwrap();
    let mut tile_header = bytes[sot..packet].to_vec();
    tile_header.splice(
        tile_header.len() - 2..tile_header.len() - 2,
        segment(0xff58, &[0]),
    );
    tile_header.splice(
        tile_header.len() - 2..tile_header.len() - 2,
        segment(0xff61, &[0]),
    );
    let declared_length = u32::try_from(tile_header.len() + 9).unwrap();
    tile_header[6..10].copy_from_slice(&declared_length.to_be_bytes());
    cache
        .insert(fragment(id(2, 0), 0, &tile_header, true))
        .unwrap();
    cache
        .insert(fragment(id(0, 0), 0, &bytes[packet..packet + 9], false))
        .unwrap();
    let mut decoder = JpipAutomaticProgressiveDecoder::new(0);
    assert_eq!(
        decoder
            .update(&cache, &crate::DecodeOptions::default())
            .unwrap()
            .status(),
        JpipProgressiveStatus::Complete
    );
}

#[test]
fn automatic_mapping_interleaves_multiple_tiles_and_collapses_tile_parts() {
    let bytes = two_tile_codestream();
    let first_sot = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x90])
        .unwrap();
    let second_sot = bytes[first_sot + 2..]
        .windows(2)
        .position(|value| value == [0xff, 0x90])
        .map(|value| value + first_sot + 2)
        .unwrap();
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache
        .insert(fragment(id(6, 0), 0, &bytes[..first_sot], true))
        .unwrap();
    cache
        .insert(fragment(
            id(2, 0),
            0,
            &bytes[first_sot..first_sot + 14],
            true,
        ))
        .unwrap();
    cache
        .insert(fragment(
            id(2, 1),
            0,
            &bytes[second_sot..second_sot + 14],
            true,
        ))
        .unwrap();
    cache.insert(fragment(id(0, 0), 0, &[0], false)).unwrap();
    cache.insert(fragment(id(0, 1), 0, &[0], false)).unwrap();
    let mapping = cache.derive_precinct_map(0).unwrap();
    assert_eq!(mapping.mappings().len(), 2);
    assert_eq!(mapping.mappings()[0].databin().in_class(), 0);
    assert_eq!(mapping.mappings()[1].databin().in_class(), 1);
    let mut decoder = JpipAutomaticProgressiveDecoder::new(0);
    let update = decoder
        .update(&cache, &crate::DecodeOptions::default())
        .unwrap();
    assert_eq!(update.status(), JpipProgressiveStatus::Complete);
    assert_eq!(update.image().unwrap().width(), 2);

    let two_layers = decodable_codestream_with_layers(2);
    let sot = two_layers
        .windows(2)
        .position(|value| value == [0xff, 0x90])
        .unwrap();
    let mut tile_headers = two_layers[sot..sot + 14].to_vec();
    let mut second = tile_headers.clone();
    second[10] = 1;
    second[11] = 2;
    tile_headers[11] = 2;
    tile_headers.extend_from_slice(&second);
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache
        .insert(fragment(id(6, 0), 0, &two_layers[..sot], true))
        .unwrap();
    cache
        .insert(fragment(id(2, 0), 0, &tile_headers, true))
        .unwrap();
    cache.insert(fragment(id(0, 0), 0, &[0, 0], false)).unwrap();
    let mut decoder = JpipAutomaticProgressiveDecoder::new(0);
    assert_eq!(
        decoder
            .update(&cache, &crate::DecodeOptions::default())
            .unwrap()
            .status(),
        JpipProgressiveStatus::Complete
    );
}

#[test]
fn semantic_metadata_assembly_places_nested_boxes_and_codestreams() {
    let codestream = decodable_codestream();
    let sot = codestream
        .windows(2)
        .position(|value| value == [0xff, 0x90])
        .unwrap();
    let packet = sot + 14;
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut jp2h_payload = box32(*b"ihdr", &image_header);
    jp2h_payload.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
    let jp2h_length = u32::try_from(jp2h_payload.len() + 8).unwrap();
    let mut root = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
    root.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    root.extend(metadata_placeholder(*b"jp2h", jp2h_length, 1, 1, None));
    root.extend(metadata_placeholder(
        *b"jp2c",
        u32::try_from(codestream.len() + 8).unwrap(),
        4,
        0,
        Some(0),
    ));

    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache.insert(fragment(id(8, 0), 0, &root, true)).unwrap();
    let missing_metadata = cache.assemble_semantic_container(0).unwrap();
    assert_eq!(missing_metadata.status(), JpipAvailability::Partial);
    assert_eq!(
        missing_metadata.semantic_needs()[0].kind(),
        JpipSemanticNeedKind::MetadataBin
    );

    cache
        .insert(fragment(id(8, 1), 0, &jp2h_payload, true))
        .unwrap();
    let missing_codestream = cache.assemble_semantic_container(0).unwrap();
    assert_eq!(missing_codestream.status(), JpipAvailability::Partial);
    assert!(
        missing_codestream
            .semantic_needs()
            .iter()
            .any(|need| need.kind() == JpipSemanticNeedKind::Codestream)
    );

    cache
        .insert(fragment(id(6, 0), 0, &codestream[..sot], true))
        .unwrap();
    cache
        .insert(fragment(id(2, 0), 0, &codestream[sot..packet], true))
        .unwrap();
    cache
        .insert(fragment(
            id(0, 0),
            0,
            &codestream[packet..packet + 1],
            false,
        ))
        .unwrap();
    let assembled = cache.assemble_semantic_container(0).unwrap();
    assert_eq!(assembled.status(), JpipAvailability::Available);
    assert!(assembled.semantic_needs().is_empty());
    let container = assembled.container().unwrap();
    let inspected =
        crate::jp2::parse_and_inspect(container.as_bytes(), &ResourceLimits::default()).unwrap();
    assert_eq!(inspected.file.codestream_count(), 1);
    assert!(
        container
            .as_bytes()
            .windows(4)
            .all(|value| value != b"phld")
    );
}

#[test]
fn sarah_optional_sod_complete_header_forms_normalize_identically() {
    for tile in [0_u16, 1, 255, 256, 65534] {
        for retained in [
            Vec::new(),
            segment(0xff64, &[0, 1]),
            segment(0xff64, &[0, 1, b'j', b'p', b'p']),
        ] {
            let mut expected = vec![0xff, 0x90, 0, 10];
            expected.extend_from_slice(&tile.to_be_bytes());
            expected.extend_from_slice(&[0, 0, 0, 0, 0, 1]);
            expected.extend_from_slice(&retained);
            expected.extend_from_slice(&[0xff, 0x93]);
            for sod in [false, true] {
                let mut wire = retained.clone();
                if sod {
                    wire.extend_from_slice(&[0xff, 0x93]);
                }
                assert_eq!(
                    super::automatic_headers::normalize_automatic_tile_headers(&wire, tile)
                        .unwrap(),
                    vec![expected.clone()],
                    "tile={tile} SOD={sod}"
                );
            }
        }
    }
}

#[test]
fn sarah_optional_sod_public_snapshot_decodes_complete_empty_header() {
    let code = decodable_codestream();
    let sot = code
        .windows(2)
        .position(|bytes| bytes == [0xff, 0x90])
        .unwrap();
    let packet = sot + 14;
    for tile_header in [Vec::new(), vec![0xff, 0x93], segment(0xff64, &[0, 1])] {
        let mut cache = DatabinCache::new(ResourceLimits::default());
        cache
            .insert(fragment(id(6, 0), 0, &code[..sot], true))
            .unwrap();
        cache
            .insert(fragment(id(2, 0), 0, &tile_header, true))
            .unwrap();
        cache
            .insert(fragment(id(0, 0), 0, &code[packet..packet + 1], true))
            .unwrap();
        assert!(cache.is_complete(id(2, 0)));
        let mut decoder = JpipAutomaticProgressiveDecoder::new(0);
        let update = decoder
            .update(&cache, &crate::DecodeOptions::default())
            .unwrap();
        assert_eq!(update.status(), JpipProgressiveStatus::Complete);
        assert!(update.image().is_some());
    }
}

fn equivalent_metadata_fixture(
    whole_header: bool,
    original_extended: bool,
    equivalent_extended: bool,
    flags: u32,
) -> (DatabinCache, Vec<u8>) {
    fn header(kind: [u8; 4], length: usize, extended: bool) -> Vec<u8> {
        if extended {
            let mut bytes = 1_u32.to_be_bytes().to_vec();
            bytes.extend_from_slice(&kind);
            bytes.extend_from_slice(&u64::try_from(length + 16).unwrap().to_be_bytes());
            bytes
        } else {
            box32(kind, &vec![0; length])[..8].to_vec()
        }
    }

    let color = [1, 0, 0, 0, 0, 0, 17];
    let mut image_header = 1_u32.to_be_bytes().to_vec();
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let image_fields = box32(*b"ihdr", &image_header);
    let mut plain_header = image_fields.clone();
    plain_header.extend(box32(*b"colr", &color));
    let equivalent_payload = if flags & 1 != 0 {
        b"<not-the-original/>".to_vec()
    } else if whole_header {
        plain_header.clone()
    } else {
        color.to_vec()
    };
    let original_type = if flags & 1 != 0 { *b"colr" } else { *b"xref" };
    let equivalent_type = if flags & 1 != 0 {
        *b"xml "
    } else if whole_header {
        *b"jp2h"
    } else {
        *b"colr"
    };
    let original_header = header(original_type, color.len(), original_extended);
    let equivalent_header = header(
        equivalent_type,
        equivalent_payload.len(),
        equivalent_extended,
    );
    let mut fields = flags.to_be_bytes().to_vec();
    fields.extend_from_slice(&3_u64.to_be_bytes());
    fields.extend_from_slice(&original_header);
    fields.extend_from_slice(&2_u64.to_be_bytes());
    fields.extend_from_slice(&equivalent_header);
    let placeholder = box32(*b"phld", &fields);

    let mut root = box32(*b"jP  ", &[13, 10, 135, 10]);
    root.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    let mut expected = root.clone();
    let mut cache = DatabinCache::new(ResourceLimits::default());
    if whole_header {
        root.extend(placeholder);
        expected.extend(equivalent_header);
        expected.extend(&equivalent_payload);
    } else {
        let mut transported = image_fields.clone();
        transported.extend(placeholder);
        root.extend(metadata_placeholder(
            *b"jp2h",
            u32::try_from(transported.len() + 8).unwrap(),
            1,
            1,
            None,
        ));
        cache
            .insert(fragment(id(8, 1), 0, &transported, true))
            .unwrap();
        let mut expected_payload = image_fields;
        if flags & 1 != 0 {
            expected_payload.extend(original_header);
            expected_payload.extend(color);
        } else {
            expected_payload.extend(equivalent_header);
            expected_payload.extend(&equivalent_payload);
        }
        expected.extend(box32(*b"jp2h", &expected_payload));
    }
    let codestream = box32(*b"jp2c", &decodable_codestream());
    root.extend_from_slice(&codestream);
    expected.extend(codestream);
    cache.insert(fragment(id(8, 0), 0, &root, true)).unwrap();
    cache
        .insert(fragment(id(8, 2), 0, &equivalent_payload, true))
        .unwrap();
    cache.insert(fragment(id(8, 3), 0, &color, true)).unwrap();
    crate::jp2::parse_and_inspect(&expected, &ResourceLimits::default()).unwrap();
    (cache, expected)
}

#[test]
fn semantic_equivalent_metadata_preserves_declared_representation() {
    let mut failures = Vec::new();
    for whole_header in [false, true] {
        for original_extended in [false, true] {
            for equivalent_extended in [false, true] {
                let (cache, expected) = equivalent_metadata_fixture(
                    whole_header,
                    original_extended,
                    equivalent_extended,
                    2,
                );
                let actual = cache.assemble_semantic_container(0);
                match actual {
                    Ok(assembled) => assert_eq!(
                        assembled.container().unwrap().as_bytes(),
                        expected,
                        "whole_header={whole_header} original_extended={original_extended} equivalent_extended={equivalent_extended}"
                    ),
                    Err(error) => failures.push(format!(
                        "whole_header={whole_header} original_extended={original_extended} equivalent_extended={equivalent_extended}: {error:?}"
                    )),
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn semantic_original_metadata_precedes_available_equivalent_representation() {
    for original_extended in [false, true] {
        for equivalent_extended in [false, true] {
            let (cache, expected) =
                equivalent_metadata_fixture(false, original_extended, equivalent_extended, 3);
            let actual = cache.assemble_semantic_container(0).unwrap();
            assert_eq!(actual.container().unwrap().as_bytes(), expected);
        }
    }
}

#[test]
fn placeholder_reconstruction_preserves_raw_precedence_and_header_owners() {
    use super::reconstruction::{PlaceholderSource, placeholder_reconstruction};
    use PlaceholderSource::{Codestream, Empty, Equivalent, Original};

    let sources = [
        Empty, Original, Equivalent, Original, Codestream, Original, Equivalent, Original,
    ];
    for original_length in [0, 1, 7, 8, 15, 16, 31] {
        let original = vec![0x17; original_length];
        for equivalent_length in [0, 1, 7, 8, 15, 16, 31] {
            let equivalent = vec![0xc3; equivalent_length];
            for (low_flags, expected_source) in sources.iter().copied().enumerate() {
                for upper_flags in [0, 8, 0x10000, 0x8000_0000] {
                    let flags = u32::try_from(low_flags).unwrap() | upper_flags;
                    let expected_header = if expected_source == Equivalent {
                        equivalent.as_slice()
                    } else {
                        original.as_slice()
                    };
                    let (source, header) =
                        placeholder_reconstruction(flags, &original, Some(&equivalent)).unwrap();
                    assert_eq!(source, expected_source);
                    assert_eq!(header, expected_header);
                    assert_eq!(header.as_ptr(), expected_header.as_ptr());
                    let missing = placeholder_reconstruction(flags, &original, None);
                    if expected_source == Equivalent {
                        assert_eq!(
                            missing,
                            Err(DecodeError::MalformedInput {
                                offset: 0,
                                kind: MalformedKind::InvalidBoxContents,
                            })
                        );
                    } else {
                        assert_eq!(missing, Ok((expected_source, original.as_slice())));
                    }
                }
            }
        }
    }
}

#[test]
fn tile_part_transition_status_distinguishes_sufficient_packet_boundaries() {
    let bytes = decodable_codestream_with_layers(2);
    let sot = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x90])
        .unwrap();
    let mut first = bytes[sot..sot + 12].to_vec();
    first[11] = 2;
    first.extend(segment(0xff58, &[0, 1]));
    first.extend_from_slice(&[0xff, 0x93]);
    let first_length = u32::try_from(first.len() + 1).unwrap();
    first[6..10].copy_from_slice(&first_length.to_be_bytes());
    let mut second = bytes[sot..sot + 12].to_vec();
    second[10] = 1;
    second[11] = 2;
    second.extend(segment(0xff52, &[0, 0, 0, 2, 0, 0, 0, 0, 0, 1]));
    second.extend_from_slice(&[0xff, 0x93]);
    let second_length = u32::try_from(second.len() + 1).unwrap();
    second[6..10].copy_from_slice(&second_length.to_be_bytes());
    let mut headers = first.clone();
    headers.extend(second.clone());

    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache.insert(fragment(id(2, 0), 0, &headers, true)).unwrap();
    let report = cache.tile_part_transitions(0, 0).unwrap();
    assert_eq!(report.status(), JpipAvailability::Available);
    assert_eq!(report.transitions().len(), 2);
    assert_eq!(report.transitions()[0].packet_count(), Some(1));
    assert!(report.transitions()[1].has_functional_change());

    let mut insufficient = first[..12].to_vec();
    insufficient.extend_from_slice(&[0xff, 0x93]);
    insufficient[6..10].copy_from_slice(&16_u32.to_be_bytes());
    insufficient.extend(second);
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache
        .insert(fragment(id(2, 0), 0, &insufficient, true))
        .unwrap();
    let report = cache.tile_part_transitions(0, 0).unwrap();
    assert_eq!(report.status(), JpipAvailability::Available);
    assert!(report.semantic_needs().is_empty());
    assert_eq!(report.transitions()[0].data_length(), Some(2));
}

#[test]
fn automatic_executes_functional_later_tile_part_without_plt() {
    let bytes = decodable_codestream_with_layers(2);
    let sot = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x90])
        .unwrap();
    let mut first = bytes[sot..sot + 12].to_vec();
    first[6..10].copy_from_slice(&15_u32.to_be_bytes());
    first[11] = 2;
    first.extend_from_slice(&[0xff, 0x93]);

    let cod = bytes
        .windows(2)
        .position(|value| value == [0xff, 0x52])
        .unwrap();
    let cod_length = usize::from(u16::from_be_bytes([bytes[cod + 2], bytes[cod + 3]]));
    let cod_end = cod + 2 + cod_length;
    let mut second = bytes[sot..sot + 12].to_vec();
    second[10] = 1;
    second[11] = 2;
    let second_length = 14 + cod_end - cod + 1;
    second[6..10].copy_from_slice(&(second_length as u32).to_be_bytes());
    second.extend_from_slice(&bytes[cod..cod_end]);
    second.extend_from_slice(&[0xff, 0x93]);

    let mut headers = first;
    headers.extend(second);
    let mut cache = DatabinCache::new(ResourceLimits::default());
    cache
        .insert(fragment(id(6, 0), 0, &bytes[..sot], true))
        .unwrap();
    cache.insert(fragment(id(2, 0), 0, &headers, true)).unwrap();
    cache.insert(fragment(id(0, 0), 0, &[0, 0], false)).unwrap();

    let report = cache.tile_part_transitions(0, 0).unwrap();
    assert_eq!(report.status(), JpipAvailability::Available);
    assert_eq!(report.transitions()[0].data_length(), Some(1));
    let mut decoder = JpipAutomaticProgressiveDecoder::new(0);
    let update = decoder
        .update(&cache, &crate::DecodeOptions::default())
        .unwrap();
    assert_eq!(update.status(), JpipProgressiveStatus::Complete);
    assert!(update.image().is_some());
}
