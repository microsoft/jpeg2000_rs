use super::*;

#[derive(Debug, Eq, PartialEq)]
struct FragmentFrame {
    offset: u64,
    bytes: Vec<u8>,
    storage: (usize, usize, usize),
}

#[derive(Debug, Eq, PartialEq)]
struct BinFrame {
    id: DatabinId,
    final_length: Option<u64>,
    fragments: Vec<FragmentFrame>,
    storage: (usize, usize, usize),
}

#[derive(Debug, Eq, PartialEq)]
pub(super) struct CacheFrame {
    limits: ResourceLimits,
    bins: Vec<BinFrame>,
    stored_bytes: u64,
    accepted_fragments: u64,
    storage: (usize, usize, usize),
}

pub(super) fn storage<T>(values: &Vec<T>) -> (usize, usize, usize) {
    (values.as_ptr() as usize, values.len(), values.capacity())
}

pub(super) fn frame(cache: &DatabinCache) -> CacheFrame {
    CacheFrame {
        limits: cache.limits,
        bins: cache
            .databins
            .iter()
            .map(|bin| BinFrame {
                id: bin.id,
                final_length: bin.final_length,
                fragments: bin
                    .fragments
                    .iter()
                    .map(|fragment| FragmentFrame {
                        offset: fragment.offset,
                        bytes: fragment.bytes.clone(),
                        storage: storage(&fragment.bytes),
                    })
                    .collect(),
                storage: storage(&bin.fragments),
            })
            .collect(),
        stored_bytes: cache.stored_bytes,
        accepted_fragments: cache.accepted_fragments,
        storage: storage(&cache.databins),
    }
}

pub(super) fn id(class: u64, stream: u64, bin: u64) -> DatabinId {
    DatabinId::from_wire(class, stream, bin).unwrap()
}

pub(super) fn class_key(class: u64) -> u64 {
    match class {
        1 => 0,
        5 => 4,
        _ => class,
    }
}

pub(super) fn bin(id: DatabinId, fragments: &[(u64, &[u8])], final_length: Option<u64>) -> Databin {
    Databin {
        id,
        fragments: fragments
            .iter()
            .map(|(offset, bytes)| StoredFragment {
                offset: *offset,
                bytes: bytes.to_vec(),
            })
            .collect(),
        final_length,
    }
}

fn cache(databins: Vec<Databin>, limit: u64) -> DatabinCache {
    DatabinCache {
        limits: ResourceLimits::HARDENED
            .with_maximum_input_bytes(limit)
            .unwrap(),
        databins,
        stored_bytes: u64::MAX,
        accepted_fragments: u64::MAX,
    }
}

fn invalid(offset: usize) -> DecodeError {
    DecodeError::malformed(offset as u64, MalformedKind::InvalidJpipLayout)
}

fn expected_read(cache: &DatabinCache, layout: &[DatabinId]) -> Result<Vec<u8>, DecodeError> {
    let mut bytes = Vec::new();
    for requested in layout {
        let Some(bin) = cache.databins.iter().find(|bin| {
            class_key(bin.id.class_identifier) == class_key(requested.class_identifier)
                && (requested.class_identifier == 8 || bin.id.codestream == requested.codestream)
                && bin.id.in_class == requested.in_class
        }) else {
            return Err(DecodeError::malformed(
                0,
                MalformedKind::MissingRequiredStructure,
            ));
        };
        let prefix = bin.fragments.iter().fold(0_u64, |prefix, fragment| {
            if fragment.offset == prefix {
                fragment.offset.saturating_add(fragment.bytes.len() as u64)
            } else {
                prefix
            }
        });
        if bin.final_length != Some(prefix) {
            return Err(DecodeError::malformed(
                prefix,
                MalformedKind::MissingRequiredStructure,
            ));
        }
        let part = bin
            .fragments
            .first()
            .map_or(&[][..], |fragment| fragment.bytes.as_slice());
        let total = (bytes.len() as u64)
            .checked_add(part.len() as u64)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        if total > cache.limits.maximum_input_bytes() {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                cache.limits.maximum_input_bytes(),
                total,
            ));
        }
        bytes.extend_from_slice(part);
    }
    Ok(bytes)
}

fn expected_codestream(cache: &DatabinCache, layout: &[DatabinId]) -> Result<Vec<u8>, DecodeError> {
    if layout.len() < 3 || layout.len().is_multiple_of(2) {
        return Err(invalid(layout.len()));
    }
    if layout[0].class != DatabinClass::MainHeader || layout[0].in_class != 0 {
        return Err(invalid(0));
    }
    for (index, pair) in layout[1..].chunks_exact(2).enumerate() {
        if pair[0].class != DatabinClass::TileHeader
            || pair[1].class != DatabinClass::TileData
            || pair[0].codestream != layout[0].codestream
            || pair[1].codestream != layout[0].codestream
            || pair[0].in_class != pair[1].in_class
        {
            return Err(invalid(1 + index * 2));
        }
    }
    let bytes = expected_read(cache, layout)?;
    if bytes.len() < 2 || bytes[0..2] != [0xff, 0x4f] || bytes[bytes.len() - 2..] != [0xff, 0xd9] {
        return Err(DecodeError::malformed(
            0,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    Ok(bytes)
}

fn expected_container(cache: &DatabinCache, layout: &[DatabinId]) -> Result<Vec<u8>, DecodeError> {
    if layout.is_empty() {
        return Err(invalid(0));
    }
    if let Some(index) = layout
        .iter()
        .position(|id| id.class != DatabinClass::Metadata)
    {
        return Err(invalid(index));
    }
    expected_read(cache, layout)
}

fn check(cache: &DatabinCache, layout: &[DatabinId]) {
    let before = frame(cache);
    let results = [
        cache.reconstruct_codestream(layout),
        cache.reconstruct_container(layout),
    ];
    let expected = [
        expected_codestream(cache, layout),
        expected_container(cache, layout),
    ];
    for (result, expected) in results.into_iter().zip(expected) {
        assert_eq!(
            result
                .as_ref()
                .map(|view| view.as_bytes())
                .map_err(|error| *error),
            expected.as_deref().map_err(|error| *error),
            "layout: {layout:?}"
        );
        if let Ok(view) = result {
            let mut bytes = view.into_bytes();
            if !bytes.is_empty() {
                for bin in &cache.databins {
                    for fragment in &bin.fragments {
                        assert_ne!(bytes.as_ptr(), fragment.bytes.as_ptr());
                    }
                }
                bytes[0] ^= 0xff;
            }
        }
    }
    assert_eq!(frame(cache), before);
}

#[test]
fn actual_jpip_layout_results_preserve_shape_classes_pair_order_and_error_precedence() {
    let state = cache(Vec::new(), 0);
    let ids: Vec<_> = (0..=8)
        .map(|class| id(class, 3, 0))
        .chain([id(6, 3, 1), id(2, 4, 0), id(4, 3, 1)])
        .collect();
    let mut cases = 0;
    for first in &ids {
        for header in &ids {
            for data in &ids {
                check(&state, &[*first, *header, *data]);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 1728);
    for layout in [
        vec![],
        vec![id(6, 3, 0)],
        vec![id(6, 3, 0), id(2, 3, 0)],
        vec![id(6, 3, 0), id(2, 3, 0), id(4, 3, 0), id(2, 3, 0)],
        vec![
            id(6, 3, 0),
            id(2, 3, 0),
            id(4, 3, 0),
            id(2, 4, 1),
            id(4, 3, 1),
        ],
        vec![id(8, 3, 0), id(8, 4, 1), id(6, 3, 0)],
    ] {
        check(&state, &layout);
    }
}

#[test]
fn actual_jpip_layout_results_derive_arbitrary_cache_bytes_limits_markers_and_native_frames() {
    let parts: [(u64, &[u8]); 4] = [
        (0, b""),
        (0, &[0xff, 0x4f]),
        (2, &[0xff, 0xd9]),
        (u64::MAX, b"x"),
    ];
    let mut cases = 0;
    for code in 0..65 {
        let fragments = if code == 64 {
            Vec::new()
        } else {
            vec![parts[code % 4], parts[code / 4 % 4], parts[code / 16 % 4]]
        };
        for final_length in [None, Some(0), Some(2), Some(4), Some(u64::MAX)] {
            for limit in [0, 1, 2, 4, 8] {
                let state = cache(
                    vec![
                        bin(id(6, 3, 0), &fragments, final_length),
                        bin(id(7, 3, 0), &[(0, b"later")], Some(5)),
                        bin(id(2, 3, 0), &[(0, b"")], Some(0)),
                        bin(id(4, 3, 0), &[(0, &[0xff, 0xd9])], Some(2)),
                        bin(id(8, 3, 0), &fragments, final_length),
                        bin(id(8, 4, 1), &[(0, b"abc")], Some(3)),
                    ],
                    limit,
                );
                for layout in [
                    vec![id(7, 3, 0), id(3, 3, 0), id(5, 3, 0)],
                    vec![
                        id(6, 3, 0),
                        id(2, 3, 0),
                        id(4, 3, 0),
                        id(3, 3, 0),
                        id(5, 3, 0),
                    ],
                    vec![id(8, 3, 0)],
                    vec![id(8, 4, 1), id(8, 3, 0), id(8, 4, 1)],
                    vec![id(8, 3, 0), id(8, 3, 9)],
                    vec![id(8, 3, 9), id(8, 4, 1)],
                ] {
                    check(&state, &layout);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 9750);
}

#[test]
fn actual_jpip_layout_results_compose_owned_insertion_and_keep_as_implemented_marker_admission() {
    let mut state = DatabinCache::new(ResourceLimits::HARDENED);
    for (databin, bytes) in [
        (id(6, 3, 0), &SOC[..]),
        (id(2, 3, 0), &[][..]),
        (id(4, 3, 0), &EOC[..]),
        (id(8, 4, 1), &b"not a JP2 box"[..]),
    ] {
        state
            .insert(
                JpipFragment::new(
                    databin,
                    0,
                    bytes.to_vec(),
                    true,
                    None,
                    &ResourceLimits::HARDENED,
                )
                .unwrap(),
            )
            .unwrap();
    }
    let layout = [id(6, 3, 0), id(2, 3, 0), id(5, 3, 0)];
    check(&state, &layout);
    assert_eq!(
        state.reconstruct_codestream(&layout).unwrap().as_bytes(),
        &[0xff, 0x4f, 0xff, 0xd9]
    );
    assert_eq!(
        state
            .reconstruct_container(&[id(8, 4, 1)])
            .unwrap()
            .as_bytes(),
        b"not a JP2 box"
    );
    for (main, data) in [
        (&b""[..], &b""[..]),
        (&b"x"[..], &EOC[..]),
        (&SOC[..], &b"x"[..]),
        (&b"\xff\x4fmore"[..], &b"more\xff\xd9"[..]),
    ] {
        let arbitrary = cache(
            vec![
                bin(id(6, 3, 0), &[(0, main)], Some(main.len() as u64)),
                bin(id(2, 3, 0), &[], Some(0)),
                bin(id(4, 3, 0), &[(0, data)], Some(data.len() as u64)),
            ],
            32,
        );
        check(&arbitrary, &layout);
    }
}
