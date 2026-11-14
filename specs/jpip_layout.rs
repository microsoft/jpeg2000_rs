//! Complete public JPIP reconstruction from physical cache and caller layout.

use super::*;

verus! {

pub struct Part2JpipPlaceholder {
    pub flags: u32,
    pub bin: u64,
    pub original_header: Seq<u8>,
    pub original_type: crate::jp2::BoxType,
    pub equivalent_bin: Option<u64>,
    pub equivalent_header: Option<Seq<u8>>,
    pub equivalent_type: Option<crate::jp2::BoxType>,
    pub stream: Option<u64>,
    pub stream_count: u32,
}

pub open spec fn part2_jpip_placeholder_header(
    input: Seq<u8>, position: usize,
) -> Result<(Seq<u8>, crate::jp2::BoxType, usize), crate::DecodeError> {
    match part2_jpip_read_u32(input, position) {
        Err(error) => Err(error),
        Ok(length) => {
            let size: nat = if length == 1 { 16 } else { 8 };
            let end = position as nat + size;
            if end > usize::MAX as nat {
                Err(part2_jpip_cache_error(0, crate::MalformedKind::ArithmeticOverflow))
            } else if end > input.len() {
                Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidBoxContents))
            } else {
                let header = input.subrange(position as int, end as int);
                Ok((header, crate::jp2::box_type_from_word_model(
                    ((header[4] as u32) << 24) | ((header[5] as u32) << 16)
                        | ((header[6] as u32) << 8) | header[7] as u32), end as usize))
            }
        },
    }
}

pub open spec fn part2_jpip_placeholder_equivalent(
    input: Seq<u8>, flags: u32, position: usize,
) -> Result<(Option<u64>, Option<Seq<u8>>, Option<crate::jp2::BoxType>, usize), crate::DecodeError> {
    if flags & 6 == 0 { Ok((None, None, None, position)) }
    else {
        match part2_jpip_read_u64(input, position) {
            Err(error) => Err(error),
            Ok(bin) => if position as nat + 8 > usize::MAX as nat {
                Err(part2_jpip_cache_error(0, crate::MalformedKind::ArithmeticOverflow))
            } else {
                match part2_jpip_placeholder_header(input, (position + 8) as usize) {
                    Err(error) => Err(error),
                    Ok(header) => Ok((Some(bin), Some(part2_jpip_copy_bytes(header.0)),
                        Some(header.1), header.2)),
                }
            },
        }
    }
}

pub open spec fn part2_jpip_placeholder_stream(
    input: Seq<u8>, flags: u32, position: usize,
) -> Result<(Option<u64>, u32, usize), crate::DecodeError> {
    if flags & 4 == 0 { Ok((None, 0, position)) }
    else {
        match part2_jpip_read_u64(input, position) {
            Err(error) => Err(error),
            Ok(stream) => if position as nat + 8 > usize::MAX as nat {
                Err(part2_jpip_cache_error(0, crate::MalformedKind::ArithmeticOverflow))
            } else {
                let after = (position + 8) as usize;
                if flags & 8 != 0 {
                    match part2_jpip_read_u32(input, after) {
                        Err(error) => Err(error),
                        Ok(count) => if after as nat + 4 > usize::MAX as nat {
                            Err(part2_jpip_cache_error(0, crate::MalformedKind::ArithmeticOverflow))
                        } else if count == 0 {
                            Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidBoxContents))
                        } else { Ok((Some(stream), count, (after + 4) as usize)) },
                    }
                } else if input.len() == after as nat + 4 {
                    match part2_jpip_read_u32(input, after) {
                        Err(error) => Err(error),
                        Ok(_) => if after as nat + 4 > usize::MAX as nat {
                            Err(part2_jpip_cache_error(0, crate::MalformedKind::ArithmeticOverflow))
                        } else { Ok((Some(stream), 1, (after + 4) as usize)) },
                    }
                } else { Ok((Some(stream), 1, after)) }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_parse_placeholder(input: Seq<u8>)
    -> Result<Part2JpipPlaceholder, crate::DecodeError> {
    if input.len() < 20 {
        Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidBoxContents))
    } else {
        match part2_jpip_read_u32(input, 0) {
            Err(error) => Err(error),
            Ok(flags) => match part2_jpip_read_u32(input, 4) {
                Err(error) => Err(error),
                Ok(high) => match part2_jpip_read_u32(input, 8) {
                    Err(error) => Err(error),
                    Ok(low) => match part2_jpip_placeholder_header(input, 12) {
                        Err(error) => Err(error),
                        Ok(original) => if flags & !0x0f != 0 || flags & 8 != 0 && flags & 4 == 0 {
                            Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidBoxContents))
                        } else {
                            match part2_jpip_placeholder_equivalent(input, flags, original.2) {
                                Err(error) => Err(error),
                                Ok(equivalent) => match part2_jpip_placeholder_stream(input, flags, equivalent.3) {
                                    Err(error) => Err(error),
                                    Ok(stream) => if stream.2 as nat != input.len() {
                                        Err(part2_jpip_cache_error(
                                            if flags == 4 && input.len() == original.2 as nat + 24 {
                                                original.2 as u64
                                            } else { 0 },
                                            crate::MalformedKind::InvalidBoxContents))
                                    } else {
                                        Ok(Part2JpipPlaceholder {
                                            flags, bin: ((high as u64) << 32) | low as u64,
                                            original_header: part2_jpip_copy_bytes(original.0),
                                            original_type: original.1,
                                            equivalent_bin: equivalent.0, equivalent_header: equivalent.1,
                                            equivalent_type: equivalent.2, stream: stream.0, stream_count: stream.1,
                                        })
                                    },
                                },
                            }
                        },
                    },
                },
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_placeholder_reconstruction(
    flags: u32, original: Seq<u8>, equivalent: Option<Seq<u8>>,
) -> Result<(u8, Seq<u8>), crate::DecodeError> {
    if flags & 1 != 0 { Ok((0, original)) }
    else if flags & 2 != 0 {
        match equivalent {
            Some(header) => Ok((1, header)),
            None => Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidBoxContents)),
        }
    } else if flags & 4 != 0 { Ok((2, original)) }
    else { Ok((3, original)) }
}

pub open spec fn part2_jpip_layout_error(offset: u64) -> crate::DecodeError {
    part2_jpip_cache_error(offset, crate::MalformedKind::InvalidJpipLayout)
}

#[verifier::opaque]
pub open spec fn part2_jpip_codestream_pairs(
    layout: Seq<Part2JpipDatabin>, position: nat,
) -> Result<(), crate::DecodeError>
    decreases if position < layout.len() { layout.len() - position } else { 0 },
{
    if position >= layout.len() { Ok(()) }
    else if position + 1 > usize::MAX as nat {
        Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::ArithmeticOverflow))
    } else if position + 1 >= layout.len() {
        Err(part2_jpip_layout_error((position + 1) as u64))
    } else {
        let header = layout[position as int];
        let data = layout[(position + 1) as int];
        if header.1 != crate::jpip::DatabinClass::TileHeader
            || data.1 != crate::jpip::DatabinClass::TileData
            || header.2 != layout[0].2 || data.2 != layout[0].2
            || header.3 != data.3 {
            Err(part2_jpip_layout_error(position as u64))
        } else { part2_jpip_codestream_pairs(layout, position + 2) }
    }
}

pub open spec fn part2_jpip_codestream_markers(bytes: Seq<u8>) -> bool {
    bytes.len() >= 2 && bytes[0] == 0xff && bytes[1] == 0x4f
        && bytes[bytes.len() - 2] == 0xff && bytes[bytes.len() - 1] == 0xd9
}

pub open spec fn part2_jpip_cache_codestream(
    cache: Part2JpipCache, layout: Seq<Part2JpipDatabin>,
) -> Result<Seq<u8>, crate::DecodeError> {
    if layout.len() < 3 || layout.len() % 2 == 0 {
        Err(part2_jpip_layout_error(layout.len() as u64))
    } else if layout[0].1 != crate::jpip::DatabinClass::MainHeader || layout[0].3 != 0 {
        Err(part2_jpip_layout_error(0))
    } else {
        match part2_jpip_codestream_pairs(layout, 1) {
            Err(error) => Err(error),
            Ok(()) => match part2_jpip_cache_reconstruct(cache, layout) {
                Err(error) => Err(error),
                Ok(bytes) => if part2_jpip_codestream_markers(bytes) { Ok(bytes) }
                    else { Err(part2_jpip_cache_error(0, crate::MalformedKind::MissingRequiredStructure)) },
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_metadata_layout(
    layout: Seq<Part2JpipDatabin>, position: nat,
) -> Result<(), crate::DecodeError>
    decreases if position < layout.len() { layout.len() - position } else { 0 },
{
    if position >= layout.len() { Ok(()) }
    else if layout[position as int].1 != crate::jpip::DatabinClass::Metadata {
        Err(part2_jpip_layout_error(position as u64))
    } else { part2_jpip_metadata_layout(layout, position + 1) }
}

pub open spec fn part2_jpip_cache_container(
    cache: Part2JpipCache, layout: Seq<Part2JpipDatabin>,
) -> Result<Seq<u8>, crate::DecodeError> {
    if layout.len() == 0 { Err(part2_jpip_layout_error(0)) }
    else {
        match part2_jpip_metadata_layout(layout, 0) {
            Err(error) => Err(error),
            Ok(()) => part2_jpip_cache_reconstruct(cache, layout),
        }
    }
}

pub open spec fn part2_jpip_write_u64(
    before: Seq<u8>, position: usize, value: u64,
) -> (Result<(), crate::DecodeError>, Seq<u8>) {
    let high = part2_jpip_write_u32(before, position, (value >> 32) as u32);
    match high.0 {
        Err(error) => (Err(error), high.1),
        Ok(()) => if position as nat + 4 > usize::MAX as nat {
            (Err(part2_jpip_range_overflow(0)), high.1)
        } else { part2_jpip_write_u32(high.1, (position as nat + 4) as usize, (value & 0xffffffff) as u32) },
    }
}

pub open spec fn part2_jpip_superbox(value: crate::jp2::BoxType) -> bool {
    value == crate::jp2::box_type_from_bytes_model(*b"jp2h")
        || value == crate::jp2::box_type_from_bytes_model(*b"jpch")
        || value == crate::jp2::box_type_from_bytes_model(*b"jplh")
        || value == crate::jp2::box_type_from_bytes_model(*b"cgrp")
        || value == crate::jp2::box_type_from_bytes_model(*b"res ")
        || value == crate::jp2::box_type_from_bytes_model(*b"asoc")
        || value == crate::jp2::box_type_from_bytes_model(*b"comp")
}

pub open spec fn part2_jpip_append_reconstructed_box(
    before: Seq<u8>, original: Seq<u8>, payload: Seq<u8>,
) -> (Result<(), crate::DecodeError>, Seq<u8>) {
    if original.len() != 8 && original.len() != 16 {
        (Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidBoxContents)), before)
    } else if original.len() + payload.len() > usize::MAX as nat {
        (Err(part2_jpip_range_overflow(0)), before)
    } else {
        let total = original.len() + payload.len();
        if original.len() == 8 && total > u32::MAX as nat {
            (Err(part2_jpip_range_overflow(0)), before)
        } else {
            let first = part2_jpip_write_u32(original, 0, if original.len() == 8 { total as u32 } else { 1 });
            let patched = if original.len() == 8 { first }
                else { match first.0 {
                    Err(error) => (Err(error), first.1),
                    Ok(()) => part2_jpip_write_u64(first.1, 8, total as u64),
                } };
            match patched.0 {
                Err(error) => (Err(error), before),
                Ok(()) => (Ok(()), before + patched.1 + payload),
            }
        }
    }
}

pub struct Part2JpipSemanticState {
    pub active: Seq<u64>,
    pub output: Seq<u8>,
    pub missing: Seq<Part2JpipMissing>,
    pub needs: Seq<Part2JpipSemanticNeed>,
}

pub struct Part2JpipSemanticRoot {
    pub cache: Part2JpipCache,
    pub metadata_stream: u64,
    pub bin: u64,
    pub boxes: bool,
    pub depth: u32,
    pub remaining_depth: u32,
    pub before: Part2JpipSemanticState,
}

pub struct Part2JpipSemanticStreamPoint {
    pub cache: Part2JpipCache,
    pub first: u64,
    pub count: u32,
    pub index: u32,
    pub header: Seq<u8>,
    pub complete: bool,
    pub payload: Seq<u8>,
    pub state: Part2JpipSemanticState,
}

pub enum Part2JpipSemanticEvent {
    Snapshot { stream: u64, events: Seq<Part2JpipSnapshotEvent> },
}

pub type Part2JpipSemanticRun<T> =
    Option<(Result<T, crate::DecodeError>, Part2JpipSemanticState, Seq<Part2JpipSemanticEvent>)>;

pub open spec fn part2_jpip_semantic_lift<T>(
    result: Result<T, crate::DecodeError>, state: Part2JpipSemanticState, events: Seq<Part2JpipSemanticEvent>,
) -> Part2JpipSemanticRun<T> { Some((result, state, events)) }

pub open spec fn part2_jpip_semantic_metadata_length(
    cache: Part2JpipCache, stream: u64, bin: u64,
) -> nat {
    match part2_jpip_cache_view(cache, (8, crate::jpip::DatabinClass::Metadata, stream, bin)) {
        Err(_) => 0, Ok(bytes) => bytes.len(),
    }
}

pub(crate) open spec fn part2_jpip_semantic_snapshot(
    cache: Part2JpipCache, stream: u64, state: Part2JpipSemanticState, events: Seq<Part2JpipSemanticEvent>,
) -> Part2JpipSemanticRun<Part2JpipAutomaticSnapshotResult> {
    if events.len() == 0 { None } else { match events[0] {
        Part2JpipSemanticEvent::Snapshot { stream: actual, events: calls } =>
            if actual != stream { None } else {
                match part2_jpip_snapshot_run(Part2JpipSnapshotInput {
                    cache, stream, selected: None, components: Seq::empty(), limits: &cache.0 }, calls) {
                    Some((result, tail)) => if tail.len() == 0 {
                        part2_jpip_semantic_lift(result, state, events.drop_first())
                    } else { None },
                    None => None,
                }
            },
    } }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_semantic_streams(
    cache: Part2JpipCache, first: u64, count: u32, index: u32, header: Seq<u8>,
    complete: bool, payload: Seq<u8>, state: Part2JpipSemanticState, events: Seq<Part2JpipSemanticEvent>,
) -> Part2JpipSemanticRun<(bool, Seq<u8>)>
    decreases count as int - index as int,
{
    if index >= count { part2_jpip_semantic_lift(Ok((complete, payload)), state, events) }
    else if first as nat + index as nat > u64::MAX as nat {
        part2_jpip_semantic_lift(Err(part2_jpip_range_overflow(0)), state, events)
    } else {
        let stream = (first as nat + index as nat) as u64;
        match part2_jpip_semantic_snapshot(cache, stream, state, events) {
            None => None,
            Some((Err(error), state, tail)) => part2_jpip_semantic_lift(Err(error), state, tail),
            Some((Ok(snapshot), state, tail)) => match snapshot.0 {
                Some(ready) => if ready.1 == ready.2 {
                    if count == 1 {
                        part2_jpip_semantic_streams(cache, first, count, (index + 1) as u32, header,
                            complete, payload + ready.0, state, tail)
                    } else {
                        let appended = part2_jpip_append_reconstructed_box(state.output, header, ready.0);
                        let state = Part2JpipSemanticState { output: appended.1, ..state };
                        match appended.0 {
                            Err(error) => part2_jpip_semantic_lift(Err(error), state, tail),
                            Ok(()) => part2_jpip_semantic_streams(cache, first, count, (index + 1) as u32,
                                header, complete, payload, state, tail),
                        }
                    }
                } else {
                    part2_jpip_semantic_streams(cache, first, count, (index + 1) as u32, header, false, payload,
                        Part2JpipSemanticState { missing: state.missing + ready.3,
                            needs: state.needs.push((crate::jpip::JpipSemanticNeedKind::Codestream, stream)), ..state }, tail)
                },
                None => part2_jpip_semantic_streams(cache, first, count, (index + 1) as u32, header, false, payload,
                    Part2JpipSemanticState { missing: state.missing + snapshot.1,
                        needs: state.needs.push((crate::jpip::JpipSemanticNeedKind::Codestream, stream)), ..state }, tail),
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_semantic_placeholder(
    cache: Part2JpipCache, metadata_stream: u64, payload: Seq<u8>, depth: u32, remaining_depth: u32,
    state: Part2JpipSemanticState, events: Seq<Part2JpipSemanticEvent>,
) -> Part2JpipSemanticRun<(bool, bool, Seq<u8>, Seq<u8>)>
    decreases remaining_depth as nat, 0nat,
{
    match part2_jpip_parse_placeholder(payload) {
        Err(error) => part2_jpip_semantic_lift(Err(error), state, events),
        Ok(placeholder) => match part2_jpip_placeholder_reconstruction(
            placeholder.flags, placeholder.original_header, placeholder.equivalent_header) {
            Err(error) => part2_jpip_semantic_lift(Err(error), state, events),
            Ok((source, header)) => if source == 0 || source == 1 {
                let target = if source == 0 { Some((placeholder.bin, placeholder.original_type)) }
                    else { match placeholder.equivalent_bin {
                        None => None, Some(bin) => match placeholder.equivalent_type { None => None, Some(kind) => Some((bin, kind)) },
                    } };
                match target {
                    None => part2_jpip_semantic_lift(Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidBoxContents)), state, events),
                    Some((bin, kind)) => if depth == u32::MAX || remaining_depth == 0 {
                        part2_jpip_semantic_lift(Err(part2_jpip_range_overflow(0)), state, events)
                    } else {
                        let original_output = state.output;
                        match part2_jpip_semantic_expand(cache, metadata_stream, bin, part2_jpip_superbox(kind),
                            (depth + 1) as u32, (remaining_depth - 1) as u32,
                            Part2JpipSemanticState { output: Seq::empty(), ..state }, events) {
                            None => None,
                            Some((result, child, tail)) => {
                                let payload = child.output;
                                let state = Part2JpipSemanticState { output: original_output, ..child };
                                match result {
                                    Err(error) => part2_jpip_semantic_lift(Err(error), state, tail),
                                    Ok(complete) => part2_jpip_semantic_lift(Ok((complete, false, header, payload)), state, tail),
                                }
                            },
                        }
                    },
                }
            } else if source == 2 {
                match placeholder.stream {
                    None => part2_jpip_semantic_lift(Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidBoxContents)), state, events),
                    Some(first) => match part2_jpip_semantic_streams(cache, first, placeholder.stream_count, 0, header,
                        true, Seq::empty(), state, events) {
                        None => None,
                        Some((Err(error), state, tail)) => part2_jpip_semantic_lift(Err(error), state, tail),
                        Some((Ok((complete, payload)), state, tail)) => part2_jpip_semantic_lift(
                            Ok((complete, placeholder.stream_count > 1 && complete, header, payload)), state, tail),
                    },
                }
            } else { part2_jpip_semantic_lift(Ok((true, false, header, Seq::empty())), state, events) },
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_semantic_boxes(
    cache: Part2JpipCache, metadata_stream: u64, bin: u64, depth: u32, remaining_depth: u32,
    reader: Part2BoxReaderState, remaining_boxes: nat, complete: bool,
    state: Part2JpipSemanticState, events: Seq<Part2JpipSemanticEvent>,
) -> Part2JpipSemanticRun<bool>
    decreases remaining_depth as nat, remaining_boxes,
{
    let next = part2_box_reader_next_ref(reader);
    match next.0 {
        None => part2_jpip_semantic_lift(Ok(complete),
            Part2JpipSemanticState { active: state.active.drop_last(), ..state }, events),
        Some(item) => if remaining_boxes == 0 {
            part2_jpip_semantic_lift(Err(part2_jpip_cache_error(bin, crate::MalformedKind::InvalidBoxLength)), state, events)
        } else { match item {
            Err(error) => part2_jpip_semantic_lift(Err(error), state, events),
            Ok(reference) => if reference.0.0 == crate::jp2::box_type_from_bytes_model(*b"phld") {
                match part2_jpip_semantic_placeholder(cache, metadata_stream, reference.1, depth, remaining_depth, state, events) {
                    None => None,
                    Some((Err(error), state, tail)) => part2_jpip_semantic_lift(Err(error), state, tail),
                    Some((Ok((replacement, appended, header, payload)), state, tail)) => {
                        if replacement && !appended {
                            let step = part2_jpip_append_reconstructed_box(state.output, header, payload);
                            let state = Part2JpipSemanticState { output: step.1, ..state };
                            match step.0 {
                                Err(error) => part2_jpip_semantic_lift(Err(error), state, tail),
                                Ok(()) => part2_jpip_semantic_boxes(cache, metadata_stream, bin, depth, remaining_depth,
                                    next.1, (remaining_boxes - 1) as nat, complete, state, tail),
                            }
                        } else { part2_jpip_semantic_boxes(cache, metadata_stream, bin, depth, remaining_depth,
                            next.1, (remaining_boxes - 1) as nat, complete && replacement, state, tail) }
                    },
                }
            } else {
                let start = reference.0.1;
                let length = reference.0.3;
                if start > usize::MAX as u64 || length > usize::MAX as u64 || start as nat + length as nat > usize::MAX as nat {
                    part2_jpip_semantic_lift(Err(part2_jpip_range_overflow(0)), state, events)
                } else if start as nat + length as nat > reader.input.len() {
                    part2_jpip_semantic_lift(Err(part2_jpip_cache_error(start, crate::MalformedKind::Truncated)), state, events)
                } else {
                    part2_jpip_semantic_boxes(cache, metadata_stream, bin, depth, remaining_depth, next.1,
                        (remaining_boxes - 1) as nat, complete,
                        Part2JpipSemanticState { output: state.output + reader.input.subrange(
                            start as int, (start as nat + length as nat) as int), ..state }, events)
                }
            },
        } },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_semantic_expand(
    cache: Part2JpipCache, metadata_stream: u64, bin: u64, boxes: bool, depth: u32, remaining_depth: u32,
    state: Part2JpipSemanticState, events: Seq<Part2JpipSemanticEvent>,
) -> Part2JpipSemanticRun<bool>
    decreases remaining_depth as nat, part2_jpip_semantic_metadata_length(cache, metadata_stream, bin) + 1,
{
    if depth > crate::limits::resource_box_depth_limit(&cache.0) {
        part2_jpip_semantic_lift(Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::BoxDepth,
            limit: crate::limits::resource_box_depth_limit(&cache.0) as u64, actual: depth as u64 }), state, events)
    } else if state.active.contains(bin) {
        part2_jpip_semantic_lift(Err(part2_jpip_cache_error(bin, crate::MalformedKind::InvalidBoxContents)), state, events)
    } else {
        let id = (8u64, crate::jpip::DatabinClass::Metadata, metadata_stream, bin);
        if !part2_jpip_cache_complete(cache, id) {
            part2_jpip_semantic_lift(Ok(false), Part2JpipSemanticState {
                missing: state.missing + part2_jpip_complete_missing(cache, id),
                needs: state.needs.push((crate::jpip::JpipSemanticNeedKind::MetadataBin, bin)), ..state }, events)
        } else {
            match part2_jpip_cache_view(cache, id) {
                Err(error) => part2_jpip_semantic_lift(Err(error), state, events),
                Ok(bytes) => if !boxes {
                    part2_jpip_semantic_lift(Ok(true), Part2JpipSemanticState { output: state.output + bytes, ..state }, events)
                } else {
                    let state = Part2JpipSemanticState { active: state.active.push(bin), ..state };
                    match part2_box_reader_from_input(bytes, cache.0) {
                        Err(error) => part2_jpip_semantic_lift(Err(error), state, events),
                        Ok(reader) => part2_jpip_semantic_boxes(cache, metadata_stream, bin, depth, remaining_depth,
                            reader, bytes.len(), true, state, events),
                    }
                },
            }
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_semantic_expand_result(
    cache: Part2JpipCache, metadata_stream: u64, bin: u64, boxes: bool, depth: u32, remaining_depth: u32,
    before: Part2JpipSemanticState, result: Result<bool, crate::DecodeError>, after: Part2JpipSemanticState,
) -> bool {
    exists|events: Seq<Part2JpipSemanticEvent>| part2_jpip_semantic_expand(
        cache, metadata_stream, bin, boxes, depth, remaining_depth, before, events)
        == Some((result, after, Seq::empty()))
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_semantic_expand_prefix(
    cache: Part2JpipCache, metadata_stream: u64, bin: u64, boxes: bool, depth: u32, remaining_depth: u32,
    before: Part2JpipSemanticState, result: Result<bool, crate::DecodeError>, after: Part2JpipSemanticState,
    events: Seq<Part2JpipSemanticEvent>,
) -> bool {
    forall|tail: Seq<Part2JpipSemanticEvent>|
        #[trigger] part2_jpip_semantic_expand(cache, metadata_stream, bin, boxes, depth, remaining_depth,
            before, events + tail) == Some((result, after, tail))
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_semantic_expand_trace(
    cache: Part2JpipCache, metadata_stream: u64, bin: u64, boxes: bool, depth: u32, remaining_depth: u32,
    before: Part2JpipSemanticState, result: Result<bool, crate::DecodeError>, after: Part2JpipSemanticState,
) -> bool {
    exists|events: Seq<Part2JpipSemanticEvent>| #[trigger] part2_jpip_semantic_expand_prefix(
        cache, metadata_stream, bin, boxes, depth, remaining_depth, before, result, after, events)
}

pub(crate) open spec fn part2_jpip_semantic_placeholder_error_continuation(
    cache: Part2JpipCache, metadata_stream: u64, bin: u64, boxes: bool, depth: u32, remaining_depth: u32,
    before: Part2JpipSemanticState, prefix: Seq<Part2JpipSemanticEvent>, payload: Seq<u8>, state: Part2JpipSemanticState,
) -> bool {
    forall|events: Seq<Part2JpipSemanticEvent>|
        match #[trigger] part2_jpip_semantic_placeholder(cache, metadata_stream, payload, depth, remaining_depth, state, events) {
            Some((Err(error), after, tail)) => part2_jpip_semantic_expand(
                cache, metadata_stream, bin, boxes, depth, remaining_depth, before, prefix + events)
                == Some((Err(error), after, tail)),
            _ => true,
        }
}

pub(crate) proof fn part2_jpip_semantic_box_bounds(
    reader: Part2BoxReaderState, reference: Part2BoxReference,
)
    requires part2_box_reader_next_ref(reader).0 == Some(Ok(reference)),
    ensures reference.0.1 as nat <= usize::MAX as nat,
        reference.0.3 as nat <= usize::MAX as nat,
        reference.0.1 as nat + reference.0.3 as nat <= usize::MAX as nat,
        reference.0.1 as nat + reference.0.3 as nat <= reader.input.len(),
{
    reveal(part2_box_reader_next);
    reveal(part2_box_reader_after_work);
    reveal(part2_box_reader_after_header);
}

pub(crate) proof fn part2_jpip_semantic_reader_frame(reader: Part2BoxReaderState)
    ensures part2_box_reader_next_ref(reader).1.input == reader.input,
        part2_box_reader_next_ref(reader).1.limits == reader.limits,
{
    reveal(part2_box_reader_next);
    reveal(part2_box_reader_after_work);
    reveal(part2_box_reader_after_header);
}

pub(crate) proof fn part2_jpip_semantic_placeholder_box_step(
    cache: Part2JpipCache, metadata_stream: u64, bin: u64, depth: u32, remaining_depth: u32,
    reader: Part2BoxReaderState, remaining_boxes: nat, complete: bool,
    state: Part2JpipSemanticState, reference: Part2BoxReference,
)
    requires part2_box_reader_next_ref(reader).0 == Some(Ok(reference)), remaining_boxes > 0,
        reference.0.0 == crate::jp2::box_type_from_bytes_model(*b"phld"),
    ensures forall|events: Seq<Part2JpipSemanticEvent>|
        #[trigger] part2_jpip_semantic_boxes(cache, metadata_stream, bin, depth, remaining_depth,
            reader, remaining_boxes, complete, state, events)
            == match part2_jpip_semantic_placeholder(cache, metadata_stream, reference.1, depth, remaining_depth, state, events) {
                None => None,
                Some((Err(error), after, tail)) => part2_jpip_semantic_lift(Err(error), after, tail),
                Some((Ok((replacement, appended, header, payload)), after, tail)) =>
                    if replacement && !appended {
                        let step = part2_jpip_append_reconstructed_box(after.output, header, payload);
                        let after = Part2JpipSemanticState { output: step.1, ..after };
                        match step.0 {
                            Err(error) => part2_jpip_semantic_lift(Err(error), after, tail),
                            Ok(()) => part2_jpip_semantic_boxes(cache, metadata_stream, bin, depth, remaining_depth,
                                part2_box_reader_next_ref(reader).1, (remaining_boxes - 1) as nat, complete, after, tail),
                        }
                    } else { part2_jpip_semantic_boxes(cache, metadata_stream, bin, depth, remaining_depth,
                        part2_box_reader_next_ref(reader).1, (remaining_boxes - 1) as nat, complete && replacement, after, tail) },
            },
{
    reveal_with_fuel(part2_jpip_semantic_boxes, 2);
    reveal_with_fuel(part2_jpip_semantic_placeholder, 2);
}

pub(crate) proof fn part2_jpip_semantic_original_error_prefix(
    cache: Part2JpipCache, metadata_stream: u64, payload: Seq<u8>, placeholder: Part2JpipPlaceholder,
    header: Seq<u8>, depth: u32, remaining_depth: u32, before: Part2JpipSemanticState,
    error: crate::DecodeError, child: Part2JpipSemanticState, events: Seq<Part2JpipSemanticEvent>,
)
    requires part2_jpip_parse_placeholder(payload) == Ok(placeholder),
        part2_jpip_placeholder_reconstruction(placeholder.flags, placeholder.original_header, placeholder.equivalent_header)
            == Ok((0u8, header)),
        depth < u32::MAX, remaining_depth > 0,
        part2_jpip_semantic_expand_prefix(cache, metadata_stream, placeholder.bin,
            part2_jpip_superbox(placeholder.original_type), (depth + 1) as u32, (remaining_depth - 1) as u32,
            Part2JpipSemanticState { output: Seq::empty(), ..before }, Err(error), child, events),
    ensures forall|tail: Seq<Part2JpipSemanticEvent>|
        #[trigger] part2_jpip_semantic_placeholder(cache, metadata_stream, payload, depth, remaining_depth, before, events + tail)
            == Some((Err(error), Part2JpipSemanticState { output: before.output, ..child }, tail)),
{
    reveal(part2_jpip_semantic_expand_prefix);
    reveal_with_fuel(part2_jpip_semantic_placeholder, 2);
    reveal_with_fuel(part2_jpip_semantic_expand, 2);
    assert forall|tail: Seq<Part2JpipSemanticEvent>|
        part2_jpip_semantic_placeholder(cache, metadata_stream, payload, depth, remaining_depth, before, events + tail)
            == Some((Err(error), Part2JpipSemanticState { output: before.output, ..child }, tail)) by {
        assert(part2_jpip_semantic_expand(cache, metadata_stream, placeholder.bin,
            part2_jpip_superbox(placeholder.original_type), (depth + 1) as u32, (remaining_depth - 1) as u32,
            Part2JpipSemanticState { output: Seq::empty(), ..before }, events + tail) == Some((Err(error), child, tail)));
    }
}

pub(crate) proof fn part2_jpip_semantic_placeholder_fields(input: Seq<u8>, value: Part2JpipPlaceholder)
    requires part2_jpip_parse_placeholder(input) == Ok(value),
    ensures value.flags & 2 != 0 ==> value.equivalent_bin.is_some() && value.equivalent_type.is_some(),
        value.flags & 4 != 0 ==> value.stream.is_some() && value.stream_count > 0,
{
    reveal(part2_jpip_parse_placeholder);
    let flags = value.flags;
    assert(flags & 2 != 0 ==> flags & 6 != 0) by (bit_vector);
}

pub(crate) proof fn part2_jpip_semantic_original_success_prefix(
    cache: Part2JpipCache, metadata_stream: u64, payload: Seq<u8>, placeholder: Part2JpipPlaceholder,
    header: Seq<u8>, depth: u32, remaining_depth: u32, before: Part2JpipSemanticState,
    complete: bool, child: Part2JpipSemanticState, events: Seq<Part2JpipSemanticEvent>,
)
    requires part2_jpip_parse_placeholder(payload) == Ok(placeholder),
        part2_jpip_placeholder_reconstruction(placeholder.flags, placeholder.original_header, placeholder.equivalent_header)
            == Ok((0u8, header)),
        depth < u32::MAX, remaining_depth > 0,
        part2_jpip_semantic_expand_prefix(cache, metadata_stream, placeholder.bin,
            part2_jpip_superbox(placeholder.original_type), (depth + 1) as u32, (remaining_depth - 1) as u32,
            Part2JpipSemanticState { output: Seq::empty(), ..before }, Ok(complete), child, events),
    ensures forall|tail: Seq<Part2JpipSemanticEvent>|
        #[trigger] part2_jpip_semantic_placeholder(cache, metadata_stream, payload, depth, remaining_depth, before, events + tail)
            == Some((Ok((complete, false, header, child.output)), Part2JpipSemanticState { output: before.output, ..child }, tail)),
{
    reveal(part2_jpip_semantic_expand_prefix);
    reveal_with_fuel(part2_jpip_semantic_placeholder, 2);
    reveal_with_fuel(part2_jpip_semantic_expand, 2);
    assert forall|tail: Seq<Part2JpipSemanticEvent>|
        part2_jpip_semantic_placeholder(cache, metadata_stream, payload, depth, remaining_depth, before, events + tail)
            == Some((Ok((complete, false, header, child.output)), Part2JpipSemanticState { output: before.output, ..child }, tail)) by {
        assert(part2_jpip_semantic_expand(cache, metadata_stream, placeholder.bin,
            part2_jpip_superbox(placeholder.original_type), (depth + 1) as u32, (remaining_depth - 1) as u32,
            Part2JpipSemanticState { output: Seq::empty(), ..before }, events + tail) == Some((Ok(complete), child, tail)));
    }
}

pub(crate) proof fn part2_jpip_semantic_equivalent_prefix(
    cache: Part2JpipCache, metadata_stream: u64, payload: Seq<u8>, placeholder: Part2JpipPlaceholder,
    header: Seq<u8>, bin: u64, kind: crate::jp2::BoxType, depth: u32, remaining_depth: u32, before: Part2JpipSemanticState,
    result: Result<bool, crate::DecodeError>, child: Part2JpipSemanticState, events: Seq<Part2JpipSemanticEvent>,
)
    requires part2_jpip_parse_placeholder(payload) == Ok(placeholder),
        part2_jpip_placeholder_reconstruction(placeholder.flags, placeholder.original_header, placeholder.equivalent_header)
            == Ok((1u8, header)), placeholder.equivalent_bin == Some(bin), placeholder.equivalent_type == Some(kind),
        depth < u32::MAX, remaining_depth > 0,
        part2_jpip_semantic_expand_prefix(cache, metadata_stream, bin,
            part2_jpip_superbox(kind), (depth + 1) as u32, (remaining_depth - 1) as u32,
            Part2JpipSemanticState { output: Seq::empty(), ..before }, result, child, events),
    ensures forall|tail: Seq<Part2JpipSemanticEvent>|
        #[trigger] part2_jpip_semantic_placeholder(cache, metadata_stream, payload, depth, remaining_depth, before, events + tail)
            == Some((match result { Err(error) => Err(error), Ok(complete) => Ok((complete, false, header, child.output)) },
                Part2JpipSemanticState { output: before.output, ..child }, tail)),
{
    reveal(part2_jpip_semantic_expand_prefix);
    reveal_with_fuel(part2_jpip_semantic_placeholder, 2);
    reveal_with_fuel(part2_jpip_semantic_expand, 2);
    assert forall|tail: Seq<Part2JpipSemanticEvent>|
        part2_jpip_semantic_placeholder(cache, metadata_stream, payload, depth, remaining_depth, before, events + tail)
            == Some((match result { Err(error) => Err(error), Ok(complete) => Ok((complete, false, header, child.output)) },
                Part2JpipSemanticState { output: before.output, ..child }, tail)) by {
        assert(part2_jpip_semantic_expand(cache, metadata_stream, bin,
            part2_jpip_superbox(kind), (depth + 1) as u32, (remaining_depth - 1) as u32,
            Part2JpipSemanticState { output: Seq::empty(), ..before }, events + tail) == Some((result, child, tail)));
    }
}

pub(crate) open spec fn part2_jpip_semantic_placeholder_streams_known(
    cache: Part2JpipCache, metadata_stream: u64, payload: Seq<u8>, depth: u32, remaining_depth: u32,
    state: Part2JpipSemanticState, first: u64, count: u32, header: Seq<u8>,
) -> bool {
    forall|events: Seq<Part2JpipSemanticEvent>|
        #[trigger] part2_jpip_semantic_placeholder(cache, metadata_stream, payload, depth, remaining_depth, state, events)
            == match part2_jpip_semantic_streams(cache, first, count, 0, header, true, Seq::empty(), state, events) {
                None => None,
                Some((Err(error), after, tail)) => part2_jpip_semantic_lift(Err(error), after, tail),
                Some((Ok((complete, bytes)), after, tail)) => part2_jpip_semantic_lift(
                    Ok((complete, count > 1 && complete, header, bytes)), after, tail),
            }
}

pub(crate) open spec fn part2_jpip_semantic_stream_at(
    point: Part2JpipSemanticStreamPoint, events: Seq<Part2JpipSemanticEvent>,
) -> Part2JpipSemanticRun<(bool, Seq<u8>)> {
    part2_jpip_semantic_streams(point.cache, point.first, point.count, point.index,
        point.header, point.complete, point.payload, point.state, events)
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_semantic_stream_error_continuation(
    root: Part2JpipSemanticRoot, prefix: Seq<Part2JpipSemanticEvent>, point: Part2JpipSemanticStreamPoint,
) -> bool {
    forall|events: Seq<Part2JpipSemanticEvent>|
        match #[trigger] part2_jpip_semantic_stream_at(point, events) {
            Some((Err(error), after, tail)) => part2_jpip_semantic_expand(root.cache, root.metadata_stream,
                root.bin, root.boxes, root.depth, root.remaining_depth, root.before, prefix + events)
                == Some((Err(error), after, tail)),
            _ => true,
        }
}

pub(crate) proof fn part2_jpip_semantic_stream_continuation(
    root: Part2JpipSemanticRoot, parent: Seq<Part2JpipSemanticEvent>, payload: Seq<u8>,
    state: Part2JpipSemanticState, prefix: Seq<Part2JpipSemanticEvent>, point: Part2JpipSemanticStreamPoint,
)
    requires point.cache == root.cache,
        part2_jpip_semantic_placeholder_error_continuation(root.cache, root.metadata_stream, root.bin, root.boxes,
            root.depth, root.remaining_depth, root.before, parent, payload, state),
        part2_jpip_semantic_placeholder_streams_known(root.cache, root.metadata_stream, payload,
            root.depth, root.remaining_depth, state, point.first, point.count, point.header),
        forall|tail: Seq<Part2JpipSemanticEvent>|
            part2_jpip_semantic_streams(point.cache, point.first, point.count, 0,
                point.header, true, Seq::empty(), state, prefix + tail)
                == part2_jpip_semantic_stream_at(point, tail),
    ensures part2_jpip_semantic_stream_error_continuation(root, parent + prefix, point),
{
    reveal(part2_jpip_semantic_stream_error_continuation);
    assert forall|events: Seq<Part2JpipSemanticEvent>|
        match #[trigger] part2_jpip_semantic_stream_at(point, events) {
            Some((Err(error), after, tail)) => part2_jpip_semantic_expand(root.cache, root.metadata_stream,
                root.bin, root.boxes, root.depth, root.remaining_depth, root.before, (parent + prefix) + events)
                == Some((Err(error), after, tail)),
            _ => true,
        } by {
        if let Some((Err(error), after, tail)) = part2_jpip_semantic_stream_at(point, events) {
            assert(part2_jpip_semantic_streams(point.cache, point.first, point.count, 0,
                point.header, true, Seq::empty(), state, prefix + events) == Some((Err(error), after, tail)));
            assert(part2_jpip_semantic_placeholder(root.cache, root.metadata_stream, payload,
                root.depth, root.remaining_depth, state, prefix + events) == Some((Err(error), after, tail)));
            assert(part2_jpip_semantic_expand(root.cache, root.metadata_stream, root.bin, root.boxes,
                root.depth, root.remaining_depth, root.before, parent + (prefix + events)) == Some((Err(error), after, tail)));
            assert((parent + prefix) + events =~= parent + (prefix + events));
        }
    }
}

pub(crate) proof fn part2_jpip_semantic_stream_error_lift(
    root: Part2JpipSemanticRoot, prefix: Seq<Part2JpipSemanticEvent>, point: Part2JpipSemanticStreamPoint,
    error: crate::DecodeError, after: Part2JpipSemanticState, events: Seq<Part2JpipSemanticEvent>,
)
    requires part2_jpip_semantic_stream_error_continuation(root, prefix, point),
        forall|tail: Seq<Part2JpipSemanticEvent>|
            part2_jpip_semantic_stream_at(point, events + tail) == Some((Err(error), after, tail)),
    ensures part2_jpip_semantic_expand_result(root.cache, root.metadata_stream, root.bin, root.boxes,
        root.depth, root.remaining_depth, root.before, Err(error), after),
        part2_jpip_semantic_expand_trace(root.cache, root.metadata_stream, root.bin, root.boxes,
            root.depth, root.remaining_depth, root.before, Err(error), after),
{
    reveal(part2_jpip_semantic_stream_error_continuation);
    assert forall|tail: Seq<Part2JpipSemanticEvent>|
        part2_jpip_semantic_expand(root.cache, root.metadata_stream, root.bin, root.boxes,
            root.depth, root.remaining_depth, root.before, (prefix + events) + tail)
            == Some((Err(error), after, tail)) by {
        assert(part2_jpip_semantic_stream_at(point, events + tail) == Some((Err(error), after, tail)));
        assert((prefix + events) + tail =~= prefix + (events + tail));
    }
    part2_jpip_semantic_expand_witness(root.cache, root.metadata_stream, root.bin, root.boxes,
        root.depth, root.remaining_depth, root.before, Err(error), after, prefix + events);
}

pub(crate) proof fn part2_jpip_semantic_placeholder_advance(
    root: Part2JpipSemanticRoot, reader: Part2BoxReaderState, remaining: nat, complete: bool,
    before: Part2JpipSemanticState, reference: Part2BoxReference, parent: Seq<Part2JpipSemanticEvent>,
    events: Seq<Part2JpipSemanticEvent>, replacement: (bool, bool, Seq<u8>, Seq<u8>),
    expanded: Part2JpipSemanticState, after: Part2JpipSemanticState, next_complete: bool,
)
    requires remaining > 0, part2_box_reader_next_ref(reader).0 == Some(Ok(reference)),
        reference.0.0 == crate::jp2::box_type_from_bytes_model(*b"phld"),
        forall|tail: Seq<Part2JpipSemanticEvent>|
            part2_jpip_semantic_expand(root.cache, root.metadata_stream, root.bin, root.boxes, root.depth,
                root.remaining_depth, root.before, parent + tail)
                == part2_jpip_semantic_boxes(root.cache, root.metadata_stream, root.bin, root.depth, root.remaining_depth,
                    reader, remaining, complete, before, tail),
        forall|tail: Seq<Part2JpipSemanticEvent>|
            part2_jpip_semantic_placeholder(root.cache, root.metadata_stream, reference.1, root.depth,
                root.remaining_depth, before, events + tail) == Some((Ok(replacement), expanded, tail)),
        if replacement.0 && !replacement.1 {
            let step = part2_jpip_append_reconstructed_box(expanded.output, replacement.2, replacement.3);
            step.0 == Ok(()) && after == (Part2JpipSemanticState { output: step.1, ..expanded })
                && next_complete == complete
        } else { after == expanded && next_complete == (complete && replacement.0) },
    ensures forall|tail: Seq<Part2JpipSemanticEvent>|
        part2_jpip_semantic_expand(root.cache, root.metadata_stream, root.bin, root.boxes, root.depth,
            root.remaining_depth, root.before, (parent + events) + tail)
            == part2_jpip_semantic_boxes(root.cache, root.metadata_stream, root.bin, root.depth, root.remaining_depth,
                part2_box_reader_next_ref(reader).1, (remaining - 1) as nat, next_complete, after, tail),
{
    part2_jpip_semantic_placeholder_box_step(root.cache, root.metadata_stream, root.bin, root.depth,
        root.remaining_depth, reader, remaining, complete, before, reference);
    assert forall|tail: Seq<Part2JpipSemanticEvent>|
        part2_jpip_semantic_expand(root.cache, root.metadata_stream, root.bin, root.boxes, root.depth,
            root.remaining_depth, root.before, (parent + events) + tail)
            == part2_jpip_semantic_boxes(root.cache, root.metadata_stream, root.bin, root.depth, root.remaining_depth,
                part2_box_reader_next_ref(reader).1, (remaining - 1) as nat, next_complete, after, tail) by {
        assert(part2_jpip_semantic_placeholder(root.cache, root.metadata_stream, reference.1, root.depth,
            root.remaining_depth, before, events + tail) == Some((Ok(replacement), expanded, tail)));
        assert(part2_jpip_semantic_expand(root.cache, root.metadata_stream, root.bin, root.boxes, root.depth,
            root.remaining_depth, root.before, parent + (events + tail))
            == part2_jpip_semantic_boxes(root.cache, root.metadata_stream, root.bin, root.depth, root.remaining_depth,
                reader, remaining, complete, before, events + tail));
        assert((parent + events) + tail =~= parent + (events + tail));
    }
}

pub(crate) proof fn part2_jpip_semantic_metadata_error_lift(
    root: Part2JpipSemanticRoot, parent: Seq<Part2JpipSemanticEvent>, payload: Seq<u8>,
    before: Part2JpipSemanticState, placeholder: Part2JpipPlaceholder, header: Seq<u8>,
    source: u8, target: u64, kind: crate::jp2::BoxType, error: crate::DecodeError, child: Part2JpipSemanticState,
)
    requires part2_jpip_semantic_placeholder_error_continuation(root.cache, root.metadata_stream, root.bin, root.boxes,
            root.depth, root.remaining_depth, root.before, parent, payload, before),
        part2_jpip_parse_placeholder(payload) == Ok(placeholder),
        part2_jpip_placeholder_reconstruction(placeholder.flags, placeholder.original_header, placeholder.equivalent_header)
            == Ok((source, header)), source == 0 || source == 1,
        if source == 0 { target == placeholder.bin && kind == placeholder.original_type }
        else { placeholder.equivalent_bin == Some(target) && placeholder.equivalent_type == Some(kind) },
        root.depth < u32::MAX, root.remaining_depth > 0,
        part2_jpip_semantic_expand_trace(root.cache, root.metadata_stream, target, part2_jpip_superbox(kind),
            (root.depth + 1) as u32, (root.remaining_depth - 1) as u32,
            Part2JpipSemanticState { output: Seq::empty(), ..before }, Err(error), child),
    ensures part2_jpip_semantic_expand_result(root.cache, root.metadata_stream, root.bin, root.boxes,
        root.depth, root.remaining_depth, root.before, Err(error), Part2JpipSemanticState { output: before.output, ..child }),
        part2_jpip_semantic_expand_trace(root.cache, root.metadata_stream, root.bin, root.boxes,
            root.depth, root.remaining_depth, root.before, Err(error), Part2JpipSemanticState { output: before.output, ..child }),
{
    reveal(part2_jpip_semantic_expand_trace);
    let events = choose|events: Seq<Part2JpipSemanticEvent>|
        #[trigger] part2_jpip_semantic_expand_prefix(root.cache, root.metadata_stream, target,
            part2_jpip_superbox(kind), (root.depth + 1) as u32, (root.remaining_depth - 1) as u32,
            Part2JpipSemanticState { output: Seq::empty(), ..before }, Err(error), child, events);
    if source == 0 {
        part2_jpip_semantic_original_error_prefix(root.cache, root.metadata_stream, payload, placeholder,
            header, root.depth, root.remaining_depth, before, error, child, events);
    } else {
        part2_jpip_semantic_equivalent_prefix(root.cache, root.metadata_stream, payload, placeholder,
            header, target, kind, root.depth, root.remaining_depth, before, Err(error), child, events);
    }
    assert forall|tail: Seq<Part2JpipSemanticEvent>|
        part2_jpip_semantic_expand(root.cache, root.metadata_stream, root.bin, root.boxes,
            root.depth, root.remaining_depth, root.before, (parent + events) + tail)
            == Some((Err(error), Part2JpipSemanticState { output: before.output, ..child }, tail)) by {
        assert(part2_jpip_semantic_placeholder(root.cache, root.metadata_stream, payload,
            root.depth, root.remaining_depth, before, events + tail)
            == Some((Err(error), Part2JpipSemanticState { output: before.output, ..child }, tail)));
        assert((parent + events) + tail =~= parent + (events + tail));
    }
    part2_jpip_semantic_expand_witness(root.cache, root.metadata_stream, root.bin, root.boxes,
        root.depth, root.remaining_depth, root.before, Err(error), Part2JpipSemanticState { output: before.output, ..child },
        parent + events);
}

pub(crate) proof fn part2_jpip_semantic_placeholder_append_error(
    root: Part2JpipSemanticRoot, reader: Part2BoxReaderState, remaining: nat, complete: bool,
    before: Part2JpipSemanticState, reference: Part2BoxReference, parent: Seq<Part2JpipSemanticEvent>,
    events: Seq<Part2JpipSemanticEvent>, header: Seq<u8>, payload: Seq<u8>, expanded: Part2JpipSemanticState, error: crate::DecodeError,
)
    requires remaining > 0, part2_box_reader_next_ref(reader).0 == Some(Ok(reference)),
        reference.0.0 == crate::jp2::box_type_from_bytes_model(*b"phld"),
        forall|tail: Seq<Part2JpipSemanticEvent>|
            part2_jpip_semantic_expand(root.cache, root.metadata_stream, root.bin, root.boxes, root.depth,
                root.remaining_depth, root.before, parent + tail)
                == part2_jpip_semantic_boxes(root.cache, root.metadata_stream, root.bin, root.depth, root.remaining_depth,
                    reader, remaining, complete, before, tail),
        forall|tail: Seq<Part2JpipSemanticEvent>|
            part2_jpip_semantic_placeholder(root.cache, root.metadata_stream, reference.1, root.depth,
                root.remaining_depth, before, events + tail) == Some((Ok((true, false, header, payload)), expanded, tail)),
        part2_jpip_append_reconstructed_box(expanded.output, header, payload).0 == Err(error),
    ensures part2_jpip_semantic_expand_result(root.cache, root.metadata_stream, root.bin, root.boxes,
        root.depth, root.remaining_depth, root.before, Err(error), expanded),
        part2_jpip_semantic_expand_trace(root.cache, root.metadata_stream, root.bin, root.boxes,
            root.depth, root.remaining_depth, root.before, Err(error), expanded),
{
    part2_jpip_semantic_placeholder_box_step(root.cache, root.metadata_stream, root.bin, root.depth,
        root.remaining_depth, reader, remaining, complete, before, reference);
    assert forall|tail: Seq<Part2JpipSemanticEvent>|
        part2_jpip_semantic_expand(root.cache, root.metadata_stream, root.bin, root.boxes, root.depth,
            root.remaining_depth, root.before, (parent + events) + tail) == Some((Err(error), expanded, tail)) by {
        assert(part2_jpip_semantic_placeholder(root.cache, root.metadata_stream, reference.1, root.depth,
            root.remaining_depth, before, events + tail) == Some((Ok((true, false, header, payload)), expanded, tail)));
        assert(part2_jpip_semantic_expand(root.cache, root.metadata_stream, root.bin, root.boxes, root.depth,
            root.remaining_depth, root.before, parent + (events + tail))
            == part2_jpip_semantic_boxes(root.cache, root.metadata_stream, root.bin, root.depth, root.remaining_depth,
                reader, remaining, complete, before, events + tail));
        assert((parent + events) + tail =~= parent + (events + tail));
    }
    part2_jpip_semantic_expand_witness(root.cache, root.metadata_stream, root.bin, root.boxes,
        root.depth, root.remaining_depth, root.before, Err(error), expanded, parent + events);
}

pub(crate) proof fn part2_jpip_semantic_boxes_prefix(
    cache: Part2JpipCache, metadata_stream: u64, bin: u64, depth: u32, remaining_depth: u32,
    before: Part2JpipSemanticState, bytes: Seq<u8>, reader: Part2BoxReaderState,
)
    requires depth <= crate::limits::resource_box_depth_limit(&cache.0), !before.active.contains(bin),
        part2_jpip_cache_complete(cache, (8, crate::jpip::DatabinClass::Metadata, metadata_stream, bin)),
        part2_jpip_cache_view(cache, (8, crate::jpip::DatabinClass::Metadata, metadata_stream, bin)) == Ok(bytes),
        part2_box_reader_from_input(bytes, cache.0) == Ok(reader),
    ensures forall|tail: Seq<Part2JpipSemanticEvent>|
        #[trigger] part2_jpip_semantic_expand(cache, metadata_stream, bin, true, depth, remaining_depth, before, tail)
            == part2_jpip_semantic_boxes(cache, metadata_stream, bin, depth, remaining_depth, reader,
                bytes.len(), true, Part2JpipSemanticState { active: before.active.push(bin), ..before }, tail),
{
    crate::limits::semantic_limit_value_equivalence();
    reveal_with_fuel(part2_jpip_semantic_expand, 2);
    reveal_with_fuel(part2_jpip_semantic_boxes, 2);
    assert forall|tail: Seq<Part2JpipSemanticEvent>|
        part2_jpip_semantic_expand(cache, metadata_stream, bin, true, depth, remaining_depth, before, tail)
            == part2_jpip_semantic_boxes(cache, metadata_stream, bin, depth, remaining_depth, reader,
                bytes.len(), true, Part2JpipSemanticState { active: before.active.push(bin), ..before }, tail) by {
    }
}

pub(crate) proof fn part2_jpip_semantic_expand_witness(
    cache: Part2JpipCache, metadata_stream: u64, bin: u64, boxes: bool, depth: u32, remaining_depth: u32,
    before: Part2JpipSemanticState, result: Result<bool, crate::DecodeError>, after: Part2JpipSemanticState,
    events: Seq<Part2JpipSemanticEvent>,
)
    requires forall|tail: Seq<Part2JpipSemanticEvent>|
        part2_jpip_semantic_expand(cache, metadata_stream, bin, boxes, depth, remaining_depth,
            before, events + tail) == Some((result, after, tail)),
    ensures part2_jpip_semantic_expand_result(cache, metadata_stream, bin, boxes, depth, remaining_depth,
            before, result, after),
        part2_jpip_semantic_expand_trace(cache, metadata_stream, bin, boxes, depth, remaining_depth, before, result, after),
{
    reveal(part2_jpip_semantic_expand_result);
    reveal(part2_jpip_semantic_expand_trace);
    reveal(part2_jpip_semantic_expand_prefix);
    assert(events + Seq::empty() =~= events);
    assert(part2_jpip_semantic_expand_prefix(cache, metadata_stream, bin, boxes, depth, remaining_depth,
        before, result, after, events));
    assert(exists|prefix: Seq<Part2JpipSemanticEvent>| #[trigger] part2_jpip_semantic_expand_prefix(
        cache, metadata_stream, bin, boxes, depth, remaining_depth, before, result, after, prefix));
}

pub type Part2JpipContainerAssembly = (
    crate::jpip::JpipAvailability, Seq<Part2JpipMissing>, Seq<Part2JpipSemanticNeed>, Option<Seq<u8>>,
);

pub(crate) open spec fn part2_jpip_semantic_assembly_run(
    cache: Part2JpipCache, metadata_stream: u64, events: Seq<Part2JpipSemanticEvent>,
) -> Option<(Result<Part2JpipContainerAssembly, crate::DecodeError>, Seq<Part2JpipSemanticEvent>)> {
    let initial = Part2JpipSemanticState { active: Seq::empty(), output: Seq::empty(),
        missing: Seq::empty(), needs: Seq::empty() };
    match part2_jpip_semantic_expand(cache, metadata_stream, 0, true, 0, u32::MAX, initial, events) {
        None => None,
        Some((Err(error), _state, tail)) => Some((Err(error), tail)),
        Some((Ok(complete), state, tail)) => if !complete {
            Some((Ok((if state.output.len() == 0 { crate::jpip::JpipAvailability::Missing }
                else { crate::jpip::JpipAvailability::Partial }, state.missing, state.needs, None)), tail))
        } else if state.output.len() as u64 > crate::limits::resource_input_byte_limit(&cache.0) {
            Some((Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes,
                limit: crate::limits::resource_input_byte_limit(&cache.0), actual: state.output.len() as u64 }), tail))
        } else {
            match part2_parse_and_inspect_container(state.output, &cache.0) {
                Err(error) => Some((Err(error), tail)),
                Ok(_) => Some((Ok((crate::jpip::JpipAvailability::Available, state.missing, state.needs, Some(state.output))), tail)),
            }
        },
    }
}

pub closed spec fn part2_jpip_semantic_assembly_result(
    cache: Part2JpipCache, metadata_stream: u64, result: Result<Part2JpipContainerAssembly, crate::DecodeError>,
) -> bool {
    exists|events: Seq<Part2JpipSemanticEvent>| part2_jpip_semantic_assembly_run(cache, metadata_stream, events)
        == Some((result, Seq::empty()))
}

pub(crate) proof fn part2_jpip_semantic_assembly_witness(
    cache: Part2JpipCache, metadata_stream: u64, events: Seq<Part2JpipSemanticEvent>,
    result: Result<Part2JpipContainerAssembly, crate::DecodeError>,
)
    requires part2_jpip_semantic_assembly_run(cache, metadata_stream, events) == Some((result, Seq::empty())),
    ensures part2_jpip_semantic_assembly_result(cache, metadata_stream, result),
{
    reveal(part2_jpip_semantic_assembly_result);
}

pub(crate) proof fn part2_jpip_semantic_assembly_first_error(
    cache: Part2JpipCache, metadata_stream: u64, error: crate::DecodeError, after: Part2JpipSemanticState,
)
    requires part2_jpip_semantic_expand_result(cache, metadata_stream, 0, true, 0, u32::MAX,
        Part2JpipSemanticState { active: Seq::empty(), output: Seq::empty(), missing: Seq::empty(), needs: Seq::empty() },
        Err(error), after),
    ensures part2_jpip_semantic_assembly_result(cache, metadata_stream, Err(error)),
{
    reveal(part2_jpip_semantic_expand_result);
    let before = Part2JpipSemanticState { active: Seq::empty(), output: Seq::empty(), missing: Seq::empty(), needs: Seq::empty() };
    let events = choose|events: Seq<Part2JpipSemanticEvent>|
        #[trigger] part2_jpip_semantic_expand(cache, metadata_stream, 0, true, 0, u32::MAX, before, events)
            == Some((Err(error), after, Seq::empty()));
    part2_jpip_semantic_assembly_witness(cache, metadata_stream, events, Err(error));
}

}
