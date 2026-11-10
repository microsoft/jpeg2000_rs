//! Raw container traversal, source-derived owners and ordered final attachment.

use super::*;

verus! {

pub type Part2RawCodestream = (Part2BoxHeader, Seq<u8>, Option<Part2RawCodestreamAssociation>);

pub struct Part2RawContainerState {
    pub header: Option<Part2RawJp2Header>,
    pub streams: Seq<Part2RawCodestream>,
    pub associations: Seq<Part2RawCodestreamAssociation>,
    pub layers: Seq<Part2RawCompositingLayer>,
    pub composition: Option<Part2RawComposition>,
    pub metadata_boxes: u32,
    pub metadata_depth: u32,
    pub box_count: u64,
}

pub struct Part2RawJp2File {
    pub file_type: Part2FileType,
    pub header: Part2RawJp2Header,
    pub streams: Seq<Part2RawCodestream>,
    pub layers: Seq<Part2RawCompositingLayer>,
    pub composition: Option<Part2RawComposition>,
    pub metadata_boxes: u32,
    pub metadata_depth: u32,
    pub box_count: u64,
}

pub open spec fn part2_container_error(offset: u64, kind: crate::MalformedKind) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset, kind }
}

pub open spec fn part2_container_initial_state() -> Part2RawContainerState {
    Part2RawContainerState {
        header: None, streams: Seq::empty(), associations: Seq::empty(), layers: Seq::empty(),
        composition: None, metadata_boxes: 0, metadata_depth: 0, box_count: 2,
    }
}

pub open spec fn part2_container_next_stream_count(count: nat, limits: crate::ResourceLimits, offset: u64)
    -> Result<u64, crate::DecodeError>
{
    if count >= u64::MAX as nat {
        Err(part2_container_error(offset, crate::MalformedKind::ArithmeticOverflow))
    } else {
        let actual = (count + 1) as u64;
        if actual > crate::limits::resource_codestream_limit(&limits) as u64 {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Codestreams,
                limit: crate::limits::resource_codestream_limit(&limits) as u64, actual })
        } else { Ok(actual) }
    }
}

#[verifier::opaque]
pub open spec fn part2_container_step(
    input: Part2BoxReference, previous: Part2RawContainerState, file_type: Part2FileType, limits: crate::ResourceLimits,
) -> Result<Part2RawContainerState, crate::DecodeError> {
    if previous.box_count == u64::MAX {
        Err(part2_container_error(0, crate::MalformedKind::ArithmeticOverflow))
    } else {
        let state = Part2RawContainerState { box_count: (previous.box_count + 1) as u64, ..previous };
        let kind = input.0.0;
        let offset = input.0.1;
        if kind == crate::jp2::BoxType::SIGNATURE || kind == crate::jp2::BoxType::FILE_TYPE {
            Err(part2_container_error(offset, crate::MalformedKind::InvalidBoxOrder))
        } else if kind == crate::jp2::BoxType::JP2_HEADER {
            if state.header.is_some() || state.streams.len() > 0 || state.associations.len() > 0
                || state.layers.len() > 0 || state.composition.is_some() {
                Err(part2_container_error(offset, crate::MalformedKind::InvalidBoxOrder))
            } else {
                match part2_box_payload_offset(input.0) {
                    Err(error) => Err(error),
                    Ok(base) => match part2_parse_jp2_header(input.1, limits, base) {
                        Err(error) => Err(error),
                        Ok(header) => Ok(Part2RawContainerState { header: Some(header), ..state }),
                    },
                }
            }
        } else if kind == crate::jp2::BoxType::CODESTREAM_HEADER {
            if !part2_file_type_jpx(file_type) {
                Err(part2_container_error(offset, crate::MalformedKind::InvalidFileType))
            } else if state.header.is_none() || state.streams.len() > 0 {
                Err(part2_container_error(offset, crate::MalformedKind::InvalidBoxOrder))
            } else {
                match part2_container_next_stream_count(state.associations.len(), limits, offset) {
                    Err(error) => Err(error),
                    Ok(_) => match part2_box_payload_offset(input.0) {
                        Err(error) => Err(error),
                        Ok(base) => match part2_parse_codestream_header(input.1, state.header, limits, base) {
                            Err(error) => Err(error),
                            Ok(header) => Ok(Part2RawContainerState {
                                associations: state.associations.push((input.0, input.1, Some(header))), ..state
                            }),
                        },
                    },
                }
            }
        } else if kind == crate::jp2::BoxType::COMPOSITING_LAYER_HEADER {
            if !part2_file_type_jpx(file_type) {
                Err(part2_container_error(offset, crate::MalformedKind::InvalidFileType))
            } else if state.header.is_none() || state.streams.len() > 0 || state.composition.is_some() {
                Err(part2_container_error(offset, crate::MalformedKind::InvalidBoxOrder))
            } else if state.layers.len() >= usize::MAX as nat {
                Err(part2_container_error(offset, crate::MalformedKind::ArithmeticOverflow))
            } else {
                let actual = (state.layers.len() + 1) as u64;
                if actual > crate::limits::resource_layer_limit(&limits) as u64 {
                    Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Layers,
                        limit: crate::limits::resource_layer_limit(&limits) as u64, actual })
                } else {
                    match part2_parse_compositing_layer(input, limits) {
                        Err(error) => Err(error),
                        Ok(layer) => Ok(Part2RawContainerState { layers: state.layers.push(layer), ..state }),
                    }
                }
            }
        } else if kind == crate::jp2::BoxType::COMPOSITION {
            if !part2_file_type_jpx(file_type) {
                Err(part2_container_error(offset, crate::MalformedKind::InvalidFileType))
            } else if state.header.is_none() || state.streams.len() > 0
                || state.composition.is_some() || state.layers.len() == 0 {
                Err(part2_container_error(offset, crate::MalformedKind::InvalidBoxOrder))
            } else {
                match part2_parse_composition(input, limits) {
                    Err(error) => Err(error),
                    Ok(composition) => Ok(Part2RawContainerState { composition: Some(composition), ..state }),
                }
            }
        } else if kind == crate::jp2::BoxType::CONTIGUOUS_CODESTREAM {
            if state.header.is_none() {
                Err(part2_container_error(offset, crate::MalformedKind::InvalidBoxOrder))
            } else {
                match part2_container_next_stream_count(state.streams.len(), limits, offset) {
                    Err(error) => Err(error),
                    Ok(actual) => if actual > 1 && !part2_file_type_jpx(file_type) {
                        Err(part2_container_error(offset, crate::MalformedKind::InvalidBoxContents))
                    } else {
                        Ok(Part2RawContainerState { streams: state.streams.push((input.0, input.1, None)), ..state })
                    },
                }
            }
        } else {
            match part2_inspect_metadata_box(input, limits, 1, (u32::MAX - 1) as u32) {
                Err(error) => Err(error),
                Ok(value) => {
                    let count = state.metadata_boxes as nat + value.0 as nat;
                    if count > u32::MAX as nat {
                        Err(part2_container_error(0, crate::MalformedKind::ArithmeticOverflow))
                    } else {
                        Ok(Part2RawContainerState { metadata_boxes: count as u32,
                            metadata_depth: if state.metadata_depth < value.1 { value.1 } else { state.metadata_depth }, ..state })
                    }
                },
            }
        }
    }
}

pub open spec fn part2_container_attach(
    streams: Seq<Part2RawCodestream>, associations: Seq<Part2RawCodestreamAssociation>, count: nat,
) -> Seq<Part2RawCodestream> {
    Seq::new(streams.len(), |i: int|
        if i < count && i < associations.len() {
            (streams[i].0, streams[i].1, Some(part2_codestream_association_clone(associations[i])))
        } else { streams[i] })
}

#[verifier::opaque]
pub open spec fn part2_container_finish(state: Part2RawContainerState, file_type: Part2FileType)
    -> Result<Part2RawJp2File, crate::DecodeError>
{
    match state.header {
        None => Err(part2_raw_header_missing(0)),
        Some(header) => {
            if state.streams.len() == 0 { Err(part2_raw_header_missing(0)) }
            else if state.associations.len() > state.streams.len() {
                Err(part2_container_error(0, crate::MalformedKind::InvalidBoxContents))
            } else {
                match part2_validate_layer_references(state.layers, state.streams.len() as usize) {
                    Err(error) => Err(error),
                    Ok(()) => Ok(Part2RawJp2File {
                        file_type, header,
                        streams: part2_container_attach(state.streams, state.associations, state.associations.len()),
                        layers: state.layers, composition: state.composition, metadata_boxes: state.metadata_boxes,
                        metadata_depth: state.metadata_depth, box_count: state.box_count,
                    }),
                }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_container_boxes(
    input: Seq<u8>, reader: Part2BoxReaderState, state: Part2RawContainerState,
    file_type: Part2FileType, limits: crate::ResourceLimits,
) -> Result<Part2RawJp2File, crate::DecodeError>
    decreases input.len() as int - reader.position as int,
{
    let next = part2_box_reader_next_ref(reader);
    match next.0 {
        None => part2_container_finish(state, file_type),
        Some(result) => if next.1.position <= reader.position || next.1.position > input.len() {
            Err(part2_container_error(reader.position as u64, crate::MalformedKind::InvalidBoxLength))
        } else {
            match result {
                Err(error) => Err(error),
                Ok(box_ref) => match part2_container_step(box_ref, state, file_type, limits) {
                    Err(error) => Err(error),
                    Ok(updated) => part2_container_boxes(input, next.1, updated, file_type, limits),
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_parse_container(input: Seq<u8>, limits: crate::ResourceLimits)
    -> Result<Part2RawJp2File, crate::DecodeError>
{
    match part2_container_prologue(input, limits) {
        Err(error) => Err(error),
        Ok(prefix) => part2_container_boxes(input, prefix.1, part2_container_initial_state(), prefix.0, limits),
    }
}

}
