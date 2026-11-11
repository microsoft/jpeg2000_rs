//! Complete data-bin reconstruction and recursive metadata placeholder expansion.

use super::{
    DatabinCache, DatabinClass, DatabinId, DecodeError, EOC, JpipAvailability, JpipByteView,
    JpipContainerAssembly, JpipMissingRange, JpipPacketSelection, JpipPlaceholder,
    JpipSemanticNeed, JpipSemanticNeedKind, MalformedKind, Resource, SOC, append_missing_ranges,
    copy_bytes, read_u32_be, read_u64_be, write_u32_be, write_u64_be,
};
#[cfg(verus_keep_ghost)]
use super::{
    databin_id_view, jpip_byte_outcome, jpip_byte_view, jpip_cache_view, jpip_layout_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(super) enum PlaceholderSource {
    Original,
    Equivalent,
    Codestream,
    Empty,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(super) open spec fn placeholder_source_view(source: PlaceholderSource) -> u8 {
        match source {
            PlaceholderSource::Original => 0,
            PlaceholderSource::Equivalent => 1,
            PlaceholderSource::Codestream => 2,
            PlaceholderSource::Empty => 3,
        }
    }

    pub(super) open spec fn placeholder_header_option_view(
        header: Option<&[u8]>,
    ) -> Option<Seq<u8>> {
        match header { Some(bytes) => Some(bytes@), None => None }
    }

    pub(super) open spec fn placeholder_reconstruction_outcome(
        value: Result<(PlaceholderSource, &[u8]), DecodeError>,
    ) -> Result<(u8, Seq<u8>), DecodeError> {
        match value {
            Ok((source, header)) => Ok((placeholder_source_view(source), header@)),
            Err(error) => Err(error),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures placeholder_reconstruction_outcome(result)
        == crate::specs::part2_jpip_placeholder_reconstruction(
            flags, original@, placeholder_header_option_view(equivalent),
        ),
))]
pub(super) fn placeholder_reconstruction<'a>(
    flags: u32,
    original: &'a [u8],
    equivalent: Option<&'a [u8]>,
) -> Result<(PlaceholderSource, &'a [u8]), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_jpip_placeholder_reconstruction); }
    if flags & 1 != 0 {
        Ok((PlaceholderSource::Original, original))
    } else if flags & 2 != 0 {
        match equivalent {
            Some(header) => Ok((PlaceholderSource::Equivalent, header)),
            None => Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents)),
        }
    } else if flags & 4 != 0 {
        Ok((PlaceholderSource::Codestream, original))
    } else {
        Ok((PlaceholderSource::Empty, original))
    }
}

impl DatabinCache {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_byte_outcome(result) == crate::specs::part2_jpip_cache_codestream(
            jpip_cache_view(self), jpip_layout_view(layout)),
    ))]
    pub fn reconstruct_codestream(
        &self,
        layout: &[DatabinId],
    ) -> Result<JpipByteView, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(databin_id_view); }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost identifiers = jpip_layout_view(layout); }
        #[cfg(verus_keep_ghost)]
        proof! {
            let length = layout.len();
            assert((length & 1_usize) == length % 2_usize) by(bit_vector);
        }
        if layout.len() < 3 || layout.len() & 1 == 0 {
            return Err(DecodeError::malformed(
                layout.len() as u64,
                MalformedKind::InvalidJpipLayout,
            ));
        }
        let first = layout[0];
        if !matches!(first.class, DatabinClass::MainHeader) || first.in_class != 0 {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout));
        }
        let mut pair = 1_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant pair <= layout.len(),
                    identifiers == jpip_layout_view(layout),
                    identifiers.len() == layout.len(),
                    forall|position: int| 0 <= position < layout.len() ==>
                        #[trigger] identifiers[position] == databin_id_view(layout@[position]),
                    layout.len() >= 3, layout.len() % 2 == 1, pair % 2 == 1,
                    databin_id_view(first) == identifiers[0],
                    first.class == DatabinClass::MainHeader, first.in_class == 0,
                    crate::specs::part2_jpip_codestream_pairs(identifiers, 1) ==
                        crate::specs::part2_jpip_codestream_pairs(identifiers, pair as nat),
                decreases layout.len() - pair,
            )
        )]
        while pair < layout.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_codestream_pairs); }
            let data_index = pair.checked_add(1).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(pair as u64, MalformedKind::ArithmeticOverflow),
                ))]
                || {
                DecodeError::malformed(pair as u64, MalformedKind::ArithmeticOverflow)
            })?;
            let header = *layout.get(pair).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_layout_error(pair as u64),
                ))]
                || DecodeError::malformed(pair as u64, MalformedKind::InvalidJpipLayout),
            )?;
            let data = *layout.get(data_index).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_layout_error(data_index as u64),
                ))]
                || DecodeError::malformed(data_index as u64, MalformedKind::InvalidJpipLayout),
            )?;
            if !matches!(header.class, DatabinClass::TileHeader)
                || !matches!(data.class, DatabinClass::TileData)
                || header.codestream != first.codestream
                || data.codestream != first.codestream
                || header.in_class != data.in_class
            {
                return Err(DecodeError::malformed(
                    pair as u64,
                    MalformedKind::InvalidJpipLayout,
                ));
            }
            pair += 2;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_codestream_pairs); }
        let view = self.reconstruct(layout)?;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_byte_view); }
        if !view.bytes.starts_with(&SOC) || !view.bytes.ends_with(&EOC) {
            return Err(DecodeError::malformed(
                0,
                MalformedKind::MissingRequiredStructure,
            ));
        }
        Ok(view)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_byte_outcome(result) == crate::specs::part2_jpip_cache_container(
            jpip_cache_view(self), jpip_layout_view(layout)),
    ))]
    pub fn reconstruct_container(&self, layout: &[DatabinId]) -> Result<JpipByteView, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(databin_id_view); }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost identifiers = jpip_layout_view(layout); }
        if layout.is_empty() {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout));
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= layout.len(),
                    identifiers == jpip_layout_view(layout),
                    identifiers.len() == layout.len(), layout.len() > 0,
                    forall|position: int| 0 <= position < layout.len() ==>
                        #[trigger] identifiers[position] == databin_id_view(layout@[position]),
                    crate::specs::part2_jpip_metadata_layout(identifiers, 0) ==
                        crate::specs::part2_jpip_metadata_layout(identifiers, index as nat),
                decreases layout.len() - index,
            )
        )]
        while index < layout.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_metadata_layout); }
            if !matches!(layout[index].class, DatabinClass::Metadata) {
                return Err(DecodeError::malformed(
                    index as u64,
                    MalformedKind::InvalidJpipLayout,
                ));
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_metadata_layout); }
        self.reconstruct(layout)
    }

    pub fn assemble_semantic_container(
        &self,
        metadata_codestream: u64,
    ) -> Result<JpipContainerAssembly, DecodeError> {
        let mut output = Vec::new();
        let mut missing = Vec::new();
        let mut needs = Vec::new();
        let mut active = Vec::new();
        let complete = self.expand_metadata_bin(
            metadata_codestream,
            0,
            true,
            0,
            u32::MAX,
            &mut active,
            &mut output,
            &mut missing,
            &mut needs,
        )?;
        if !complete {
            return Ok(JpipContainerAssembly {
                status: if output.is_empty() {
                    JpipAvailability::Missing
                } else {
                    JpipAvailability::Partial
                },
                missing,
                needs,
                container: None,
            });
        }
        if output.len() as u64 > self.limits.maximum_input_bytes() {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                self.limits.maximum_input_bytes(),
                output.len() as u64,
            ));
        }
        crate::jp2::parse_and_inspect(&output, &self.limits)?;
        Ok(JpipContainerAssembly {
            status: JpipAvailability::Available,
            missing,
            needs,
            container: Some(JpipByteView { bytes: output }),
        })
    }

    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(verus_keep_ghost, verus_spec(decreases remaining_depth,))]
    fn expand_metadata_bin(
        &self,
        metadata_codestream: u64,
        bin: u64,
        boxes: bool,
        depth: u32,
        remaining_depth: u32,
        active: &mut Vec<u64>,
        output: &mut Vec<u8>,
        missing: &mut Vec<JpipMissingRange>,
        needs: &mut Vec<JpipSemanticNeed>,
    ) -> Result<bool, DecodeError> {
        if !crate::refinement::jpip_metadata_descent_allowed(
            depth,
            self.limits.maximum_box_depth(),
            false,
        ) {
            return Err(DecodeError::limit(
                Resource::BoxDepth,
                u64::from(self.limits.maximum_box_depth()),
                u64::from(depth),
            ));
        }
        let mut active_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant active_index <= active.len(),
                decreases active.len() - active_index,
            )
        )]
        while active_index < active.len() {
            if !crate::refinement::jpip_metadata_descent_allowed(
                depth,
                self.limits.maximum_box_depth(),
                active[active_index] == bin,
            ) {
                return Err(DecodeError::malformed(
                    bin,
                    MalformedKind::InvalidBoxContents,
                ));
            }
            active_index += 1;
        }
        let id = DatabinId::new(8, metadata_codestream, bin)?;
        if !self.is_complete(id) {
            append_missing_ranges(missing, &self.complete_databin_missing(id));
            needs.push(JpipSemanticNeed {
                kind: JpipSemanticNeedKind::MetadataBin,
                identifier: bin,
            });
            return Ok(false);
        }
        let bytes = self.databin_view(id)?.into_bytes();
        if !boxes {
            output.extend_from_slice(&bytes);
            return Ok(true);
        }
        active.push(bin);
        let mut reader = crate::jp2::BoxReader::new(&bytes, &self.limits)?;
        let mut complete = true;
        let mut remaining_boxes = bytes.len();
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(decreases remaining_boxes,)
        )]
        while let Some(box_result) = reader.next_box_ref() {
            if remaining_boxes == 0 {
                return Err(DecodeError::malformed(bin, MalformedKind::InvalidBoxLength));
            }
            remaining_boxes -= 1;
            let box_ref = box_result?;
            if box_ref
                .header
                .box_type()
                .equals(crate::jp2::BoxType::new(*b"phld"))
            {
                let placeholder = parse_jpip_placeholder(box_ref.payload)?;
                let (source, header) = placeholder_reconstruction(
                    placeholder.flags,
                    &placeholder.original_header,
                    match &placeholder.equivalent_header {
                        Some(header) => Some(header.as_slice()),
                        None => None,
                    },
                )?;
                let mut payload = Vec::new();
                let mut appended = false;
                let replacement_complete = match source {
                    PlaceholderSource::Original => self.expand_metadata_bin(
                        metadata_codestream,
                        placeholder.bin,
                        jpip_superbox(placeholder.original_type),
                        depth.checked_add(1).ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                        })?,
                        remaining_depth.checked_sub(1).ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                        })?,
                        active,
                        &mut payload,
                        missing,
                        needs,
                    )?,
                    PlaceholderSource::Equivalent => {
                        let bin = placeholder.equivalent_bin.ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::InvalidBoxContents)
                        })?;
                        let box_type = placeholder.equivalent_type.ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::InvalidBoxContents)
                        })?;
                        self.expand_metadata_bin(
                            metadata_codestream,
                            bin,
                            jpip_superbox(box_type),
                            depth.checked_add(1).ok_or_else(|| {
                                DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                            })?,
                            remaining_depth.checked_sub(1).ok_or_else(|| {
                                DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                            })?,
                            active,
                            &mut payload,
                            missing,
                            needs,
                        )?
                    }
                    PlaceholderSource::Codestream => {
                        let first_stream = placeholder.stream.ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::InvalidBoxContents)
                        })?;
                        let mut stream_index = 0_u32;
                        let mut streams_complete = true;
                        #[cfg_attr(
                        verus_keep_ghost,
                        verus_spec(
                            invariant stream_index <= placeholder.stream_count,
                            decreases placeholder.stream_count - stream_index,
                        )
                    )]
                        while stream_index < placeholder.stream_count {
                            let stream = first_stream
                                .checked_add(u64::from(stream_index))
                                .ok_or_else(|| {
                                    DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                                })?;
                            let snapshot = self.build_automatic_snapshot(
                                stream,
                                None,
                                &JpipPacketSelection::all_components(),
                                &self.limits,
                            )?;
                            match snapshot.ready {
                                Some(snapshot) if snapshot.available_layers == snapshot.layers => {
                                    if placeholder.stream_count == 1 {
                                        payload.extend_from_slice(snapshot.codestream.as_bytes());
                                    } else {
                                        append_reconstructed_box(
                                            output,
                                            header,
                                            snapshot.codestream.as_bytes(),
                                        )?;
                                    }
                                }
                                Some(snapshot) => {
                                    append_missing_ranges(missing, &snapshot.missing);
                                    needs.push(JpipSemanticNeed {
                                        kind: JpipSemanticNeedKind::Codestream,
                                        identifier: stream,
                                    });
                                    streams_complete = false;
                                }
                                None => {
                                    append_missing_ranges(missing, &snapshot.missing);
                                    needs.push(JpipSemanticNeed {
                                        kind: JpipSemanticNeedKind::Codestream,
                                        identifier: stream,
                                    });
                                    streams_complete = false;
                                }
                            }
                            stream_index += 1;
                        }
                        appended = placeholder.stream_count > 1 && streams_complete;
                        streams_complete
                    }
                    PlaceholderSource::Empty => {
                        payload.clear();
                        true
                    }
                };
                if replacement_complete {
                    if !appended {
                        append_reconstructed_box(output, header, &payload)?;
                    }
                } else {
                    complete = false;
                }
            } else {
                let start = usize::try_from(box_ref.header.offset())
                    .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                let length = usize::try_from(box_ref.header.total_length())
                    .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                let end = start
                    .checked_add(length)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                output.extend_from_slice(bytes.get(start..end).ok_or_else(|| {
                    DecodeError::malformed(start as u64, MalformedKind::Truncated)
                })?);
            }
        }
        active.pop();
        Ok(complete)
    }
}

pub(super) fn parse_jpip_placeholder(payload: &[u8]) -> Result<JpipPlaceholder, DecodeError> {
    if payload.len() < 20 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents));
    }
    let flags = read_u32_be(payload, 0)?;
    let bin_high = u64::from(read_u32_be(payload, 4)?);
    let bin_low = u64::from(read_u32_be(payload, 8)?);
    let bin = (bin_high << 32) | bin_low;
    let original_start = 12_usize;
    let first_length = read_u32_be(payload, original_start)?;
    let header_length = if first_length == 1 { 16_usize } else { 8_usize };
    let original_end = original_start
        .checked_add(header_length)
        .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    let original = payload
        .get(original_start..original_end)
        .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidBoxContents))?;
    let box_type = crate::jp2::BoxType::new([
        *original
            .get(4)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidBoxContents))?,
        *original
            .get(5)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidBoxContents))?,
        *original
            .get(6)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidBoxContents))?,
        *original
            .get(7)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidBoxContents))?,
    ]);
    if flags & !0x0f != 0 || flags & 8 != 0 && flags & 4 == 0 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents));
    }
    let mut position = original_end;
    let (equivalent_bin, equivalent_header, equivalent_type) = if flags & 6 != 0 {
        let bin = read_u64_be(payload, position)?;
        position = position
            .checked_add(8)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let length = read_u32_be(payload, position)?;
        let header_length = if length == 1 { 16_usize } else { 8_usize };
        let end = position
            .checked_add(header_length)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let header = payload
            .get(position..end)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidBoxContents))?;
        let box_type = crate::jp2::BoxType::new([header[4], header[5], header[6], header[7]]);
        position = end;
        (Some(bin), Some(copy_bytes(header)), Some(box_type))
    } else {
        (None, None, None)
    };
    let (stream, stream_count) = if flags & 4 != 0 {
        let stream = read_u64_be(payload, position)?;
        position = position
            .checked_add(8)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let count = if flags & 8 != 0 {
            let count = read_u32_be(payload, position)?;
            position = position
                .checked_add(4)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            if count == 0 {
                return Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents));
            }
            count
        } else {
            1
        };
        (Some(stream), count)
    } else {
        (None, 0)
    };
    if position != payload.len() {
        if flags == 4 && payload.len() == original_end + 24 {
            // Compatibility with the previously selected provisional layout.
            return Err(DecodeError::malformed(
                original_end as u64,
                MalformedKind::InvalidBoxContents,
            ));
        } else {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents));
        }
    }
    Ok(JpipPlaceholder {
        flags,
        bin,
        original_header: copy_bytes(original),
        original_type: box_type,
        equivalent_bin,
        equivalent_header,
        equivalent_type,
        stream,
        stream_count,
    })
}

fn jpip_superbox(box_type: crate::jp2::BoxType) -> bool {
    [
        *b"jp2h", *b"jpch", *b"jplh", *b"cgrp", *b"res ", *b"asoc", *b"comp",
    ]
    .iter()
    .any(|value| box_type.equals(crate::jp2::BoxType::new(*value)))
}

fn append_reconstructed_box(
    output: &mut Vec<u8>,
    original_header: &[u8],
    payload: &[u8],
) -> Result<(), DecodeError> {
    if original_header.len() != 8 && original_header.len() != 16 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents));
    }
    let total = original_header
        .len()
        .checked_add(payload.len())
        .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    if crate::refinement::jpip_box_length(original_header.len() as u64, payload.len() as u64)
        != total as u128
    {
        return Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow));
    }
    let mut header = copy_bytes(original_header);
    if header.len() == 8 {
        let length = u32::try_from(total)
            .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        write_u32_be(&mut header, 0, length)?;
    } else {
        write_u32_be(&mut header, 0, 1)?;
        write_u64_be(&mut header, 8, total as u64)?;
    }
    output.extend_from_slice(&header);
    output.extend_from_slice(payload);
    Ok(())
}
