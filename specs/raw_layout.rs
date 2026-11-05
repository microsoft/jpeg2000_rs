//! Complete raw-input layout composition through the actual accepted producers.

use super::*;

verus! {

pub(crate) type Part1CompleteLayout = (
    Part1LayoutMainFields, Part1ProfileMetadata, u32, u64, Seq<Part1TilePartPayload>,
);
pub(crate) type Part1CompleteLayoutResult = Result<Part1CompleteLayout, crate::DecodeError>;

pub(crate) open spec fn part1_layout_profile_tiles(parts: Seq<Part1TilePartPayload>) -> Seq<Part1ProfileTile> {
    parts.map_values(|part: Part1TilePartPayload| Part1ProfileTile {
        styles: part.component_coding_styles, roi: part.roi_shifts,
        has_roi: part.has_roi_marker, has_functional: part.has_functional_header_marker,
    })
}

#[verifier::opaque]
pub(crate) open spec fn part1_layout_after_tiles<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState,
) -> Part1CompleteLayoutResult {
    match part1_classify_codestream_profile(
        main.raw.r_siz, main.raw.capabilities, main.raw.profile, main.raw.corresponding_profile,
        main.styles, main.raw.roi, part1_layout_profile_tiles(state.3), main.raw.image_size.components,
        exists|index: int| 0 <= index < main.raw.roi_seen.len() && main.raw.roi_seen[index],
    ) {
        Err(error) => Err(error),
        Ok(profile) => Ok((part1_main_header_fields(main), profile, tile_parts,
            part1_codestream_offset(reader.position), state.3)),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_layout_tile_part<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState) {
    if tile_parts == u32::MAX {
        (Err(part1_codestream_malformed(reader.position, crate::MalformedKind::ArithmeticOverflow)), reader, tile_parts, state)
    } else {
        let next = (tile_parts as int + 1) as u32;
        if next > crate::limits::resource_tile_part_limit(reader.limits) {
            (Err(crate::DecodeError::LimitExceeded {
                resource: crate::Resource::TileParts,
                limit: crate::limits::resource_tile_part_limit(reader.limits) as u64,
                actual: next as u64,
            }), reader, next, state)
        } else {
            let sot = part1_codestream_read_sot(reader, main.tile_count);
            match sot.0 {
                Err(error) => (Err(error), sot.1, next, state),
                Ok(tile) => {
                    let metadata = part1_tile_part_main_metadata(sot.1.position, tile, (next - 1) as u32,
                        main.raw.extensions.lengths, main.raw.plm_seen, main.raw.plm, main.ppm_frames,
                        main.raw.ppm_fragments, main.header);
                    match metadata {
                        Err(error) => (Err(error), sot.1, next, state),
                        Ok((lengths, headers)) => part1_layout_inherited_tile_part(sot.1, main, next, state, tile, lengths, headers),
                    }
                },
            }
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_layout_inherited_tile_part<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState,
    tile: (usize, u32, u16, u8, u8), lengths: Part1PacketLengths, headers: Part1PackedHeaders,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState) {
    let index = tile.2 as usize;
    let selection = part1_select_inherited_tile_configuration(reader.position, index,
        main.raw.roi, main.coding_style, main.quantization, main.styles,
        (state.0.0, state.0.1, state.0.2, state.0.3, state.3));
    match selection {
        Err(error) => (Err(error), reader, tile_parts, state),
        Ok(selected) => {
            let quantizations = part1_inherited_tile_owner(index, main.quantizations, state.0.4);
            let progression = part1_inherited_tile_owner(index, main.raw.progression, state.0.5);
            let copied_mct = part1_inherited_tile_owner(index,
                (main.mct.arrays, main.mct.records, main.mct.order), state.1);
            let mct = Part1MctParameters { arrays: copied_mct.0, records: copied_mct.1, order: copied_mct.2 };
            let extensions = part1_inherited_tile_owner(index, main.raw.extensions, state.2);
            let read = part1_read_tile_part(reader, tile, (selected.2, selected.3),
                selected.4, quantizations, selected.1, progression, mct, extensions,
                main.raw.image_size.components, lengths, headers);
            match read.0 {
                Err(error) => (Err(error), read.1, tile_parts, state),
                Ok((payload, parameters, extensions)) => {
                    let committed = part1_commit_persistent_tile_state(state, Part1PersistentTileCommit {
                        position: read.1.position, start: tile.0, index,
                        previous_roi: selected.0, payload,
                        parameters: (parameters.arrays, parameters.records, parameters.order), extensions,
                    });
                    (committed.0, read.1, tile_parts, committed.1)
                },
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_layout_continuation<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState, input_length: usize,
) -> Part1CompleteLayoutResult
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    match part1_codestream_peek_marker(reader) {
        Err(error) => Err(error),
        Ok(marker) => if marker == 0xff90 {
            let step = part1_layout_tile_part(reader, main, tile_parts, state);
            match step.0 {
                Err(error) => Err(error),
                Ok(()) => if !part1_parser_progress(reader.position, step.1.position, input_length) {
                    Err(part1_codestream_malformed(step.1.position, crate::MalformedKind::InvalidTilePart))
                } else { part1_layout_continuation(step.1, main, step.2, step.3, input_length) },
            }
        } else if marker == 0xffd9 {
            let finished = part1_finish_tile_part_traversal(reader, tile_parts,
                main.raw.plm_seen, main.raw.plm.len() as usize, main.raw.ppm_fragments,
                main.ppm_frames.len() as usize, main.raw.extensions.lengths.len() as usize);
            match finished.0 {
                Err(error) => Err(error),
                Ok(()) => part1_layout_after_tiles(finished.1, main, tile_parts, state),
            }
        } else { Err(part1_codestream_malformed(reader.position, crate::MalformedKind::InvalidMarkerOrder)) },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_layout_from_main_result<'a>(main: Part1MainHeaderResult<'a>, input_length: usize)
    -> Part1CompleteLayoutResult
{
    match main {
        Err(error) => Err(error),
        Ok(header) => if header.tile_count > usize::MAX {
            Err(part1_codestream_malformed(header.reader.position, crate::MalformedKind::ArithmeticOverflow))
        } else {
            part1_layout_continuation(header.reader, header, 0,
                part1_empty_persistent_tile_state(header.tile_count as usize),
                input_length)
        },
    }
}

pub(crate) open spec fn part1_read_layout(reader: Part1CodestreamReader<'_>) -> Part1CompleteLayoutResult {
    part1_layout_from_main_result(part1_read_main_header(reader),
        part1_parse_layout_prologue(reader).1.input.len() as usize)
}

pub closed spec fn part1_parse_layout(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Part1CompleteLayoutResult
{
    match part1_codestream_reader_new(input, limits) {
        Err(error) => Err(error), Ok(reader) => part1_read_layout(reader),
    }
}

pub closed spec fn part1_parse_info(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<(Part1LayoutMainFields, Part1ProfileMetadata, u32, u64), crate::DecodeError>
{
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error), Ok(layout) => Ok((layout.0, layout.1, layout.2, layout.3)),
    }
}

pub(crate) proof fn part1_parse_layout_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part1_parse_layout(input, limits) == match part1_codestream_reader_new(input, limits) {
        Err(error) => Err(error), Ok(reader) => part1_read_layout(reader),
    },
{
}

pub(crate) proof fn part1_parse_info_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part1_parse_info(input, limits) == match part1_parse_layout(input, limits) {
        Err(error) => Err(error), Ok(layout) => Ok((layout.0, layout.1, layout.2, layout.3)),
    },
{
}

}
