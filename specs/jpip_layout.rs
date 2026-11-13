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

}
