//! Complete public JPIP reconstruction from physical cache and caller layout.

use super::*;

verus! {

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
