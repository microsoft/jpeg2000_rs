//! Raw container and codestream-info composition with native validation order.

use super::*;

verus! {

pub(crate) type Part2RawCodestreamInfo = (Part1LayoutMainFields, Part1ProfileMetadata, u32, u64);
pub(crate) type Part2RawInspectedContainer = (Part2RawJp2File, Seq<Part2RawCodestreamInfo>);

pub(crate) open spec fn part2_inspection_count(file: Part2RawJp2File, display_first: bool) -> nat {
    if display_first && part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JP2_BRAND)
        && !part2_file_type_jpx(file.file_type)
        && !part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JPH_BRAND) {
        if file.streams.len() > 0 { 1 } else { 0 }
    } else { file.streams.len() }
}

pub(crate) open spec fn part2_validate_jp2_display_profile(file: Part2RawJp2File)
    -> Result<(), crate::DecodeError>
{
    if !part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JP2_BRAND)
        || file.streams.len() == 0 || (part2_file_type_jpx(file.file_type) && file.streams.len() != 1) {
        Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
    } else { Ok(()) }
}

pub(crate) open spec fn part2_inspected_header(
    file: Part2RawJp2File, index: usize, info: Part2RawCodestreamInfo,
) -> Result<(), crate::DecodeError> {
    let stream = file.streams[index as int];
    if part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JPH_BRAND)
        != part1_profile_optional_advertises_ht(info.1.2) {
        Err(part2_container_error(stream.0.1, crate::MalformedKind::InvalidProfile))
    } else {
        let header = match stream.2 {
            Some(association) => association.2,
            None => if index == 0 { Some(file.header) } else { None },
        };
        match header {
            None => Ok(()),
            Some(header) => part2_validate_selected_header(header.image,
                info.0.image_size.geometry.0, info.0.image_size.geometry.1, info.0.image_size.components,
                info.0.image_size.uniform_bit_depth, info.0.image_size.uniform_signed, stream.0.1),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_inspected_codestreams(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, index: usize, infos: Seq<Part2RawCodestreamInfo>,
    display_first: bool,
) -> Result<Part2RawInspectedContainer, crate::DecodeError>
    decreases file.streams.len() as int - index as int,
{
    if index >= part2_inspection_count(file, display_first) { Ok((file, infos)) }
    else {
        match part1_parse_info(file.streams[index as int].1, limits) {
            Err(error) => Err(error),
            Ok(info) => match part2_inspected_header(file, index, info) {
                Err(error) => Err(error),
                Ok(()) => if index == usize::MAX {
                    Err(part2_container_error(0, crate::MalformedKind::ArithmeticOverflow))
                } else {
                    part2_inspected_codestreams(file, limits, (index + 1) as usize, infos.push(info), display_first)
                },
            },
        }
    }
}

#[verifier::opaque]
pub closed spec fn part2_parse_and_inspect_container(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<Part2RawInspectedContainer, crate::DecodeError>
{
    part2_parse_and_inspect_container_mode(input, limits, false)
}

#[verifier::opaque]
pub closed spec fn part2_parse_and_inspect_container_mode(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool,
) -> Result<Part2RawInspectedContainer, crate::DecodeError>
{
    match part2_parse_container(input, *limits) {
        Err(error) => Err(error),
        Ok(file) => part2_inspected_codestreams(file, limits, 0, Seq::empty(), display_first),
    }
}

#[verifier::opaque]
pub closed spec fn part2_inspect_jph_container(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<Part2RawInspectedContainer, crate::DecodeError>
{
    match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => if part2_file_type_compatible(inspected.0.file_type, crate::jp2::BoxType::JPH_BRAND) {
            Ok(inspected)
        } else { Err(part2_container_error(0, crate::MalformedKind::InvalidProfile)) },
    }
}

pub(crate) proof fn part2_parse_and_inspect_container_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_parse_and_inspect_container(input, limits)
        == part2_parse_and_inspect_container_mode(input, limits, false),
        part2_parse_and_inspect_container(input, limits) == match part2_parse_container(input, *limits) {
        Err(error) => Err(error),
        Ok(file) => part2_inspected_codestreams(file, limits, 0, Seq::empty(), false),
    },
{
    reveal(part2_parse_and_inspect_container);
    reveal(part2_parse_and_inspect_container_mode);
}

pub(crate) proof fn part2_parse_and_inspect_container_mode_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool,
)
    ensures part2_parse_and_inspect_container_mode(input, limits, display_first)
        == match part2_parse_container(input, *limits) {
            Err(error) => Err(error),
            Ok(file) => part2_inspected_codestreams(file, limits, 0, Seq::empty(), display_first),
        },
{
    reveal(part2_parse_and_inspect_container_mode);
}

pub(crate) proof fn part2_inspect_jph_container_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_inspect_jph_container(input, limits) == match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => if part2_file_type_compatible(inspected.0.file_type, crate::jp2::BoxType::JPH_BRAND) {
            Ok(inspected)
        } else { Err(part2_container_error(0, crate::MalformedKind::InvalidProfile)) },
    },
{
    reveal(part2_inspect_jph_container);
}

}
