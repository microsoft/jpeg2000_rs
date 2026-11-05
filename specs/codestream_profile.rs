//! Actual profile observation, capability validation and complete metadata Result.

use super::*;

verus! {

pub(crate) type Part1ProfileFlags = (bool, bool, bool);
pub(crate) type Part1ProfileMetadata = (
    u16, crate::codestream::CodestreamBlockCoding, Option<(u32, Seq<u16>)>,
    Option<Seq<u16>>, Option<Seq<u16>>,
);

pub(crate) struct Part1ProfileTile {
    pub styles: (u16, Seq<Part1ParsedCodingStyle>),
    pub roi: Seq<u8>,
    pub has_roi: bool,
    pub has_functional: bool,
}

pub open spec fn part1_profile_advertises_ht(caps: (u32, Seq<u16>)) -> bool {
    caps.0 & 0x00020000u32 != 0
}

pub open spec fn part1_profile_capability_flag(caps: (u32, Seq<u16>), mask: u16) -> bool {
    match part2_capability_value(caps, 15) { None => false, Some(word) => word & mask != 0 }
}

pub(crate) open spec fn part1_profile_error() -> crate::DecodeError {
    part1_codestream_malformed(0, crate::MalformedKind::InvalidProfile)
}

pub(crate) open spec fn part1_profile_observe(style: u8, flags: Part1ProfileFlags)
    -> (Result<(), crate::DecodeError>, Part1ProfileFlags)
{
    match part1_tier1_block_coding_byte(style) {
        Err(_) => (Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidCodingStyle)), flags),
        Ok(crate::tier1::Tier1BlockCoding::Legacy) => (Ok(()), (true, flags.1, flags.2)),
        Ok(crate::tier1::Tier1BlockCoding::HighThroughput) => (Ok(()), (flags.0, true, flags.2)),
        Ok(crate::tier1::Tier1BlockCoding::Mixed) => (Ok(()), (flags.0, flags.1, true)),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_profile_observe_components(
    styles: (u16, Seq<Part1ParsedCodingStyle>), components: u16, current: u16,
    flags: Part1ProfileFlags,
) -> (Result<(), crate::DecodeError>, Part1ProfileFlags)
    decreases components as int - current as int,
{
    if current >= components { (Ok(()), flags) } else {
        match part1_style_owner_lookup(styles, current) {
            Err(error) => (Err(error), flags),
            Ok(style) => {
                let observed = part1_profile_observe(style.code_block_style, flags);
                match observed.0 {
                    Err(error) => (Err(error), observed.1),
                    Ok(()) => part1_profile_observe_components(styles, components, (current + 1) as u16, observed.1),
                }
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_profile_observe_tiles(
    tiles: Seq<Part1ProfileTile>, components: u16, index: nat, flags: Part1ProfileFlags,
) -> (Result<(), crate::DecodeError>, Part1ProfileFlags)
    decreases tiles.len() - index,
{
    if index >= tiles.len() { (Ok(()), flags) } else {
        let observed = part1_profile_observe_components(tiles[index as int].styles, components, 0, flags);
        match observed.0 {
            Err(error) => (Err(error), observed.1),
            Ok(()) => part1_profile_observe_tiles(tiles, components, index + 1, observed.1),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_profile_validate_components(
    caps: (u32, Seq<u16>), styles: (u16, Seq<Part1ParsedCodingStyle>),
    roi: Seq<u8>, components: u16, current: u16, has_roi: bool,
) -> Result<(), crate::DecodeError>
    decreases components as int - current as int,
{
    if current >= components {
        if has_roi && !part1_profile_capability_flag(caps, 0x1000) { Err(part1_profile_error()) }
        else { Ok(()) }
    } else {
        match part1_style_owner_lookup(styles, current) {
            Err(error) => Err(error),
            Ok(style) => match part2_roi_shift(roi, current) {
                Err(error) => Err(error),
                Ok(shift) => match part1_tier1_block_coding_byte(style.code_block_style) {
                    Err(_) => Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidCodingStyle)),
                    Ok(block) => if !part15_component_allowed(
                        part1_profile_capability_flag(caps, 0x1000), has_roi, shift as nat,
                        part1_profile_capability_flag(caps, 0x0020), ht_block_coding_enabled(block),
                        matches!(style.transform, crate::codestream::WaveletTransform::Irreversible9x7),
                    ) { Err(part1_profile_error()) } else {
                        part1_profile_validate_components(caps, styles, roi, components, (current + 1) as u16, has_roi)
                    },
                },
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_profile_validate_tiles(
    caps: (u32, Seq<u16>), tiles: Seq<Part1ProfileTile>, components: u16, index: nat,
) -> Result<(), crate::DecodeError>
    decreases tiles.len() - index,
{
    if index >= tiles.len() { Ok(()) } else {
        let tile = tiles[index as int];
        match part1_profile_validate_components(caps, tile.styles, tile.roi, components, 0, tile.has_roi) {
            Err(error) => Err(error),
            Ok(()) => part1_profile_validate_tiles(caps, tiles, components, index + 1),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_profile_output(
    r_siz: u16, caps: Option<(u32, Seq<u16>)>, profile: Option<Seq<u16>>,
    corresponding: Option<Seq<u16>>, flags: Part1ProfileFlags,
) -> Part1ProfileMetadata {
    let class = part15_codestream_class(flags.0, flags.1, flags.2);
    let block = if class == 2 { crate::codestream::CodestreamBlockCoding::Mixed }
        else if class == 1 { crate::codestream::CodestreamBlockCoding::HighThroughput }
        else { crate::codestream::CodestreamBlockCoding::Legacy };
    (r_siz, block, caps, profile, corresponding)
}

#[verifier::opaque]
pub(crate) open spec fn part1_profile_after_observation(
    r_siz: u16, caps: Option<(u32, Seq<u16>)>, profile: Option<Seq<u16>>,
    corresponding: Option<Seq<u16>>, styles: (u16, Seq<Part1ParsedCodingStyle>),
    roi: Seq<u8>, tiles: Seq<Part1ProfileTile>, components: u16, has_roi: bool,
    flags: Part1ProfileFlags,
) -> Result<Part1ProfileMetadata, crate::DecodeError> {
    let advertised = match caps { None => false, Some(value) => part1_profile_advertises_ht(value) };
    let styles_ht = flags.1 || flags.2;
    let output = part1_profile_output(r_siz, caps, profile, corresponding, flags);
    if !part15_signaling_valid(r_siz & 0x4000u16 != 0, advertised, styles_ht, corresponding.is_some()) {
        Err(part1_profile_error())
    } else if advertised {
        match caps {
            None => Err(part1_profile_error()),
            Some(caps) => match part2_capability_value(caps, 15) {
                None => Err(part1_profile_error()),
                Some(word) => if !part15_capability_fields_valid(
                    (word >> 14) as nat, ((word & 0x07c0u16) >> 6) as nat, (word & 0x1fu16) as nat,
                ) { Err(part1_profile_error()) } else {
                    match part2_capability_block_mode(caps) {
                        None => Err(part1_profile_error()),
                        Some(mode) => {
                            let mode = match mode {
                                crate::codestream::Part15BlockMode::HtOnly => 0nat,
                                crate::codestream::Part15BlockMode::HtDeclared => 2nat,
                                crate::codestream::Part15BlockMode::Mixed => 3nat,
                            };
                            if !part15_mode_allows(mode, flags.0, flags.2)
                                || (!part1_profile_capability_flag(caps, 0x1000)
                                    && (has_roi || exists|index: int| 0 <= index < tiles.len()
                                        && (#[trigger] tiles[index]).has_roi))
                                || !part15_headers_allowed(part1_profile_capability_flag(caps, 0x0800),
                                    exists|index: int| 0 <= index < tiles.len()
                                        && (#[trigger] tiles[index]).has_functional)
                            { Err(part1_profile_error()) } else {
                                match part1_profile_validate_components(caps, styles, roi, components, 0, has_roi) {
                                    Err(error) => Err(error),
                                    Ok(()) => match part1_profile_validate_tiles(caps, tiles, components, 0) {
                                        Err(error) => Err(error), Ok(()) => Ok(output),
                                    },
                                }
                            }
                        },
                    }
                },
            },
        }
    } else if styles_ht { Err(part1_profile_error()) } else { Ok(output) }
}

#[verifier::opaque]
pub(crate) open spec fn part1_classify_codestream_profile(
    r_siz: u16, caps: Option<(u32, Seq<u16>)>, profile: Option<Seq<u16>>,
    corresponding: Option<Seq<u16>>, styles: (u16, Seq<Part1ParsedCodingStyle>),
    roi: Seq<u8>, tiles: Seq<Part1ProfileTile>, components: u16, has_roi: bool,
) -> Result<Part1ProfileMetadata, crate::DecodeError> {
    let main = part1_profile_observe_components(styles, components, 0, (false, false, false));
    match main.0 {
        Err(error) => Err(error),
        Ok(()) => {
            let observed = part1_profile_observe_tiles(tiles, components, 0, main.1);
            match observed.0 {
                Err(error) => Err(error),
                Ok(()) => part1_profile_after_observation(
                    r_siz, caps, profile, corresponding, styles, roi, tiles, components, has_roi, observed.1),
            }
        },
    }
}

}
