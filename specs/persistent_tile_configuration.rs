//! Raw persistent configuration selection and ordered partial commit frames.

use super::*;

verus! {

pub open spec fn part1_inherited_tile_owner<T>(index: usize, main: T, states: Seq<Option<T>>) -> T {
    if (index as int) < states.len() {
        match states[index as int] { Some(owner) => owner, None => main }
    } else { main }
}

pub open spec fn part1_roi_shifts_equal(left: Seq<u8>, right: Seq<u8>) -> bool {
    left == right
}

pub(crate) type Part1PersistentTileConfiguration = (
    Seq<Option<Seq<u8>>>,
    Seq<Option<Part1ParsedCodingStyle>>,
    Seq<Option<Part2Quantization>>,
    Seq<Option<usize>>,
    Seq<Option<(u16, Seq<Part2Quantization>)>>,
    Seq<Option<Seq<crate::codestream::ProgressionChange>>>,
);

pub(crate) type Part1PersistentTileSelection = (
    Seq<Option<Seq<u8>>>, Seq<Option<Part1ParsedCodingStyle>>,
    Seq<Option<Part2Quantization>>, Seq<Option<usize>>, Seq<Part1TilePartPayload>,
);

pub(crate) type Part1InheritedTileConfiguration = (
    Option<Seq<u8>>, Seq<u8>, Part1ParsedCodingStyle, Part2Quantization,
    (u16, Seq<Part1ParsedCodingStyle>),
);

#[verifier::opaque]
pub(crate) open spec fn part1_select_inherited_tile_configuration(
    position: usize, index: usize, main_roi: Seq<u8>, main_style: Part1ParsedCodingStyle,
    main_quantization: Part2Quantization, main_components: (u16, Seq<Part1ParsedCodingStyle>),
    state: Part1PersistentTileSelection,
) -> Result<Part1InheritedTileConfiguration, crate::DecodeError> {
    if index as int >= state.0.len() {
        Err(part1_codestream_malformed(position, crate::MalformedKind::InvalidTilePart))
    } else {
        let previous = state.0[index as int];
        let roi = match previous { Some(value) => value, None => main_roi };
        let style = if (index as int) < state.1.len() {
            match state.1[index as int] { Some(value) => value, None => main_style }
        } else { main_style };
        let quantization = if (index as int) < state.2.len() {
            match state.2[index as int] { Some(value) => value, None => main_quantization }
        } else { main_quantization };
        let part = if (index as int) < state.3.len() { state.3[index as int] } else { None };
        match part {
            None => Ok((previous, roi, style, quantization, main_components)),
            Some(part) => if part as int >= state.4.len() {
                Err(part1_codestream_malformed(position, crate::MalformedKind::InvalidTilePart))
            } else {
                Ok((previous, roi, style, quantization, state.4[part as int].component_coding_styles))
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_persistent_tile_configuration_prefix(
    position: usize, start: usize, index: usize, payload_index: usize,
    previous_roi: Option<Seq<u8>>, payload: Part1TilePartPayload,
    state: Part1PersistentTileConfiguration, count: nat,
) -> (Result<(), crate::DecodeError>, Part1PersistentTileConfiguration)
    decreases count,
{
    if count == 0 {
        if match previous_roi {
            Some(previous) => previous != payload.roi_shifts,
            None => false,
        } {
            (Err(part1_codestream_malformed(start, crate::MalformedKind::InvalidRegionOfInterest)), state)
        } else { (Ok(()), state) }
    } else {
        let prior = part1_persistent_tile_configuration_prefix(
            position, start, index, payload_index, previous_roi, payload, state, (count - 1) as nat);
        match prior.0 {
            Err(error) => (Err(error), prior.1),
            Ok(()) => {
                let raw = prior.1;
                let length = if count == 1 { raw.0.len() }
                    else if count == 2 { raw.1.len() }
                    else if count == 3 { raw.2.len() }
                    else if count == 4 { raw.3.len() }
                    else if count == 5 { raw.4.len() }
                    else { raw.5.len() };
                if index as int >= length {
                    (Err(part1_codestream_malformed(position, crate::MalformedKind::InvalidTilePart)), raw)
                } else {
                    let updated = if count == 1 {
                        (raw.0.update(index as int, Some(payload.roi_shifts)), raw.1, raw.2, raw.3, raw.4, raw.5)
                    } else if count == 2 {
                        (raw.0, raw.1.update(index as int, Some(payload.coding_style)), raw.2, raw.3, raw.4, raw.5)
                    } else if count == 3 {
                        (raw.0, raw.1, raw.2.update(index as int, Some(payload.quantization)), raw.3, raw.4, raw.5)
                    } else if count == 4 {
                        (raw.0, raw.1, raw.2, raw.3.update(index as int, Some(payload_index)), raw.4, raw.5)
                    } else if count == 5 {
                        (raw.0, raw.1, raw.2, raw.3,
                            raw.4.update(index as int, Some(payload.component_quantizations)), raw.5)
                    } else {
                        (raw.0, raw.1, raw.2, raw.3, raw.4,
                            raw.5.update(index as int, Some(payload.progression_changes)))
                    };
                    (Ok(()), updated)
                }
            },
        }
    }
}

pub(crate) open spec fn part1_commit_persistent_tile_configuration(
    position: usize, start: usize, index: usize, payload_index: usize,
    previous_roi: Option<Seq<u8>>, payload: Part1TilePartPayload,
    state: Part1PersistentTileConfiguration,
) -> (Result<(), crate::DecodeError>, Part1PersistentTileConfiguration) {
    part1_persistent_tile_configuration_prefix(
        position, start, index, payload_index, previous_roi, payload, state, 6)
}

}
