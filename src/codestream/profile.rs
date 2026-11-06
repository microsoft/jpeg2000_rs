//! Profile markers, extended capabilities and block-coding compatibility.

use super::reader::{read_u16, read_u32};
use super::{
    CodestreamBlockCoding, CodestreamProfile, ComponentCodingStyles, DecodeError,
    ExtendedCapabilities, HT_RSIZ_FLAG, MalformedKind, PART_15_CAPABILITY_FLAG, Parser,
    Part15BlockMode, ProfileNumber, RoiShifts, Segment, Tier1BlockCoding, TilePartPayload,
    WaveletTransform,
};
#[cfg(verus_keep_ghost)]
use super::{
    cap_payload_outcome, codestream_profile_capabilities, complete_codestream_profile_outcome,
    complete_codestream_profile_view, component_coding_style_result, component_style_owner_view,
    extended_capabilities_view, marker_words_outcome, optional_capabilities_view,
    optional_profile_number_view, parsed_coding_style_view, profile_number_outcome,
    profile_number_view, profile_tile_inputs_view, roi_shifts_view, segment_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl ExtendedCapabilities {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == extended_capabilities_view(self).0,
    ))]
    pub const fn p_cap(&self) -> u32 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(extended_capabilities_view); }
        self.p_cap
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == extended_capabilities_view(self).1,
    ))]
    pub fn c_capabilities(&self) -> &[u16] {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(extended_capabilities_view); }
        &self.c_capabilities
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_profile_advertises_ht(extended_capabilities_view(self)),
    ))]
    pub const fn advertises_part15(&self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(extended_capabilities_view); }
        self.p_cap & PART_15_CAPABILITY_FLAG != 0
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_capability_value(extended_capabilities_view(self), 15),
    ))]
    pub fn part15_value(&self) -> Option<u16> {
        self.capability_for_part(15)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_capability_block_mode(extended_capabilities_view(self)),
    ))]
    pub fn part15_block_mode(&self) -> Option<Part15BlockMode> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_capability_block_mode); }
        match self.part15_value()? >> 14 {
            0 => Some(Part15BlockMode::HtOnly),
            2 => Some(Part15BlockMode::HtDeclared),
            3 => Some(Part15BlockMode::Mixed),
            _ => None,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_capability_multiple_sets(extended_capabilities_view(self)),
    ))]
    pub fn part15_allows_multiple_ht_sets(&self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_capability_multiple_sets); }
        matches!(self.part15_value(), Some(value) if value & 0x2000 != 0)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_profile_capability_flag(extended_capabilities_view(self), 0x1000),
    ))]
    pub fn part15_allows_roi(&self) -> bool {
        matches!(self.part15_value(), Some(value) if value & 0x1000 != 0)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_profile_capability_flag(extended_capabilities_view(self), 0x0800),
    ))]
    pub fn part15_allows_heterogeneous_headers(&self) -> bool {
        matches!(self.part15_value(), Some(value) if value & 0x0800 != 0)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_profile_capability_flag(extended_capabilities_view(self), 0x0020),
    ))]
    pub fn part15_allows_irreversible_ht(&self) -> bool {
        matches!(self.part15_value(), Some(value) if value & 0x0020 != 0)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_capability_magnitude_bound(extended_capabilities_view(self)),
    ))]
    pub fn part15_magnitude_bound(&self) -> Option<u8> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_capability_magnitude_bound); }
        let value = self.part15_value()?;
        #[cfg(verus_keep_ghost)]
        proof! { assert(value & 0x1fu16 <= 31u16) by(bit_vector); }
        let parameter = (value & 0x1f) as u8;
        Some(crate::refinement::part15_magnitude_bound(parameter))
    }

    #[allow(clippy::manual_map, clippy::question_mark)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_capability_value(extended_capabilities_view(self), part),
    ))]
    pub fn capability_for_part(&self, part: u8) -> Option<u16> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(extended_capabilities_view); reveal(crate::specs::part2_capability_value); }
        if part == 0 || part > 32 {
            return None;
        }
        let mut index = 0_usize;
        let mut current = 1_u8;
        let mut mask = 0x8000_0000_u32;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant current <= part,
                    part > 0, part <= 32,
                    crate::specs::part2_capability_value(extended_capabilities_view(self), part)
                        == crate::specs::part2_capability_lookup_run(
                            self.p_cap, self.c_capabilities@, part, current, mask, index,
                        ),
                decreases part - current,
            )
        )]
        while current < part {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part2_capability_lookup_run, 1); }
            if self.p_cap & mask != 0 {
                index = match index.checked_add(1) {
                    Some(value) => value,
                    None => return None,
                };
            }
            mask >>= 1;
            current = match current.checked_add(1) {
                Some(value) => value,
                None => return None,
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part2_capability_lookup_run, 1);
            assert(current == part);
        }
        if self.p_cap & mask == 0 {
            return None;
        }
        match self.c_capabilities.get(index) {
            Some(value) => Some(*value),
            None => None,
        }
    }
}
impl ProfileNumber {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == profile_number_view(self),
    ))]
    pub fn words(&self) -> &[u16] {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(profile_number_view); }
        &self.words
    }
}
impl CodestreamProfile {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_profile_optional_advertises_ht(codestream_profile_capabilities(self)),
    ))]
    pub fn is_part15(&self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(codestream_profile_capabilities); }
        match self.extended_capabilities.as_ref() {
            Some(capabilities) => capabilities.advertises_part15(),
            None => false,
        }
    }

    pub const fn uses_high_throughput(&self) -> bool {
        !matches!(self.block_coding, CodestreamBlockCoding::Legacy)
    }

    pub const fn extended_capabilities(&self) -> Option<&ExtendedCapabilities> {
        self.extended_capabilities.as_ref()
    }

    pub const fn profile(&self) -> Option<&ProfileNumber> {
        self.profile.as_ref()
    }

    pub const fn corresponding_profile(&self) -> Option<&ProfileNumber> {
        self.corresponding_profile.as_ref()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_profile_multiple_sets(codestream_profile_capabilities(self)),
    ))]
    pub fn part15_allows_multiple_ht_sets(&self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(codestream_profile_capabilities); reveal(crate::specs::part2_profile_multiple_sets); }
        match self.extended_capabilities.as_ref() {
            Some(capabilities) => capabilities.part15_allows_multiple_ht_sets(),
            None => false,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_profile_magnitude_bound(codestream_profile_capabilities(self)),
    ))]
    pub fn part15_magnitude_bound(&self) -> u8 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(codestream_profile_capabilities); reveal(crate::specs::part2_profile_magnitude_bound); }
        match self.extended_capabilities.as_ref() {
            None => 74,
            Some(capabilities) => capabilities.part15_magnitude_bound().unwrap_or(74),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_profile_force_ht(codestream_profile_capabilities(self)),
    ))]
    pub fn part15_requires_all_ht_blocks(&self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(codestream_profile_capabilities); reveal(crate::specs::part2_profile_force_ht); }
        match self.extended_capabilities.as_ref() {
            None => false,
            Some(capabilities) => matches!(
                capabilities.part15_block_mode(),
                Some(Part15BlockMode::HtOnly)
            ),
        }
    }
}
impl<'a> Parser<'a> {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures cap_payload_outcome(result) == crate::specs::part1_parse_cap(segment_view(segment)),
    ))]
    pub(super) fn parse_cap(
        &self,
        segment: Segment<'a>,
    ) -> Result<ExtendedCapabilities, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_parse_cap); reveal(extended_capabilities_view); }
        if segment.payload.len() < 4 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let p_cap = read_u32([
            segment.payload[0],
            segment.payload[1],
            segment.payload[2],
            segment.payload[3],
        ]);
        if p_cap == 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidProfile));
        }
        let capability_count = count_set_bits(p_cap);
        let expected_length = crate::refinement::part15_cap_payload_length(capability_count);
        if segment.payload.len() != expected_length {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let c_capabilities = self.read_marker_words(segment, 4)?;
        Ok(ExtendedCapabilities {
            p_cap,
            c_capabilities,
        })
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures profile_number_outcome(result) == crate::specs::part1_parse_profile_number(segment_view(segment)),
    ))]
    pub(super) fn parse_profile_number(
        &self,
        segment: Segment<'a>,
    ) -> Result<ProfileNumber, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_parse_profile_number); reveal(profile_number_view); }
        let remainder = segment.payload.len() % 2;
        if segment.payload.len() < 2 || remainder != 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let words = self.read_marker_words(segment, 0)?;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_marker_words); }
        if matches!(words.last(), Some(value) if *value == 0) {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidProfile));
        }
        Ok(ProfileNumber { words })
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures marker_words_outcome(result) == crate::specs::part1_marker_words(segment_view(segment), start),
    ))]
    pub(super) fn read_marker_words(
        &self,
        segment: Segment<'a>,
        start: usize,
    ) -> Result<Vec<u16>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_marker_words); }
        if start > segment.payload.len() {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let mut words = Vec::with_capacity((segment.payload.len() - start) / 2);
        let mut position = start;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    start <= position <= segment.payload.len(),
                    (position - start) % 2 == 0,
                    words@ == crate::specs::part1_marker_word_sequence(
                        segment.payload@.subrange(start as int, position as int)),
                decreases segment.payload.len() - position,
            )
        )]
        while position < segment.payload.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part1_segment_byte);
                reveal(crate::specs::part1_marker_words);
            }
            let next = match position.checked_add(1) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
            let first = self.segment_byte(segment, position, 0)?;
            let second = match self.segment_byte(segment, next, 0) {
                Ok(value) => value,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(next == segment.payload.len());
                        assert((segment.payload.len() - start) % 2 == 1);
                    }
                    return Err(error);
                }
            };
            words.push(read_u16([first, second]));
            let next_position = match position.checked_add(2) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                let raw = segment.payload@;
                let previous = crate::specs::part1_marker_word_sequence(raw.subrange(start as int, position as int));
                let next_words = crate::specs::part1_marker_word_sequence(raw.subrange(start as int, next_position as int));
                assert(next_words =~= previous.push(crate::specs::part1_marker_value(raw[position as int], raw[position as int + 1]))) by {
                    assert forall|index: int| 0 <= index < next_words.len() implies
                        next_words[index] == previous.push(crate::specs::part1_marker_value(raw[position as int], raw[position as int + 1]))[index] by {
                        if index >= previous.len() { assert(2 * index == position - start); }
                    };
                }
            }
            position = next_position;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(segment.payload@.subrange(start as int, position as int)
                =~= segment.payload@.subrange(start as int, segment.payload.len() as int));
        }
        Ok(words)
    }
}
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures complete_codestream_profile_outcome(result)
        == crate::specs::part1_classify_codestream_profile(
            r_siz, optional_capabilities_view(&extended_capabilities),
            optional_profile_number_view(&profile), optional_profile_number_view(&corresponding_profile),
            component_style_owner_view(main_styles), roi_shifts_view(main_roi_shifts),
            profile_tile_inputs_view(tile_parts@), components, main_has_roi_marker),
))]
pub(super) fn classify_codestream_profile(
    r_siz: u16,
    extended_capabilities: Option<ExtendedCapabilities>,
    profile: Option<ProfileNumber>,
    corresponding_profile: Option<ProfileNumber>,
    main_styles: &ComponentCodingStyles,
    main_roi_shifts: &RoiShifts,
    tile_parts: &[TilePartPayload<'_>],
    components: u16,
    main_has_roi_marker: bool,
) -> Result<CodestreamProfile, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_classify_codestream_profile);
        reveal(crate::specs::part1_profile_after_observation);
        reveal(complete_codestream_profile_outcome);
        reveal(complete_codestream_profile_view);
        reveal(optional_capabilities_view);
        reveal(optional_profile_number_view);
        reveal(profile_tile_inputs_view);
        reveal(component_coding_style_result);
        reveal(component_style_owner_view);
        reveal(parsed_coding_style_view);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost main_observed = crate::specs::part1_profile_observe_components(
            component_style_owner_view(main_styles), components, 0, (false, false, false));
    }
    let mut has_legacy = false;
    let mut has_ht_only = false;
    let mut has_mixed = false;
    let mut component = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component <= components,
                main_observed == crate::specs::part1_profile_observe_components(
                    component_style_owner_view(main_styles), components, 0, (false, false, false)),
                main_observed == crate::specs::part1_profile_observe_components(
                    component_style_owner_view(main_styles), components, component,
                    (has_legacy, has_ht_only, has_mixed)),
            decreases components - component,
        )
    )]
    while component < components {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_classify_codestream_profile);
            reveal(complete_codestream_profile_outcome);
            reveal(component_coding_style_result);
            reveal(component_style_owner_view);
            reveal(parsed_coding_style_view);
            reveal_with_fuel(crate::specs::part1_profile_observe_components, 1);
            reveal(crate::specs::part1_style_owner_lookup);
        }
        observe_block_coding(
            main_styles.style(component)?.code_block_style,
            &mut has_legacy,
            &mut has_ht_only,
            &mut has_mixed,
        )?;
        component = component
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part1_profile_observe_components, 1);
        assert(main_observed == (Ok(()), (has_legacy, has_ht_only, has_mixed)));
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost tiles_observed = crate::specs::part1_profile_observe_tiles(
            profile_tile_inputs_view(tile_parts@), components, 0, (has_legacy, has_ht_only, has_mixed));
    }
    let mut tile_part_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant tile_part_index <= tile_parts.len(),
                main_observed == crate::specs::part1_profile_observe_components(
                    component_style_owner_view(main_styles), components, 0, (false, false, false)),
                main_observed.0 == Ok(()),
                tiles_observed == crate::specs::part1_profile_observe_tiles(
                    profile_tile_inputs_view(tile_parts@), components, 0, main_observed.1),
                tiles_observed == crate::specs::part1_profile_observe_tiles(
                    profile_tile_inputs_view(tile_parts@), components, tile_part_index as nat,
                    (has_legacy, has_ht_only, has_mixed)),
            decreases tile_parts.len() - tile_part_index,
        )
    )]
    while tile_part_index < tile_parts.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_classify_codestream_profile);
            reveal(complete_codestream_profile_outcome);
            reveal(profile_tile_inputs_view);
            reveal_with_fuel(crate::specs::part1_profile_observe_tiles, 1);
        }
        let tile_part = tile_parts
            .get(tile_part_index)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        component = 0;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost starting_tile_flags = (has_legacy, has_ht_only, has_mixed);
            let ghost tile_observed = crate::specs::part1_profile_observe_components(
                component_style_owner_view(&tile_part.component_coding_styles), components, 0,
                (has_legacy, has_ht_only, has_mixed));
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant component <= components,
                    tile_part_index < tile_parts.len(),
                    *tile_part == tile_parts@[tile_part_index as int],
                    main_observed == crate::specs::part1_profile_observe_components(
                        component_style_owner_view(main_styles), components, 0, (false, false, false)),
                    main_observed.0 == Ok(()),
                    tiles_observed == crate::specs::part1_profile_observe_tiles(
                        profile_tile_inputs_view(tile_parts@), components, 0, main_observed.1),
                    tiles_observed == crate::specs::part1_profile_observe_tiles(
                        profile_tile_inputs_view(tile_parts@), components, tile_part_index as nat, starting_tile_flags),
                    tile_observed == crate::specs::part1_profile_observe_components(
                        component_style_owner_view(&tile_part.component_coding_styles), components, 0, starting_tile_flags),
                    tile_observed == crate::specs::part1_profile_observe_components(
                        component_style_owner_view(&tile_part.component_coding_styles), components, component,
                        (has_legacy, has_ht_only, has_mixed)),
                decreases components - component,
            )
        )]
        while component < components {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part1_classify_codestream_profile);
                reveal(complete_codestream_profile_outcome);
                reveal(profile_tile_inputs_view);
                reveal(component_coding_style_result);
                reveal(component_style_owner_view);
                reveal(parsed_coding_style_view);
                reveal_with_fuel(crate::specs::part1_profile_observe_tiles, 1);
                reveal_with_fuel(crate::specs::part1_profile_observe_components, 1);
                reveal(crate::specs::part1_style_owner_lookup);
            }
            observe_block_coding(
                tile_part
                    .component_coding_styles
                    .style(component)?
                    .code_block_style,
                &mut has_legacy,
                &mut has_ht_only,
                &mut has_mixed,
            )?;
            component = component
                .checked_add(1)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_profile_observe_components, 1);
            assert(tile_observed == (Ok(()), (has_legacy, has_ht_only, has_mixed)));
        }
        tile_part_index = tile_part_index
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part1_profile_observe_tiles, 1);
        assert(tiles_observed == (Ok(()), (has_legacy, has_ht_only, has_mixed)));
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost classification_goal = crate::specs::part1_classify_codestream_profile(
            r_siz, optional_capabilities_view(&extended_capabilities),
            optional_profile_number_view(&profile), optional_profile_number_view(&corresponding_profile),
            component_style_owner_view(main_styles), roi_shifts_view(main_roi_shifts),
            profile_tile_inputs_view(tile_parts@), components, main_has_roi_marker);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(classification_goal == crate::specs::part1_profile_after_observation(
            r_siz, optional_capabilities_view(&extended_capabilities),
            optional_profile_number_view(&profile), optional_profile_number_view(&corresponding_profile),
            component_style_owner_view(main_styles), roi_shifts_view(main_roi_shifts),
            profile_tile_inputs_view(tile_parts@), components, main_has_roi_marker,
            (has_legacy, has_ht_only, has_mixed)));
    }

    let cap_part15 = match &extended_capabilities {
        Some(capabilities) => capabilities.advertises_part15(),
        None => false,
    };
    let r_siz_part15 = r_siz & HT_RSIZ_FLAG != 0;
    let styles_part15 = has_ht_only || has_mixed;
    if !crate::refinement::part15_signaling_valid(
        r_siz_part15,
        cap_part15,
        styles_part15,
        corresponding_profile.is_some(),
    ) {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    if cap_part15 {
        let capabilities = extended_capabilities.as_ref().ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_profile_error(),
                ))]
            || DecodeError::malformed(0, MalformedKind::InvalidProfile),
        )?;
        let value = capabilities.part15_value().ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_profile_error(),
                ))]
            || DecodeError::malformed(0, MalformedKind::InvalidProfile),
        )?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((value >> 14u16) <= 3u16) by(bit_vector);
            assert(((value & 0x07c0u16) >> 6u16) <= 31u16) by(bit_vector);
        }
        if !crate::refinement::part15_capability_fields_valid(
            (value >> 14) as u8,
            ((value & 0x07c0) >> 6) as u8,
            (value & 0x1f) as u8,
        ) {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
        }
        let block_mode = capabilities.part15_block_mode().ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_profile_error(),
                ))]
            || DecodeError::malformed(0, MalformedKind::InvalidProfile),
        )?;
        let mode = match block_mode {
            Part15BlockMode::HtOnly => 0,
            Part15BlockMode::HtDeclared => 2,
            Part15BlockMode::Mixed => 3,
        };
        if !crate::refinement::part15_mode_allows(mode, has_legacy, has_mixed) {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(profile_tile_inputs_view);
            assert(tile_parts@.as_ref().len() == tile_parts.len());
            assert forall|index: int| 0 <= index < tile_parts.len() implies
                (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_roi
                    == tile_parts@.as_ref()[index].has_roi_marker
                && profile_tile_inputs_view(tile_parts@)[index].has_functional
                    == tile_parts@.as_ref()[index].has_functional_header_marker by {
                tile_parts@.lemma_as_ref_index(index);
            }
            assert((exists|index: int| 0 <= index < tile_parts.len()
                && tile_parts@.as_ref()[index].has_roi_marker)
                == (exists|index: int| 0 <= index < tile_parts.len()
                    && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_roi)) by {
                if exists|index: int| 0 <= index < tile_parts.len()
                    && tile_parts@.as_ref()[index].has_roi_marker {
                    let index = choose|index: int| 0 <= index < tile_parts.len()
                        && tile_parts@.as_ref()[index].has_roi_marker;
                    assert(profile_tile_inputs_view(tile_parts@)[index].has_roi);
                }
                if exists|index: int| 0 <= index < tile_parts.len()
                    && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_roi {
                    let index = choose|index: int| 0 <= index < tile_parts.len()
                        && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_roi;
                    assert(tile_parts@.as_ref()[index].has_roi_marker);
                }
            }
            assert((exists|index: int| 0 <= index < tile_parts.len()
                && tile_parts@.as_ref()[index].has_functional_header_marker)
                == (exists|index: int| 0 <= index < tile_parts.len()
                    && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_functional)) by {
                if exists|index: int| 0 <= index < tile_parts.len()
                    && tile_parts@.as_ref()[index].has_functional_header_marker {
                    let index = choose|index: int| 0 <= index < tile_parts.len()
                        && tile_parts@.as_ref()[index].has_functional_header_marker;
                    assert(profile_tile_inputs_view(tile_parts@)[index].has_functional);
                }
                if exists|index: int| 0 <= index < tile_parts.len()
                    && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_functional {
                    let index = choose|index: int| 0 <= index < tile_parts.len()
                        && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_functional;
                    assert(tile_parts@.as_ref()[index].has_functional_header_marker);
                }
            }
        }
        if !capabilities.part15_allows_roi()
            && (main_has_roi_marker
                || tile_parts.iter().any(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: bool =>
                    ensures result == part.has_roi_marker,
                ))]
                    |part| part.has_roi_marker,
                ))
        {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
        }
        if !crate::refinement::part15_headers_allowed(
            capabilities.part15_allows_heterogeneous_headers(),
            tile_parts.iter().any(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: bool =>
                        ensures result == part.has_functional_header_marker,
                    ))]
                |part| part.has_functional_header_marker,
            ),
        ) {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_profile_capability_flag(
                extended_capabilities_view(capabilities), 0x1000)
                || (!main_has_roi_marker && !(exists|index: int| 0 <= index < tile_parts.len()
                    && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_roi))) by {
                if !crate::specs::part1_profile_capability_flag(extended_capabilities_view(capabilities), 0x1000) {
                    assert(!main_has_roi_marker);
                    if exists|index: int| 0 <= index < tile_parts.len()
                        && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_roi {
                        let index = choose|index: int| 0 <= index < tile_parts.len()
                            && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_roi;
                        assert(tile_parts@.as_ref()[index].has_roi_marker);
                        assert(false);
                    }
                }
            }
            assert(crate::specs::part1_profile_capability_flag(
                extended_capabilities_view(capabilities), 0x0800)
                || !(exists|index: int| 0 <= index < tile_parts.len()
                    && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_functional)) by {
                if !crate::specs::part1_profile_capability_flag(extended_capabilities_view(capabilities), 0x0800) {
                    if exists|index: int| 0 <= index < tile_parts.len()
                        && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_functional {
                        let index = choose|index: int| 0 <= index < tile_parts.len()
                            && (#[trigger] profile_tile_inputs_view(tile_parts@)[index]).has_functional;
                        assert(tile_parts@.as_ref()[index].has_functional_header_marker);
                        assert(false);
                    }
                }
            }
            reveal(crate::specs::part1_profile_after_observation);
            assert(((value >> 14) as u8) as u16 == value >> 14) by(bit_vector);
            assert((((value & 0x07c0u16) >> 6) as u8) as u16 == (value & 0x07c0u16) >> 6) by(bit_vector);
            assert(((value & 0x1fu16) as u8) as u16 == value & 0x1fu16) by(bit_vector);
            assert(classification_goal == match crate::specs::part1_profile_validate_components(
                extended_capabilities_view(capabilities), component_style_owner_view(main_styles),
                roi_shifts_view(main_roi_shifts), components, 0, main_has_roi_marker) {
                    Err(error) => Err(error),
                    Ok(()) => match crate::specs::part1_profile_validate_tiles(
                        extended_capabilities_view(capabilities), profile_tile_inputs_view(tile_parts@), components, 0) {
                            Err(error) => Err(error),
                            Ok(()) => Ok(crate::specs::part1_profile_output(
                                r_siz, optional_capabilities_view(&extended_capabilities),
                                optional_profile_number_view(&profile), optional_profile_number_view(&corresponding_profile),
                                (has_legacy, has_ht_only, has_mixed))),
                        },
                });
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost validated_main = crate::specs::part1_profile_validate_components(
                extended_capabilities_view(capabilities), component_style_owner_view(main_styles),
                roi_shifts_view(main_roi_shifts), components, 0, main_has_roi_marker);
        }
        validate_part15_component_capabilities(
            capabilities,
            main_styles,
            main_roi_shifts,
            components,
            main_has_roi_marker,
        )?;
        #[cfg(verus_keep_ghost)]
        proof! { assert(validated_main == Ok(())); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost validated_tiles = crate::specs::part1_profile_validate_tiles(
                extended_capabilities_view(capabilities), profile_tile_inputs_view(tile_parts@), components, 0);
            let ghost successful_output = crate::specs::part1_profile_output(
                r_siz, optional_capabilities_view(&extended_capabilities),
                optional_profile_number_view(&profile), optional_profile_number_view(&corresponding_profile),
                (has_legacy, has_ht_only, has_mixed));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(classification_goal == match validated_tiles {
                Err(error) => Err(error), Ok(()) => Ok(successful_output),
            });
        }
        let mut tile_part_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile_part_index <= tile_parts.len(),
                    classification_goal == crate::specs::part1_classify_codestream_profile(
                        r_siz, optional_capabilities_view(&extended_capabilities),
                        optional_profile_number_view(&profile), optional_profile_number_view(&corresponding_profile),
                        component_style_owner_view(main_styles), roi_shifts_view(main_roi_shifts),
                        profile_tile_inputs_view(tile_parts@), components, main_has_roi_marker),
                    classification_goal == match validated_tiles {
                        Err(error) => Err(error), Ok(()) => Ok(successful_output),
                    },
                    successful_output == crate::specs::part1_profile_output(
                        r_siz, optional_capabilities_view(&extended_capabilities),
                        optional_profile_number_view(&profile), optional_profile_number_view(&corresponding_profile),
                        (has_legacy, has_ht_only, has_mixed)),
                    validated_tiles == crate::specs::part1_profile_validate_tiles(
                        extended_capabilities_view(capabilities), profile_tile_inputs_view(tile_parts@), components, 0),
                    validated_tiles == crate::specs::part1_profile_validate_tiles(
                        extended_capabilities_view(capabilities), profile_tile_inputs_view(tile_parts@),
                        components, tile_part_index as nat),
                decreases tile_parts.len() - tile_part_index,
            )
        )]
        while tile_part_index < tile_parts.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(complete_codestream_profile_outcome);
                reveal(profile_tile_inputs_view);
                reveal_with_fuel(crate::specs::part1_profile_validate_tiles, 1);
            }
            let tile_part = tile_parts
                .get(tile_part_index)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            validate_part15_component_capabilities(
                capabilities,
                &tile_part.component_coding_styles,
                &tile_part.roi_shifts,
                components,
                tile_part.has_roi_marker,
            )?;
            tile_part_index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_profile_validate_tiles, 1);
            assert(validated_tiles == Ok(()));
        }
    } else if styles_part15 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    let block_coding =
        match crate::refinement::part15_codestream_class(has_legacy, has_ht_only, has_mixed) {
            2 => CodestreamBlockCoding::Mixed,
            1 => CodestreamBlockCoding::HighThroughput,
            _ => CodestreamBlockCoding::Legacy,
        };
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_profile_output);
        reveal(complete_codestream_profile_outcome);
        reveal(complete_codestream_profile_view);
    }
    Ok(CodestreamProfile {
        r_siz,
        block_coding,
        extended_capabilities,
        profile,
        corresponding_profile,
    })
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_profile_validate_components(
        extended_capabilities_view(capabilities), component_style_owner_view(styles),
        roi_shifts_view(roi_shifts), components, 0, has_roi_marker),
))]
fn validate_part15_component_capabilities(
    capabilities: &ExtendedCapabilities,
    styles: &ComponentCodingStyles,
    roi_shifts: &RoiShifts,
    components: u16,
    has_roi_marker: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(component_coding_style_result);
        reveal(component_style_owner_view);
        reveal(parsed_coding_style_view);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost goal = crate::specs::part1_profile_validate_components(
            extended_capabilities_view(capabilities), component_style_owner_view(styles),
            roi_shifts_view(roi_shifts), components, 0, has_roi_marker);
    }
    let mut component = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component <= components,
                goal == crate::specs::part1_profile_validate_components(
                    extended_capabilities_view(capabilities), component_style_owner_view(styles),
                    roi_shifts_view(roi_shifts), components, 0, has_roi_marker),
                goal == crate::specs::part1_profile_validate_components(
                    extended_capabilities_view(capabilities), component_style_owner_view(styles),
                    roi_shifts_view(roi_shifts), components, component, has_roi_marker),
            decreases components - component,
        )
    )]
    while component < components {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(component_coding_style_result);
            reveal(component_style_owner_view);
            reveal(parsed_coding_style_view);
            reveal_with_fuel(crate::specs::part1_profile_validate_components, 1);
            reveal(crate::specs::part1_style_owner_lookup);
        }
        let style = styles.style(component)?;
        let roi_shift = roi_shifts.shift(component)?;
        let block_coding = crate::tier1::tier1_block_coding_from_code_block_style(style.code_block_style)
            .map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(0, MalformedKind::InvalidCodingStyle),
                ))]
                |_coding_error| DecodeError::malformed(0, MalformedKind::InvalidCodingStyle),
            )?;
        if !crate::refinement::part15_component_allowed(
            capabilities.part15_allows_roi(),
            has_roi_marker,
            roi_shift,
            capabilities.part15_allows_irreversible_ht(),
            block_coding.uses_high_throughput(),
            matches!(style.transform, WaveletTransform::Irreversible9x7),
        ) {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
        }
        component = component
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(component == components);
        reveal_with_fuel(crate::specs::part1_profile_validate_components, 1);
    }
    if has_roi_marker && !capabilities.part15_allows_roi() {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    Ok(())
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, (*final(has_legacy), *final(has_ht_only), *final(has_mixed)))
        == crate::specs::part1_profile_observe(style, (*old(has_legacy), *old(has_ht_only), *old(has_mixed))),
))]
fn observe_block_coding(
    style: u8,
    has_legacy: &mut bool,
    has_ht_only: &mut bool,
    has_mixed: &mut bool,
) -> Result<(), DecodeError> {
    match crate::tier1::tier1_block_coding_from_code_block_style(style) {
        Ok(Tier1BlockCoding::Legacy) => *has_legacy = true,
        Ok(Tier1BlockCoding::HighThroughput) => *has_ht_only = true,
        Ok(Tier1BlockCoding::Mixed) => *has_mixed = true,
        Err(_) => return Err(DecodeError::malformed(0, MalformedKind::InvalidCodingStyle)),
    }
    Ok(())
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result as nat == crate::specs::part1_set_bits_prefix(value, 32),
        result <= 32,
))]
pub(super) fn count_set_bits(value: u32) -> u8 {
    let mut count = 0_u8;
    let mut bit = 0_u8;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant bit <= 32, count <= bit,
                count as nat == crate::specs::part1_set_bits_prefix(value, bit as nat),
            decreases 32 - bit,
        )
    )]
    while bit < 32 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_set_bits_prefix, 1); }
        if value & (1_u32 << u32::from(bit)) != 0 {
            count = match count.checked_add(1) {
                Some(value) => value,
                None => return count,
            };
        }

        bit += 1;
    }

    count
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_maximum_u32_for_bits(bits),
))]
pub(super) fn maximum_u32_for_bits(bits: u8) -> Result<u32, DecodeError> {
    if bits == 0 || bits > 31 {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        });
    }
    let mut value = 0_u32;
    let mut bit = 0_u8;
    #[cfg(verus_keep_ghost)]
    proof! { assert((1u64 << 0u8) == 1u64) by (bit_vector); }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant bit <= bits, 0 < bits <= 31,
                value as u64 == (1u64 << bit) - 1,
            decreases bits - bit,
        )
    )]
    while bit < bits {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(bit < 31 ==> (1u64 << bit) - 1 <= 1073741823u64) by (bit_vector);
            assert(bit < 31 ==> ((1u64 << bit) - 1) * 2 + 1 == (1u64 << (bit + 1)) - 1) by (bit_vector);
        }
        let doubled = match value.checked_mul(2) {
            Some(value) => value,
            None => {
                return Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::ArithmeticOverflow,
                });
            }
        };
        value = match doubled.checked_add(1) {
            Some(value) => value,
            None => {
                return Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::ArithmeticOverflow,
                });
            }
        };
        bit = match bit.checked_add(1) {
            Some(value) => value,
            None => {
                return Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::ArithmeticOverflow,
                });
            }
        };
    }
    Ok(value)
}
