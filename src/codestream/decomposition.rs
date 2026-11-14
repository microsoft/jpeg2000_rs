//! Part 2 decomposition marker decoding and coding-style resolution.

use super::mct_copy::reserve_values;
use super::reader::read_u16;
use super::{
    ArbitraryDecomposition, CodingStyle, ComponentCodingStyles, DecodeError,
    DecompositionDirection, DecompositionStructure, MalformedKind, Parser, Part2Extensions,
    Segment,
};
use super::{FreshPart2Path, MctCopyPath};
#[cfg(verus_keep_ghost)]
use super::{
    ads_payload_outcome, component_style_owner_view, dfs_payload_outcome,
    owned_arbitrary_decomposition_view, owned_decomposition_view, owned_extensions_view,
    parsed_coding_style_outcome, parsed_coding_style_view, parser_view, segment_view,
    two_bit_values_outcome,
};
#[cfg(verus_keep_ghost)]
use crate::specs::{Part2FreshInput, Part2FreshKind, Part2FreshValue};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures parsed_coding_style_outcome(result) == crate::specs::part1_resolve_decomposition_style(
        parsed_coding_style_view(style), owned_extensions_view(extensions)),
))]
pub(super) fn resolve_decomposition_style(
    style: CodingStyle,
    extensions: &Part2Extensions,
) -> Result<CodingStyle, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = parsed_coding_style_view(style);
        let ghost goal = crate::specs::part1_resolve_decomposition_style(initial, owned_extensions_view(extensions));
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_resolve_decomposition_style); }
    let Some(index) = style.decomposition_structure else {
        return Ok(style);
    };
    let Some(structure) = extensions.decomposition_structure(index) else {
        let decomposition = match extensions.arbitrary_decomposition(index) {
            Some(value) => value,
            None => {
                return Err(DecodeError::malformed(
                    0,
                    MalformedKind::MissingRequiredStructure,
                ));
            }
        };
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= decomposition.sublevel_depths.len(),
                initial == parsed_coding_style_view(style),
                goal == crate::specs::part1_resolve_decomposition_style(initial, owned_extensions_view(extensions)),
                goal == if crate::specs::part1_ads_depths_valid(decomposition.sublevel_depths@, position as nat) {
                    Ok(initial)
                } else { Err(crate::specs::part1_codestream_malformed(0, MalformedKind::InvalidCodingStyle)) },
            decreases decomposition.sublevel_depths.len() - position,
        ))]
        while position < decomposition.sublevel_depths.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_ads_depths_valid, 1); }
            let depth = decomposition.sublevel_depths[position];
            if depth == 0 || depth > 3 {
                return Err(DecodeError::malformed(0, MalformedKind::InvalidCodingStyle));
            }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_ads_depths_valid, 1); }
        return Ok(style);
    };
    if structure.directions.is_empty() {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidCodingStyle));
    }
    let mut resolved = style;
    let mut stage = 0_u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant stage <= style.decomposition_levels,
            initial == parsed_coding_style_view(style),
            structure.directions.len() > 0,
            goal == crate::specs::part1_resolve_decomposition_style(initial, owned_extensions_view(extensions)),
            goal == crate::specs::part1_decomposition_directions_from(
                parsed_coding_style_view(resolved), structure.directions@, stage as nat),
            resolved.decomposition_levels == style.decomposition_levels,
        decreases style.decomposition_levels - stage,
    ))]
    while stage < style.decomposition_levels {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_decomposition_directions_from, 1); }
        let requested = usize::from(stage);
        let direction_index = requested.min(structure.directions.len() - 1);
        let direction = structure.directions[direction_index];
        if requested >= resolved.decomposition_directions.len() {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodingStyle));
        }
        resolved.decomposition_directions[requested] = direction;
        stage += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_decomposition_directions_from, 1); }
    Ok(resolved)
}

impl<'a> Parser<'a> {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, component_style_owner_view(final(styles))) == crate::specs::part1_resolve_decompositions(
            component_style_owner_view(old(styles)), owned_extensions_view(extensions)),
    ))]
    pub(super) fn resolve_decomposition_structures(
        &self,
        styles: &mut ComponentCodingStyles,
        extensions: &Part2Extensions,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial = component_style_owner_view(styles);
            let ghost goal = crate::specs::part1_resolve_decompositions(initial, owned_extensions_view(extensions));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_resolve_decompositions);
            reveal(crate::specs::part1_resolve_decomposition_style);
            reveal(crate::specs::part1_set_component_style);
        }
        let mut component = 0_u16;
        let components = styles.components;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant component <= components,
                    components == initial.0, styles.components == components,
                    initial == component_style_owner_view(old(styles)),
                    goal == crate::specs::part1_resolve_decompositions(initial, owned_extensions_view(extensions)),
                    goal == crate::specs::part1_resolve_decompositions_from(
                        component_style_owner_view(styles), owned_extensions_view(extensions), component as nat),
                decreases components - component,
            )
        )]
        while component < components {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_resolve_decompositions_from, 1);
                reveal(crate::specs::part1_resolve_decomposition_style);
                reveal(crate::specs::part1_set_component_style);
            }
            let style = styles.style(component)?;
            if style.decomposition_structure.is_some() {
                let resolved = resolve_decomposition_style(style, extensions)?;
                styles.set(component, resolved)?;
            }
            component += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_resolve_decompositions_from, 1); }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_p2_marker_storage_result(Part2FreshKind::Dfs, parser_view(old(self)), segment_view(segment), 0,
                owned_extensions_view(old(extensions)), (result, parser_view(final(self)), owned_extensions_view(final(extensions)))),
    ))]
    pub(super) fn parse_dfs(
        &mut self,
        segment: Segment<'a>,
        extensions: &mut Part2Extensions,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input = parser_view(self);
            let ghost extension_input = owned_extensions_view(extensions);
            let ghost goal = crate::specs::part1_parse_dfs(input, segment_view(segment), extension_input);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_parse_dfs);
            crate::specs::part1_p2_marker_normal(Part2FreshKind::Dfs, input, segment_view(segment), 0, extension_input, Seq::empty());
        }
        self.charge_extension_metadata(segment, extensions)?;
        let copied = self.decode_dfs_payload(segment);
        #[cfg(verus_keep_ghost)]
        proof! { if dfs_payload_outcome(copied) == Err(DecodeError::AllocationFailed) {
            crate::specs::part1_p2_marker_refused(Part2FreshKind::Dfs, input, segment_view(segment), 0, extension_input);
        }}
        let replacement = copied?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost charged_parser = parser_view(self);
            let ghost charged_extensions = owned_extensions_view(extensions);
            let ghost decoded = owned_decomposition_view(&replacement);
            let ghost target = crate::specs::part1_dfs_replace(charged_extensions.decompositions, decoded, 0);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(goal == (Ok(()), charged_parser, crate::specs::part1_extension_decompositions(
                charged_extensions, target, charged_extensions.arbitrary)));
        }
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                position <= extensions.decomposition_structures.len(),
                crate::specs::part1_p2_marker_result(Part2FreshKind::Dfs, input, segment_view(segment), 0, extension_input, goal),
                input == parser_view(old(self)),
                extension_input == owned_extensions_view(old(extensions)),
                parser_view(self) == charged_parser,
                owned_extensions_view(extensions) == charged_extensions,
                owned_decomposition_view(&replacement) == decoded,
                target == crate::specs::part1_dfs_replace(charged_extensions.decompositions, decoded, position as nat),
                goal == crate::specs::part1_parse_dfs(input, segment_view(segment), extension_input),
                goal == (Ok(()), charged_parser, crate::specs::part1_extension_decompositions(
                    charged_extensions, target, charged_extensions.arbitrary)),
            decreases extensions.decomposition_structures.len() - position,
        ))]
        while position < extensions.decomposition_structures.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_dfs_replace, 1); }
            if extensions.decomposition_structures[position].index == replacement.index {
                extensions.decomposition_structures[position] = replacement;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(owned_extensions_view(extensions).decompositions =~=
                        charged_extensions.decompositions.update(position as int, decoded));
                }
                return Ok(());
            }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_dfs_replace, 1); }
        extensions.decomposition_structures.push(replacement);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(owned_extensions_view(extensions).decompositions =~=
                charged_extensions.decompositions.push(decoded));
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_p2_marker_storage_result(Part2FreshKind::Ads, parser_view(old(self)), segment_view(segment), 0,
                owned_extensions_view(old(extensions)), (result, parser_view(final(self)), owned_extensions_view(final(extensions)))),
    ))]
    pub(super) fn parse_ads(
        &mut self,
        segment: Segment<'a>,
        extensions: &mut Part2Extensions,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input = parser_view(self);
            let ghost extension_input = owned_extensions_view(extensions);
            let ghost goal = crate::specs::part1_parse_ads(input, segment_view(segment), extension_input);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_parse_ads);
            crate::specs::part1_p2_marker_normal(Part2FreshKind::Ads, input, segment_view(segment), 0, extension_input, Seq::empty());
        }
        self.charge_extension_metadata(segment, extensions)?;
        let copied = self.decode_ads_payload(segment);
        #[cfg(verus_keep_ghost)]
        proof! { if ads_payload_outcome(copied) == Err(DecodeError::AllocationFailed) {
            crate::specs::part1_p2_marker_refused(Part2FreshKind::Ads, input, segment_view(segment), 0, extension_input);
        }}
        let replacement = copied?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost charged_parser = parser_view(self);
            let ghost charged_extensions = owned_extensions_view(extensions);
            let ghost decoded = owned_arbitrary_decomposition_view(&replacement);
            let ghost target = crate::specs::part1_ads_replace(charged_extensions.arbitrary, decoded, 0);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(goal == (Ok(()), charged_parser, crate::specs::part1_extension_decompositions(
                charged_extensions, charged_extensions.decompositions, target)));
        }
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                position <= extensions.arbitrary_decompositions.len(),
                crate::specs::part1_p2_marker_result(Part2FreshKind::Ads, input, segment_view(segment), 0, extension_input, goal),
                input == parser_view(old(self)),
                extension_input == owned_extensions_view(old(extensions)),
                parser_view(self) == charged_parser,
                owned_extensions_view(extensions) == charged_extensions,
                owned_arbitrary_decomposition_view(&replacement) == decoded,
                target == crate::specs::part1_ads_replace(charged_extensions.arbitrary, decoded, position as nat),
                goal == crate::specs::part1_parse_ads(input, segment_view(segment), extension_input),
                goal == (Ok(()), charged_parser, crate::specs::part1_extension_decompositions(
                    charged_extensions, charged_extensions.decompositions, target)),
            decreases extensions.arbitrary_decompositions.len() - position,
        ))]
        while position < extensions.arbitrary_decompositions.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_ads_replace, 1); }
            if extensions.arbitrary_decompositions[position].index == replacement.index {
                extensions.arbitrary_decompositions[position] = replacement;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(owned_extensions_view(extensions).arbitrary =~=
                        charged_extensions.arbitrary.update(position as int, decoded));
                }
                return Ok(());
            }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_ads_replace, 1); }
        extensions.arbitrary_decompositions.push(replacement);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(owned_extensions_view(extensions).arbitrary =~=
                charged_extensions.arbitrary.push(decoded));
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_p2_fresh_result(Part2FreshInput::Dfs(segment_view(segment)), Part2FreshValue::Dfs(dfs_payload_outcome(result))),
            dfs_payload_outcome(result) != Err(DecodeError::AllocationFailed) ==>
                dfs_payload_outcome(result) == crate::specs::part1_dfs_payload(segment_view(segment)),
    ))]
    pub(super) fn decode_dfs_payload(
        &self,
        segment: Segment<'a>,
    ) -> Result<DecompositionStructure, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_dfs_payload);
            crate::specs::part1_p2_fresh_normal(Part2FreshInput::Dfs(segment_view(segment)));
        }
        if segment.payload.len() < 3 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let descriptor = read_u16([segment.payload[0], segment.payload[1]]);
        #[cfg(verus_keep_ghost)]
        proof! { assert(descriptor & 15 <= 255) by (bit_vector); }
        let index = match u8::try_from(descriptor & 0x0f) {
            Ok(value) => value,
            Err(_) => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        let levels = segment.payload[2];
        let expanded = match usize::from(levels).checked_add(3) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        let packed = expanded / 4;
        let expected = match 3_usize.checked_add(packed) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(!0x000fu16 == 65520u16) by (bit_vector);
            assert(index == (descriptor & 15) as u8);
            assert(packed as int == (levels as int + 3) / 4);
            assert(expected as int == 3 + (levels as int + 3) / 4);
        }
        if descriptor & !0x000f != 0 || index == 0 || levels == 0 || levels > 32 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidCodingStyle));
        }
        if segment.payload.len() != expected {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost target = Seq::new(levels as nat, |level: int| crate::specs::part1_decomposition_code(
                crate::specs::part2_dfs_direction_code(segment.payload@[3 + level / 4], (level % 4) as u8)));
            let ghost goal = crate::specs::part1_dfs_payload(segment_view(segment));
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(goal == Ok((index, target))); }
        let copied = reserve_values(
            usize::from(levels),
            MctCopyPath::FreshPart2(FreshPart2Path::Dfs(segment.offset)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            if copied.is_err() { crate::specs::part1_p2_fresh_refused(Part2FreshInput::Dfs(segment_view(segment))); }
        }
        let mut directions = copied?;
        #[cfg(verus_keep_ghost)]
        proof! { assert(directions@ =~= Seq::<DecompositionDirection>::empty()); assert(directions@ =~= target.subrange(0, 0)); }
        let mut level = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    level <= levels as usize,
                    crate::specs::part1_p2_fresh_result(Part2FreshInput::Dfs(segment_view(segment)),
                        crate::specs::part1_p2_fresh_ordinary(Part2FreshInput::Dfs(segment_view(segment)))),
                    0 < levels <= 32,
                    segment.payload.len() == 3int + (levels as int + 3) / 4,
                    goal == crate::specs::part1_dfs_payload(segment_view(segment)),
                    goal == Ok((index, target)),
                    target == Seq::new(levels as nat, |i: int| crate::specs::part1_decomposition_code(
                        crate::specs::part2_dfs_direction_code(segment.payload@[3 + i / 4], (i % 4) as u8))),
                    directions@ == target.subrange(0, level as int),
                decreases levels as usize - level,
            )
        )]
        while level < usize::from(levels) {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_segment_byte); }
            let byte = self.segment_byte(segment, 3, level / 4)?;
            let slot = u8::try_from(level % 4)
                .map_err(|_| self.malformed_here(MalformedKind::ArithmeticOverflow))?;
            directions.push(match crate::refinement::dfs_direction_code(byte, slot) {
                0 => DecompositionDirection::None,
                1 => DecompositionDirection::TwoDimensional,
                2 => DecompositionDirection::Horizontal,
                _ => DecompositionDirection::Vertical,
            });
            level = level
                .checked_add(1)
                .ok_or_else(|| self.malformed_here(MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(directions@ =~= target); }
        Ok(DecompositionStructure { index, directions })
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_p2_fresh_result(Part2FreshInput::Ads(self.position, segment_view(segment)), Part2FreshValue::Ads(ads_payload_outcome(result))),
            ads_payload_outcome(result) != Err(DecodeError::AllocationFailed) ==>
                ads_payload_outcome(result) == crate::specs::part1_ads_payload(self.position, segment_view(segment)),
    ))]
    pub(super) fn decode_ads_payload(
        &self,
        segment: Segment<'a>,
    ) -> Result<ArbitraryDecomposition, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_ads_payload);
            crate::specs::part1_p2_fresh_normal(Part2FreshInput::Ads(self.position, segment_view(segment)));
            crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        }
        if segment.payload.len() < 3 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let index = segment.payload[0];
        if index == 0 || index > 127 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidCodingStyle));
        }
        let depth_count = usize::from(segment.payload[1]);
        let depth_bytes = crate::refinement::packed_two_bit_bytes(depth_count);
        let split_count_position = match 2_usize.checked_add(depth_bytes) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        let split_count = match segment.payload.get(split_count_position) {
            Some(value) => usize::from(*value),
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
            }
        };
        let split_bytes = crate::refinement::packed_two_bit_bytes(split_count);
        let fixed = match split_count_position.checked_add(1) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        let expected = match fixed.checked_add(split_bytes) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        if segment.payload.len() != expected {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost cold = Part2FreshInput::Ads(self.position, segment_view(segment));
            let ghost first = crate::specs::part1_p2_fresh_unpack(segment_view(segment), 2, depth_count, false);
            let ghost second = crate::specs::part1_p2_fresh_unpack(segment_view(segment), (split_count_position + 1) as usize, split_count, true);
            let ghost third = match crate::specs::part1_unpack_two_bit_values(self.position, segment_view(segment), (split_count_position + 1) as usize, split_count, true) {
                Err(_) => Seq::empty(), Ok(values) => crate::specs::part1_p2_fresh_leaf(FreshPart2Path::AdsDirections(segment.offset), values.len() as usize),
            };
        }
        let copied = self.unpack_two_bit_values(segment, 2, depth_count, false);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_p2_fresh_observed(Part2FreshInput::Unpack(self.position, segment_view(segment), 2, depth_count, false), Part2FreshValue::Unpack(two_bit_values_outcome(copied)));
            let status = if two_bit_values_outcome(copied) == Err(DecodeError::AllocationFailed) { Err(DecodeError::AllocationFailed) } else { Ok(()) };
            let tail = if crate::specs::part1_unpack_two_bit_values(self.position, segment_view(segment), 2, depth_count, false).is_ok() { second + third } else { Seq::empty() };
            crate::specs::part1_mct_copy_continue(Seq::empty(), first, tail, status);
            if two_bit_values_outcome(copied) == Err(DecodeError::AllocationFailed) { crate::specs::part1_p2_fresh_refused(cold); }
        }
        let sublevel_depths = copied?;
        let copied =
            self.unpack_two_bit_values(segment, split_count_position + 1, split_count, true);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_p2_fresh_observed(Part2FreshInput::Unpack(self.position, segment_view(segment), (split_count_position + 1) as usize, split_count, true), Part2FreshValue::Unpack(two_bit_values_outcome(copied)));
            let status = if two_bit_values_outcome(copied) == Err(DecodeError::AllocationFailed) { Err(DecodeError::AllocationFailed) } else { Ok(()) };
            crate::specs::part1_mct_copy_continue(first, second, third, status);
            assert(crate::specs::part1_p2_fresh_requests(cold) =~= (first + second) + third);
            if two_bit_values_outcome(copied) == Err(DecodeError::AllocationFailed) { crate::specs::part1_p2_fresh_refused(cold); }
        }
        let split_values = copied?;
        let copied = reserve_values(
            split_values.len(),
            MctCopyPath::FreshPart2(FreshPart2Path::AdsDirections(segment.offset)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_mct_copy_continue(first + second, third, Seq::empty(), super::mct_copy::copy_outcome(copied));
            assert(crate::specs::part1_p2_fresh_requests(cold) =~= ((first + second) + third) + Seq::<crate::specs::Part1MctCopyRequest>::empty());
            if copied.is_err() { crate::specs::part1_p2_fresh_refused(cold); }
        }
        let mut subband_splits = copied?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost target = split_values@.map_values(|code: u8| crate::specs::part1_decomposition_code(code));
            let ghost goal = crate::specs::part1_ads_payload(self.position, segment_view(segment));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(goal == Ok((index, sublevel_depths@, target)));
            assert(subband_splits@ =~= Seq::<DecompositionDirection>::empty());
            assert(subband_splits@ =~= target.subrange(0, 0));
        }
        let mut split = 0_usize;
        #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant
                        split <= split_values.len(),
                        crate::specs::part1_p2_fresh_result(Part2FreshInput::Ads(self.position, segment_view(segment)),
                            crate::specs::part1_p2_fresh_ordinary(Part2FreshInput::Ads(self.position, segment_view(segment)))),
                        goal == crate::specs::part1_ads_payload(self.position, segment_view(segment)),
                        goal == Ok((index, sublevel_depths@, target)),
                        target == split_values@.map_values(|code: u8| crate::specs::part1_decomposition_code(code)),
                        subband_splits@ == target.subrange(0, split as int),
                    decreases split_values.len() - split,
                )
            )]
        while split < split_values.len() {
            subband_splits.push(match split_values[split] {
                0 => DecompositionDirection::None,
                1 => DecompositionDirection::TwoDimensional,
                2 => DecompositionDirection::Horizontal,
                _ => DecompositionDirection::Vertical,
            });
            split = split
                .checked_add(1)
                .ok_or_else(|| self.malformed_here(MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(subband_splits@ =~= target); }
        Ok(ArbitraryDecomposition {
            index,
            sublevel_depths,
            subband_splits,
        })
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_p2_fresh_result(Part2FreshInput::Unpack(self.position, segment_view(segment), start, count, allow_terminal),
                Part2FreshValue::Unpack(two_bit_values_outcome(result))),
            two_bit_values_outcome(result) != Err(DecodeError::AllocationFailed) ==>
                two_bit_values_outcome(result) == crate::specs::part1_unpack_two_bit_values(
                    self.position, segment_view(segment), start, count, allow_terminal),
    ))]
    pub(super) fn unpack_two_bit_values(
        &self,
        segment: Segment<'a>,
        start: usize,
        count: usize,
        allow_terminal: bool,
    ) -> Result<Vec<u8>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost goal = crate::specs::part1_unpack_two_bit_values(
                self.position, segment_view(segment), start, count, allow_terminal);
        }
        #[cfg(verus_keep_ghost)]
        proof! { crate::specs::part1_p2_fresh_normal(Part2FreshInput::Unpack(self.position, segment_view(segment), start, count, allow_terminal)); }
        let path = if allow_terminal {
            FreshPart2Path::AdsSplit(segment.offset, start)
        } else {
            FreshPart2Path::AdsDepth(segment.offset, start)
        };
        let copied = reserve_values(count, MctCopyPath::FreshPart2(path));
        #[cfg(verus_keep_ghost)]
        proof! {
            if copied.is_err() { crate::specs::part1_p2_fresh_refused(Part2FreshInput::Unpack(self.position, segment_view(segment), start, count, allow_terminal)); }
        }
        let mut values = copied?;
        #[cfg(verus_keep_ghost)]
        proof! { assert(values@ =~= Seq::<u8>::empty()); }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    index <= count,
                    crate::specs::part1_p2_fresh_result(Part2FreshInput::Unpack(self.position, segment_view(segment), start, count, allow_terminal),
                        crate::specs::part1_p2_fresh_ordinary(Part2FreshInput::Unpack(self.position, segment_view(segment), start, count, allow_terminal))),
                    goal == crate::specs::part1_unpack_two_bit_values(
                        self.position, segment_view(segment), start, count, allow_terminal),
                    goal == crate::specs::part1_unpack_two_bit_run(
                        self.position, segment_view(segment), start, count, allow_terminal, index, values@),
                decreases count - index,
            )
        )]
        while index < count {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_unpack_two_bit_run, 1); }
            let byte = self.segment_byte(segment, start, index / 4)?;
            let slot = u8::try_from(index % 4)
                .map_err(|_| self.malformed_here(MalformedKind::ArithmeticOverflow))?;
            let value = crate::refinement::dfs_direction_code(byte, slot);
            if !allow_terminal && value == 0 {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidCodingStyle));
            }
            values.push(value);
            index = index
                .checked_add(1)
                .ok_or_else(|| self.malformed_here(MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_unpack_two_bit_run, 1); }
        let remainder = count % 4;
        if remainder != 0 {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(goal == match crate::specs::part1_segment_byte(
                    self.position, segment_view(segment), start, count / 4) {
                    Err(error) => Err(error),
                    Ok(last) => if last & crate::specs::part1_two_bit_padding_mask(count) != 0 {
                        Err(crate::specs::part1_codestream_malformed(segment.offset, MalformedKind::InvalidCodingStyle))
                    } else { Ok(values@) },
                });
            }
            let last = self.segment_byte(segment, start, count / 4)?;
            let unused = 2_u32
                .checked_mul(
                    u32::try_from(4 - remainder)
                        .map_err(|_| self.malformed_here(MalformedKind::ArithmeticOverflow))?,
                )
                .ok_or_else(|| self.malformed_here(MalformedKind::ArithmeticOverflow))?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(unused == 2 || unused == 4 || unused == 6);
                assert((unused == 2 || unused == 4 || unused == 6) ==>
                    (1u8 << unused) == if unused == 2 { 4u8 } else if unused == 4 { 16u8 } else { 64u8 })
                    by (bit_vector);
            }
            let mask = (1_u8 << unused) - 1;
            #[cfg(verus_keep_ghost)]
            proof! {
                if remainder == 1 {
                    assert(unused == 6);
                    assert(mask == 63);
                } else if remainder == 2 {
                    assert(unused == 4);
                    assert(mask == 15);
                } else {
                    assert(remainder == 3);
                    assert(unused == 2);
                    assert(mask == 3);
                }
                assert(unused == (2 * (4 - remainder)) as u32);
                assert((unused == 2 || unused == 4 || unused == 6) ==>
                    ((1u16 << unused) - 1) as u8 == if unused == 2 { 3u8 } else if unused == 4 { 15u8 } else { 63u8 })
                    by (bit_vector);
                assert(mask == crate::specs::part1_two_bit_padding_mask(count));
            }
            if last & mask != 0 {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidCodingStyle));
            }
        }
        Ok(values)
    }
}
