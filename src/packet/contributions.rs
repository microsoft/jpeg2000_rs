use super::errors::{invalid_packet_header, packet_arithmetic_overflow, packet_reader_error};
use super::{
    CodeBlockContribution, CodeBlockHeaderSegments, CodeBlockPacketContext, CodeBlockPacketState,
    CodeBlockSegmentContribution, DecodeError, MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION,
    MalformedKind, PacketBitReader, TagTree, Tier1CodingStyle,
};
#[cfg(verus_keep_ghost)]
use super::{
    code_block_contribution_view, code_block_header_outcome, code_block_packet_state_view,
    header_segments_outcome, header_segments_view, packet_bit_reader_view, tag_tree_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures code_block_packet_state_view(&result) == crate::specs::part1_code_block_packet_initial(),
))]
pub(crate) const fn code_block_packet_state_new() -> CodeBlockPacketState {
    CodeBlockPacketState {
        included: false,
        zero_bitplanes: None,
        lblock: 3,
        total_passes: 0,
        high_throughput: None,
    }
}

impl CodeBlockPacketState {
    pub const fn new() -> Self {
        code_block_packet_state_new()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == code_block_packet_state_view(self).included,))]
    pub const fn included(&self) -> bool {
        self.included
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == code_block_packet_state_view(self).zero_bitplanes,))]
    pub const fn zero_bitplanes(&self) -> Option<u16> {
        self.zero_bitplanes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == code_block_packet_state_view(self).lblock,))]
    pub const fn lblock(&self) -> u8 {
        self.lblock
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == code_block_packet_state_view(self).total_passes,))]
    pub const fn total_passes(&self) -> u32 {
        self.total_passes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == code_block_packet_state_view(self).high_throughput,))]
    pub const fn high_throughput(&self) -> Option<bool> {
        self.high_throughput
    }
}

impl Default for CodeBlockPacketState {
    fn default() -> Self {
        code_block_packet_state_new()
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_packet_styles_equal(left, right),
))]
pub(super) fn tier1_styles_equal(left: Tier1CodingStyle, right: Tier1CodingStyle) -> bool {
    matches!(
        (left.block_coding, right.block_coding),
        (
            crate::tier1::Tier1BlockCoding::Legacy,
            crate::tier1::Tier1BlockCoding::Legacy
        ) | (
            crate::tier1::Tier1BlockCoding::HighThroughput,
            crate::tier1::Tier1BlockCoding::HighThroughput
        ) | (
            crate::tier1::Tier1BlockCoding::Mixed,
            crate::tier1::Tier1BlockCoding::Mixed
        )
    ) && left.selective_arithmetic_coding_bypass == right.selective_arithmetic_coding_bypass
        && left.reset_contexts == right.reset_contexts
        && left.terminate_all_passes == right.terminate_all_passes
        && left.vertical_causal_context == right.vertical_causal_context
        && left.predictable_termination == right.predictable_termination
        && left.segmentation_symbols == right.segmentation_symbols
}

impl CodeBlockContribution {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == code_block_contribution_view(self).segment_count,
    ))]
    pub const fn segment_count(&self) -> u8 {
        self.segment_count
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_code_block_segment(code_block_contribution_view(self), index),
    ))]
    pub fn segment(&self, index: u8) -> Result<CodeBlockSegmentContribution, DecodeError> {
        if index >= self.segment_count {
            return Err(invalid_packet_header());
        }
        let index = usize::from(index);
        if index >= self.segment_passes.len() || index >= self.segment_lengths.len() {
            return Err(invalid_packet_header());
        }
        Ok(CodeBlockSegmentContribution {
            passes: self.segment_passes[index],
            data_length: self.segment_lengths[index],
        })
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures header_segments_view(&result) == crate::specs::part1_header_segments_initial(code_block_packet_state_view(state), style),
))]
pub(super) fn header_segments_new(
    state: &CodeBlockPacketState,
    style: Tier1CodingStyle,
) -> CodeBlockHeaderSegments {
    let segment_passes = [0_u8; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    let segment_lengths = [0_u32; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
    let segment_count = 0_usize;
    let accounted_passes = 0_u32;
    let data_length = 0_u32;
    let routing = match state.high_throughput {
        Some(selected) => Some(selected),
        None => match style.block_coding {
            crate::tier1::Tier1BlockCoding::Legacy => Some(false),
            crate::tier1::Tier1BlockCoding::HighThroughput => Some(true),
            crate::tier1::Tier1BlockCoding::Mixed if style.force_high_throughput => Some(true),
            crate::tier1::Tier1BlockCoding::Mixed => None,
        },
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(segment_passes@ =~= Seq::new(164, |i: int| 0u8));
        assert(segment_lengths@ =~= Seq::new(164, |i: int| 0u32));
    }
    CodeBlockHeaderSegments {
        segment_passes,
        segment_lengths,
        segment_count,
        accounted_passes,
        data_length,
        routing,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_packet_state_view(final(state)), header_segments_view(final(segments)), packet_bit_reader_view(final(reader)))
        == crate::specs::part1_header_segment_length(code_block_packet_state_view(old(state)), header_segments_view(old(segments)),
            packet_bit_reader_view(old(reader)), first_pass, remaining_passes, passes, length_bits),
        final(segments).segment_count == old(segments).segment_count,
        final(segments).accounted_passes == old(segments).accounted_passes,
        final(segments).data_length == old(segments).data_length,
        final(segments).segment_passes@ == old(segments).segment_passes@,
        final(segments).segment_lengths@ == old(segments).segment_lengths@,
        match result { Ok((actual_passes, _)) => actual_passes == passes || actual_passes == remaining_passes, Err(_) => true },
))]
pub(super) fn read_header_segment_length(
    state: &mut CodeBlockPacketState,
    segments: &mut CodeBlockHeaderSegments,
    reader: &mut PacketBitReader<'_>,
    first_pass: u32,
    remaining_passes: u32,
    passes: u32,
    length_bits: u8,
) -> Result<(u32, u32), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_header_segment_length); }
    let segment_reader_start = *reader;
    let mut segment_length = reader.read_bits(length_bits)?;
    let mut actual_passes = passes;
    if segments.routing.is_none() {
        let legacy_length_bits = state
            .lblock
            .checked_add(floor_log2(remaining_passes))
            .ok_or_else(packet_arithmetic_overflow)?;
        if legacy_length_bits > 32 {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::InvalidPacketHeader,
            ));
        }
        let mut legacy_probe = segment_reader_start;
        let legacy_length = legacy_probe.read_bits(legacy_length_bits)?;
        let leading_zero = segment_length != 0
            && length_bits > 0
            && segment_length < (1_u32 << u32::from(length_bits - 1));
        let selects_legacy = crate::refinement::ht_mixed_selects_legacy(
            segment_length,
            legacy_length,
            first_pass.is_multiple_of(3),
            state.lblock > 3,
            leading_zero,
        );
        if selects_legacy {
            if segments.accounted_passes != 0 {
                return Err(packet_reader_error(
                    reader.bytes_consumed(),
                    MalformedKind::InvalidPacketHeader,
                ));
            }
            segments.routing = Some(false);
            state.high_throughput = Some(false);
            *reader = legacy_probe;
            actual_passes = remaining_passes;
            segment_length = legacy_length;
        } else if segment_length != 0 {
            segments.routing = Some(true);
            state.high_throughput = Some(true);
        }
    }
    Ok((actual_passes, segment_length))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_packet_state_view(final(state)), tag_tree_view(final(inclusion_tree)),
        tag_tree_view(final(zero_bitplane_tree)), packet_bit_reader_view(final(reader)))
        == crate::specs::part1_header_prefix(code_block_packet_state_view(old(state)), tag_tree_view(old(inclusion_tree)),
            tag_tree_view(old(zero_bitplane_tree)), context, packet_bit_reader_view(old(reader))),
))]
fn read_header_prefix(
    state: &mut CodeBlockPacketState,
    inclusion_tree: &mut TagTree,
    zero_bitplane_tree: &mut TagTree,
    context: CodeBlockPacketContext,
    reader: &mut PacketBitReader<'_>,
) -> Result<bool, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_header_prefix);
    }
    if context.maximum_zero_bitplanes == 0
        || context.maximum_zero_bitplanes > crate::tier1::MAX_TIER1_BITPLANES
    {
        return Err(packet_reader_error(
            reader.bytes_consumed(),
            MalformedKind::InvalidPacketHeader,
        ));
    }
    let first_inclusion = !state.included;
    let included = if first_inclusion {
        let threshold = match u32::from(context.layer).checked_add(1) {
            Some(value) => value,
            None => {
                return Err(packet_reader_error(
                    reader.bytes_consumed(),
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
        inclusion_tree
            .decode(context.leaf_x, context.leaf_y, threshold, reader)?
            .is_below_threshold
    } else {
        reader.read_bit()?
    };
    if !included {
        return Ok(false);
    }

    if first_inclusion {
        state.included = crate::refinement::packet_next_included(state.included, true);
        read_header_zero_bitplanes(state, zero_bitplane_tree, context, reader)?;
    }
    Ok(true)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (code_block_header_outcome(result), code_block_packet_state_view(final(state)), tag_tree_view(final(inclusion_tree)),
        tag_tree_view(final(zero_bitplane_tree)), packet_bit_reader_view(final(reader)))
        == crate::specs::part1_packet_header_decode(code_block_packet_state_view(old(state)), tag_tree_view(old(inclusion_tree)),
            tag_tree_view(old(zero_bitplane_tree)), context, packet_bit_reader_view(old(reader))),
        result.is_err() ==> code_block_packet_state_view(final(state)) == code_block_packet_state_view(old(state)),
))]
pub fn decode_code_block_contribution(
    state: &mut CodeBlockPacketState,
    inclusion_tree: &mut TagTree,
    zero_bitplane_tree: &mut TagTree,
    context: CodeBlockPacketContext,
    reader: &mut PacketBitReader<'_>,
) -> Result<Option<CodeBlockContribution>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_packet_header_decode); }
    let mut next_state = *state;
    let first_inclusion = !next_state.included;
    if !read_header_prefix(
        &mut next_state,
        inclusion_tree,
        zero_bitplane_tree,
        context,
        reader,
    )? {
        return Ok(None);
    }
    let new_passes = read_new_passes(reader)?;
    read_header_lblock(&mut next_state, reader)?;
    let segments = read_header_segments(&mut next_state, new_passes, context, reader)?;
    commit_header_contribution(
        state,
        next_state,
        segments,
        first_inclusion,
        new_passes,
        reader,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (header_segments_outcome(result), code_block_packet_state_view(final(state)), packet_bit_reader_view(final(reader)))
        == crate::specs::part1_header_segments(code_block_packet_state_view(old(state)), packet_bit_reader_view(old(reader)), new_passes, context),
        match result { Ok(segments) => segments.segment_count <= 164, Err(_) => true },
))]
fn read_header_segments(
    state: &mut CodeBlockPacketState,
    new_passes: u8,
    context: CodeBlockPacketContext,
    reader: &mut PacketBitReader<'_>,
) -> Result<CodeBlockHeaderSegments, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_header_segments); }
    let mut segments = header_segments_new(state, context.tier1_style);
    let target_passes = u32::from(new_passes);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial_state = code_block_packet_state_view(state);
        let ghost initial_reader = packet_bit_reader_view(reader);
        let ghost initial_segments = header_segments_view(&segments);
        let ghost goal = crate::specs::part1_header_segments_run(initial_state, initial_segments, initial_reader, new_passes, context, 165);
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant segments.accounted_passes <= target_passes,
                target_passes == new_passes as u32,
                segments.segment_count <= 164,
                initial_state == code_block_packet_state_view(old(state)), initial_reader == packet_bit_reader_view(old(reader)),
                initial_segments == crate::specs::part1_header_segments_initial(initial_state, context.tier1_style),
                goal == crate::specs::part1_header_segments_run(initial_state, initial_segments, initial_reader, new_passes, context, 165),
                goal == crate::specs::part1_header_segments_run(code_block_packet_state_view(state), header_segments_view(&segments),
                    packet_bit_reader_view(reader), new_passes, context, (165 - segments.segment_count) as nat),
            decreases target_passes - segments.accounted_passes,
        )
    )]
    while segments.accounted_passes < target_passes {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_header_segments);
            reveal(crate::specs::part1_header_segments_run);
        }
        read_header_segment(state, &mut segments, new_passes, context, reader)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_header_segments_run); }
    Ok(segments)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_packet_state_view(final(state)), header_segments_view(final(segments)), packet_bit_reader_view(final(reader)))
        == crate::specs::part1_header_segment_step(code_block_packet_state_view(old(state)), header_segments_view(old(segments)),
            packet_bit_reader_view(old(reader)), new_passes, context),
        result.is_ok() ==> final(segments).segment_count == old(segments).segment_count + 1
            && old(segments).segment_count < 164
            && final(segments).accounted_passes > old(segments).accounted_passes
            && final(segments).accounted_passes <= new_passes as u32,
))]
pub(super) fn read_header_segment(
    state: &mut CodeBlockPacketState,
    segments: &mut CodeBlockHeaderSegments,
    new_passes: u8,
    context: CodeBlockPacketContext,
    reader: &mut PacketBitReader<'_>,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_header_segment_step); }
    if segments.segment_count >= segments.segment_passes.len()
        || segments.segment_count >= segments.segment_lengths.len()
    {
        return Err(packet_reader_error(
            reader.bytes_consumed(),
            MalformedKind::InvalidPacketHeader,
        ));
    }
    let first_pass = match state.total_passes.checked_add(segments.accounted_passes) {
        Some(value) => value,
        None => {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    let remaining_passes = match u32::from(new_passes).checked_sub(segments.accounted_passes) {
        Some(value) => value,
        None => {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    let parse_as_ht = segments.routing != Some(false);
    let passes = if parse_as_ht {
        crate::refinement::ht_segment_passes(first_pass % 3, remaining_passes)
    } else {
        context
            .tier1_style
            .segment_passes(first_pass, remaining_passes)
    };
    if passes == 0 || passes > remaining_passes || passes > u32::from(u8::MAX) {
        return Err(packet_reader_error(
            reader.bytes_consumed(),
            MalformedKind::InvalidPacketHeader,
        ));
    }
    let pass_length_bits = floor_log2(passes);
    let length_bits = match state.lblock.checked_add(pass_length_bits) {
        Some(value) => value,
        None => {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    if length_bits > 32 {
        return Err(packet_reader_error(
            reader.bytes_consumed(),
            MalformedKind::InvalidPacketHeader,
        ));
    }
    let (actual_passes, segment_length) = read_header_segment_length(
        state,
        segments,
        reader,
        first_pass,
        remaining_passes,
        passes,
        length_bits,
    )?;
    // A later layer can finish a buffered entropy segment without adding bytes.
    let initial_empty = segment_length == 0 && segments.routing == Some(false) && first_pass == 0;
    #[cfg(all(feature = "pdf-mq-recovery", not(verus_keep_ghost)))]
    let initial_empty =
        initial_empty && !crate::pdf_mq::permits(context.tier1_style, first_pass, actual_passes);
    if initial_empty {
        return Err(packet_reader_error(
            reader.bytes_consumed(),
            MalformedKind::InvalidPacketHeader,
        ));
    }
    segments.segment_passes[segments.segment_count] = match u8::try_from(actual_passes) {
        Ok(value) => value,
        Err(_) => {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    segments.segment_lengths[segments.segment_count] = segment_length;
    segments.data_length = match segments.data_length.checked_add(segment_length) {
        Some(value) => value,
        None => {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    segments.accounted_passes = match segments.accounted_passes.checked_add(actual_passes) {
        Some(value) => value,
        None => {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    segments.segment_count = match segments.segment_count.checked_add(1) {
        Some(value) => value,
        None => {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (code_block_header_outcome(result), code_block_packet_state_view(final(state))) == crate::specs::part1_header_commit(
        code_block_packet_state_view(old(state)), code_block_packet_state_view(&next_state), header_segments_view(&segments),
        first_inclusion, new_passes, packet_bit_reader_view(reader)),
))]
pub(super) fn commit_header_contribution(
    state: &mut CodeBlockPacketState,
    mut next_state: CodeBlockPacketState,
    segments: CodeBlockHeaderSegments,
    first_inclusion: bool,
    new_passes: u8,
    reader: &PacketBitReader<'_>,
) -> Result<Option<CodeBlockContribution>, DecodeError> {
    let CodeBlockHeaderSegments {
        segment_passes,
        segment_lengths,
        segment_count,
        data_length,
        routing,
        ..
    } = segments;
    let added_passes = u32::from(new_passes);
    if next_state.total_passes > u32::MAX - added_passes {
        return Err(packet_reader_error(
            reader.bytes_consumed(),
            MalformedKind::ArithmeticOverflow,
        ));
    }
    next_state.total_passes =
        crate::refinement::packet_next_passes(next_state.total_passes, added_passes);
    if next_state.total_passes > crate::tier1::MAX_TIER1_PASSES {
        return Err(packet_reader_error(
            reader.bytes_consumed(),
            MalformedKind::InvalidPacketHeader,
        ));
    }
    let zero_bitplanes = match next_state.zero_bitplanes {
        Some(value) => value,
        None => {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::InvalidPacketHeader,
            ));
        }
    };
    next_state.high_throughput = routing;
    *state = next_state;
    Ok(Some(CodeBlockContribution {
        first_inclusion,
        zero_bitplanes,
        new_passes,
        data_length,
        high_throughput: routing != Some(false),
        segment_count: match u8::try_from(segment_count) {
            Ok(value) => value,
            Err(_) => {
                return Err(packet_reader_error(
                    reader.bytes_consumed(),
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        },
        segment_passes,
        segment_lengths,
    }))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_packet_state_view(final(state)), tag_tree_view(final(tree)), packet_bit_reader_view(final(reader)))
        == crate::specs::part1_header_zero_loop(code_block_packet_state_view(old(state)), tag_tree_view(old(tree)), context,
            packet_bit_reader_view(old(reader)), 1),
))]
fn read_header_zero_bitplanes(
    state: &mut CodeBlockPacketState,
    tree: &mut TagTree,
    context: CodeBlockPacketContext,
    reader: &mut PacketBitReader<'_>,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_state = code_block_packet_state_view(state);
        let ghost original_tree = tag_tree_view(tree);
        let ghost original_reader = packet_bit_reader_view(reader);
    }
    let maximum_zero_bitplanes = u32::from(context.maximum_zero_bitplanes);
    let mut threshold = 1_u32;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant threshold >= 1,
            maximum_zero_bitplanes == context.maximum_zero_bitplanes as u32,
            original_state == code_block_packet_state_view(old(state)),
            original_tree == tag_tree_view(old(tree)), original_reader == packet_bit_reader_view(old(reader)),
            crate::specs::part1_header_zero_loop(original_state, original_tree, context, original_reader, 1)
                == crate::specs::part1_header_zero_loop(code_block_packet_state_view(state), tag_tree_view(tree), context,
                    packet_bit_reader_view(reader), threshold),
        decreases maximum_zero_bitplanes as int - threshold as int,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_header_zero_loop); }
        let decoded = tree.decode(context.leaf_x, context.leaf_y, threshold, reader)?;
        if decoded.is_below_threshold {
            let value = match decoded.value {
                Some(value) => value,
                None => {
                    return Err(packet_reader_error(
                        reader.bytes_consumed(),
                        MalformedKind::InvalidTagTree,
                    ));
                }
            };
            let zero_bitplanes = match u16::try_from(value) {
                Ok(value) => value,
                Err(_) => {
                    return Err(packet_reader_error(
                        reader.bytes_consumed(),
                        MalformedKind::InvalidPacketHeader,
                    ));
                }
            };
            if zero_bitplanes >= context.maximum_zero_bitplanes {
                return Err(packet_reader_error(
                    reader.bytes_consumed(),
                    MalformedKind::InvalidPacketHeader,
                ));
            }
            state.zero_bitplanes = Some(zero_bitplanes);
            return Ok(());
        }
        if threshold >= maximum_zero_bitplanes {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::InvalidPacketHeader,
            ));
        }
        threshold = match threshold.checked_add(1) {
            Some(value) => value,
            None => {
                return Err(packet_reader_error(
                    reader.bytes_consumed(),
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, packet_bit_reader_view(final(reader))) == crate::specs::part1_header_new_passes(packet_bit_reader_view(old(reader))),
))]
pub(super) fn read_new_passes(reader: &mut PacketBitReader<'_>) -> Result<u8, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_header_new_passes); }
    if !reader.read_bit()? {
        return Ok(1);
    }
    if !reader.read_bit()? {
        return Ok(2);
    }
    let suffix = reader.read_bits(2)?;
    match suffix {
        0 => Ok(3),
        1 => Ok(4),
        2 => Ok(5),
        3 => {
            let extension = reader.read_bits(5)?;
            let passes = if extension == 31 {
                reader.read_bits(7)?.checked_add(37)
            } else {
                extension.checked_add(6)
            };
            let passes = match passes {
                Some(value) => value,
                None => {
                    return Err(packet_reader_error(
                        reader.bytes_consumed(),
                        MalformedKind::ArithmeticOverflow,
                    ));
                }
            };
            match u8::try_from(passes) {
                Ok(value) => Ok(value),
                Err(_) => Err(packet_reader_error(
                    reader.bytes_consumed(),
                    MalformedKind::ArithmeticOverflow,
                )),
            }
        }
        _ => Err(packet_reader_error(
            reader.bytes_consumed(),
            MalformedKind::InvalidPacketHeader,
        )),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_packet_state_view(final(state)), packet_bit_reader_view(final(reader)))
        == crate::specs::part1_header_lblock(code_block_packet_state_view(old(state)), packet_bit_reader_view(old(reader)), 32),
))]
fn read_header_lblock(
    state: &mut CodeBlockPacketState,
    reader: &mut PacketBitReader<'_>,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = code_block_packet_state_view(state);
        let ghost start_reader = packet_bit_reader_view(reader);
    }
    let mut remaining_lblock_increments = 32_u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant remaining_lblock_increments <= 32,
            original == code_block_packet_state_view(old(state)), start_reader == packet_bit_reader_view(old(reader)),
            crate::specs::part1_header_lblock(original, start_reader, 32)
                == crate::specs::part1_header_lblock(code_block_packet_state_view(state), packet_bit_reader_view(reader), remaining_lblock_increments as nat),
        decreases remaining_lblock_increments,
    ))]
    while reader.read_bit()? {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_header_lblock); }
        if remaining_lblock_increments == 0 {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::InvalidPacketHeader,
            ));
        }
        remaining_lblock_increments -= 1;
        if state.lblock >= 31 {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::InvalidPacketHeader,
            ));
        }
        state.lblock = crate::refinement::packet_next_lblock(state.lblock);
        if state.lblock > 31 {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::InvalidPacketHeader,
            ));
        }
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_header_floor_log2(value),
))]
pub(super) fn floor_log2(value: u32) -> u8 {
    #[cfg(verus_keep_ghost)]
    proof! { vstd::std_specs::bits::axiom_u32_leading_zeros(value); }
    if value != 0 {
        (31 - value.leading_zeros()) as u8
    } else {
        0
    }
}
