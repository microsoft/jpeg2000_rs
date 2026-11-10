use vstd::prelude::*;

verus! {

pub struct Part1PacketReaderState {
    pub input: Seq<u8>,
    pub byte_index: usize,
    pub current_byte: u8,
    pub bits_remaining: u8,
    pub previous_byte_was_ff: bool,
    pub bits_read: u64,
    pub maximum_work_units: u64,
    pub maximum_header_bytes: u64,
}

pub open spec fn part1_packet_reader_error(offset: usize, kind: crate::MalformedKind) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: offset as u64, kind }
}

pub open spec fn part1_packet_reader_limit(resource: crate::Resource, limit: u64, actual: u64) -> crate::DecodeError {
    crate::DecodeError::LimitExceeded { resource, limit, actual }
}

pub open spec fn part1_packet_reader_prefix(input: Seq<u8>, header_limit: u64, work_limit: u64) -> Part1PacketReaderState {
    Part1PacketReaderState {
        input, byte_index: 0, current_byte: 0, bits_remaining: 0, previous_byte_was_ff: false,
        bits_read: 0, maximum_work_units: work_limit, maximum_header_bytes: header_limit,
    }
}

pub open spec fn part1_packet_reader_initial(input: Seq<u8>, header_limit: u64, work_limit: u64)
    -> Result<Part1PacketReaderState, crate::DecodeError>
{
    if input.len() > header_limit {
        Err(part1_packet_reader_limit(crate::Resource::PacketHeaderBytes, header_limit, input.len() as u64))
    } else { Ok(part1_packet_reader_prefix(input, header_limit, work_limit)) }
}

pub open spec fn part1_packet_reader_load(s: Part1PacketReaderState)
    -> (Result<(), crate::DecodeError>, Part1PacketReaderState)
{
    if s.byte_index as u64 >= s.maximum_header_bytes {
        if s.byte_index as u64 == u64::MAX {
            (Err(part1_packet_reader_error(s.byte_index, crate::MalformedKind::ArithmeticOverflow)), s)
        } else {
            (Err(part1_packet_reader_limit(crate::Resource::PacketHeaderBytes, s.maximum_header_bytes,
                (s.byte_index as u64 + 1) as u64)), s)
        }
    } else if s.byte_index >= s.input.len() {
        (Err(part1_packet_reader_error(s.byte_index, crate::MalformedKind::Truncated)), s)
    } else {
        let byte = s.input[s.byte_index as int];
        if s.previous_byte_was_ff && byte & 0x80u8 != 0 {
            (Err(part1_packet_reader_error(s.byte_index, crate::MalformedKind::InvalidBitStuffing)), s)
        } else if s.byte_index == usize::MAX {
            (Err(part1_packet_reader_error(s.byte_index, crate::MalformedKind::ArithmeticOverflow)), s)
        } else {
            (Ok(()), Part1PacketReaderState {
                byte_index: (s.byte_index + 1) as usize, current_byte: byte,
                bits_remaining: if s.previous_byte_was_ff { 7u8 } else { 8u8 },
                previous_byte_was_ff: byte == 0xff, ..s
            })
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_reader_finish(s: Part1PacketReaderState)
    -> (Result<(), crate::DecodeError>, Part1PacketReaderState)
{
    let loaded = if s.previous_byte_was_ff { part1_packet_reader_load(s) } else { (Ok(()), s) };
    match loaded.0 {
        Err(error) => (Err(error), loaded.1),
        Ok(()) => (Ok(()), Part1PacketReaderState { bits_remaining: 0, ..loaded.1 }),
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_reader_read(s: Part1PacketReaderState)
    -> (Result<bool, crate::DecodeError>, Part1PacketReaderState)
{
    let loaded = if s.bits_remaining == 0 { part1_packet_reader_load(s) } else { (Ok(()), s) };
    match loaded.0 {
        Err(error) => (Err(error), loaded.1),
        Ok(()) => {
            let s = loaded.1;
            if s.bits_remaining == 0 || s.bits_remaining > 8 {
                (Err(part1_packet_reader_error(s.byte_index, crate::MalformedKind::InvalidBitStuffing)), s)
            } else {
                let next = Part1PacketReaderState { bits_remaining: (s.bits_remaining - 1) as u8, ..s };
                if next.bits_read == u64::MAX {
                    (Err(part1_packet_reader_error(next.byte_index, crate::MalformedKind::ArithmeticOverflow)), next)
                } else {
                    let next = Part1PacketReaderState { bits_read: (next.bits_read + 1) as u64, ..next };
                    if next.bits_read > next.maximum_work_units {
                        (Err(part1_packet_reader_limit(crate::Resource::WorkUnits, next.maximum_work_units, next.bits_read)), next)
                    } else { (Ok(super::part1_packet_bit(next.current_byte, next.bits_remaining)), next) }
                }
            }
        },
    }
}

pub open spec fn part1_packet_reader_word(s: Part1PacketReaderState, remaining: nat, value: u32)
    -> (Result<u32, crate::DecodeError>, Part1PacketReaderState)
    decreases remaining,
{
    if remaining == 0 { (Ok(value), s) } else {
        let bit = part1_packet_reader_read(s);
        match bit.0 {
            Err(error) => (Err(error), bit.1),
            Ok(bit_value) => part1_packet_reader_word(bit.1, (remaining - 1) as nat,
                (value << 1) | if bit_value { 1u32 } else { 0u32 }),
        }
    }
}

pub open spec fn part1_packet_reader_read_bits(s: Part1PacketReaderState, count: u8)
    -> (Result<u32, crate::DecodeError>, Part1PacketReaderState)
{
    if count > 32 { (Err(part1_packet_reader_error(s.byte_index, crate::MalformedKind::InvalidMarkerLength)), s) }
    else { part1_packet_reader_word(s, count as nat, 0) }
}

pub struct Part1CodeBlockPacketState {
    pub included: bool,
    pub zero_bitplanes: Option<u16>,
    pub lblock: u8,
    pub total_passes: u32,
    pub high_throughput: Option<bool>,
}

pub open spec fn part1_code_block_packet_initial() -> Part1CodeBlockPacketState {
    Part1CodeBlockPacketState {
        included: false, zero_bitplanes: None, lblock: 3, total_passes: 0, high_throughput: None,
    }
}

pub open spec fn part1_header_floor_log2(value: u32) -> u8 {
    if value == 0 { 0 } else { (31 - vstd::std_specs::bits::u32_leading_zeros(value)) as u8 }
}

#[verifier::opaque]
pub open spec fn part1_header_new_passes(reader: Part1PacketReaderState)
    -> (Result<u8, crate::DecodeError>, Part1PacketReaderState)
{
    let first = part1_packet_reader_read(reader);
    match first.0 {
        Err(error) => (Err(error), first.1),
        Ok(false) => (Ok(1u8), first.1),
        Ok(true) => {
            let second = part1_packet_reader_read(first.1);
            match second.0 {
                Err(error) => (Err(error), second.1),
                Ok(false) => (Ok(2u8), second.1),
                Ok(true) => {
                    let suffix = part1_packet_reader_read_bits(second.1, 2);
                    match suffix.0 {
                        Err(error) => (Err(error), suffix.1),
                        Ok(value) => if value < 3 { (Ok((value + 3) as u8), suffix.1) }
                        else if value > 3 { (Err(part1_packet_reader_error(suffix.1.byte_index, crate::MalformedKind::InvalidPacketHeader)), suffix.1) }
                        else {
                            let extension = part1_packet_reader_read_bits(suffix.1, 5);
                            match extension.0 {
                                Err(error) => (Err(error), extension.1),
                                Ok(value) => {
                                    let added = if value == 31 { part1_packet_reader_read_bits(extension.1, 7) } else { extension };
                                    let delta = if value == 31 { 37nat } else { 6nat };
                                    match added.0 {
                                        Err(error) => (Err(error), added.1),
                                        Ok(value) => if value as nat + delta > u32::MAX || value as nat + delta > u8::MAX {
                                            (Err(part1_packet_reader_error(added.1.byte_index, crate::MalformedKind::ArithmeticOverflow)), added.1)
                                        } else { (Ok((value as nat + delta) as u8), added.1) },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}

pub open spec fn part1_header_lblock(
    state: Part1CodeBlockPacketState, reader: Part1PacketReaderState, remaining: nat,
) -> (Result<(), crate::DecodeError>, Part1CodeBlockPacketState, Part1PacketReaderState)
    decreases remaining,
{
    let bit = part1_packet_reader_read(reader);
    match bit.0 {
        Err(error) => (Err(error), state, bit.1),
        Ok(false) => (Ok(()), state, bit.1),
        Ok(true) => if remaining == 0 || state.lblock >= 31 {
            (Err(part1_packet_reader_error(bit.1.byte_index, crate::MalformedKind::InvalidPacketHeader)), state, bit.1)
        } else {
            part1_header_lblock(Part1CodeBlockPacketState { lblock: (state.lblock + 1) as u8, ..state }, bit.1, (remaining - 1) as nat)
        },
    }
}

pub open spec fn part1_header_zero_loop(
    state: Part1CodeBlockPacketState, tree: super::Part1TagTree, context: crate::packet::CodeBlockPacketContext,
    reader: Part1PacketReaderState, threshold: u32,
) -> (Result<(), crate::DecodeError>, Part1CodeBlockPacketState, super::Part1TagTree, Part1PacketReaderState)
    decreases context.maximum_zero_bitplanes as int - threshold as int,
{
    let decoded = super::part1_tag_tree_decode(tree, context.leaf_x, context.leaf_y, threshold, reader);
    match decoded.0 {
        Err(error) => (Err(error), state, decoded.1, decoded.2),
        Ok(value) => {
            if value.is_below_threshold {
                match value.value {
                    None => (Err(part1_packet_reader_error(decoded.2.byte_index, crate::MalformedKind::InvalidTagTree)), state, decoded.1, decoded.2),
                    Some(value) => if value > u16::MAX || value >= context.maximum_zero_bitplanes as u32 {
                        (Err(part1_packet_reader_error(decoded.2.byte_index, crate::MalformedKind::InvalidPacketHeader)), state, decoded.1, decoded.2)
                    } else { (Ok(()), Part1CodeBlockPacketState { zero_bitplanes: Some(value as u16), ..state }, decoded.1, decoded.2) },
                }
            } else if threshold >= context.maximum_zero_bitplanes as u32 {
                (Err(part1_packet_reader_error(decoded.2.byte_index, crate::MalformedKind::InvalidPacketHeader)), state, decoded.1, decoded.2)
            } else if threshold == u32::MAX {
                (Err(part1_packet_reader_error(decoded.2.byte_index, crate::MalformedKind::ArithmeticOverflow)), state, decoded.1, decoded.2)
            } else {
                part1_header_zero_loop(state, decoded.1, context, decoded.2, (threshold + 1) as u32)
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_header_prefix(
    state: Part1CodeBlockPacketState, inclusion: super::Part1TagTree, zero: super::Part1TagTree,
    context: crate::packet::CodeBlockPacketContext, reader: Part1PacketReaderState,
) -> (Result<bool, crate::DecodeError>, Part1CodeBlockPacketState, super::Part1TagTree, super::Part1TagTree, Part1PacketReaderState) {
    if context.maximum_zero_bitplanes == 0 || context.maximum_zero_bitplanes > crate::tier1::MAX_TIER1_BITPLANES {
        (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::InvalidPacketHeader)), state, inclusion, zero, reader)
    } else {
        let first = !state.included;
        let event = if first {
            let decoded = super::part1_tag_tree_decode(inclusion, context.leaf_x, context.leaf_y, (context.layer as u32 + 1) as u32, reader);
            (match decoded.0 { Err(error) => Err(error), Ok(value) => Ok(value.is_below_threshold) }, decoded.1, decoded.2)
        } else {
            let decoded = part1_packet_reader_read(reader);
            (decoded.0, inclusion, decoded.1)
        };
        match event.0 {
            Err(error) => (Err(error), state, event.1, zero, event.2),
            Ok(false) => (Ok(false), state, event.1, zero, event.2),
            Ok(true) => if !first { (Ok(true), state, event.1, zero, event.2) } else {
                let state = Part1CodeBlockPacketState { included: true, ..state };
                let decoded = part1_header_zero_loop(state, zero, context, event.2, 1);
                (match decoded.0 { Err(error) => Err(error), Ok(()) => Ok(true) }, decoded.1, event.1, decoded.2, decoded.3)
            },
        }
    }
}

pub struct Part1HeaderSegments {
    pub segment_passes: Seq<u8>,
    pub segment_lengths: Seq<u32>,
    pub segment_count: usize,
    pub accounted_passes: u32,
    pub data_length: u32,
    pub routing: Option<bool>,
}

pub open spec fn part1_header_initial_routing(state: Part1CodeBlockPacketState, style: crate::tier1::Tier1CodingStyle) -> Option<bool> {
    match state.high_throughput {
        Some(selected) => Some(selected),
        None => match style.block_coding {
            crate::tier1::Tier1BlockCoding::Legacy => Some(false),
            crate::tier1::Tier1BlockCoding::HighThroughput => Some(true),
            crate::tier1::Tier1BlockCoding::Mixed => if style.force_high_throughput { Some(true) } else { None },
        },
    }
}

pub open spec fn part1_header_segments_initial(state: Part1CodeBlockPacketState, style: crate::tier1::Tier1CodingStyle) -> Part1HeaderSegments {
    Part1HeaderSegments {
        segment_passes: Seq::new(164, |i: int| 0u8), segment_lengths: Seq::new(164, |i: int| 0u32),
        segment_count: 0, accounted_passes: 0, data_length: 0, routing: part1_header_initial_routing(state, style),
    }
}

#[verifier::opaque]
pub open spec fn part1_header_segment_length(
    state: Part1CodeBlockPacketState, segments: Part1HeaderSegments, reader: Part1PacketReaderState,
    first_pass: u32, remaining: u32, passes: u32, length_bits: u8,
) -> (Result<(u32, u32), crate::DecodeError>, Part1CodeBlockPacketState, Part1HeaderSegments, Part1PacketReaderState) {
    let decoded = part1_packet_reader_read_bits(reader, length_bits);
    match decoded.0 {
        Err(error) => (Err(error), state, segments, decoded.1),
        Ok(length) => {
            if segments.routing.is_some() { (Ok((passes, length)), state, segments, decoded.1) }
            else {
                let bits = state.lblock as nat + part1_header_floor_log2(remaining) as nat;
                if bits > u8::MAX {
                    (Err(part1_packet_reader_error(0, crate::MalformedKind::ArithmeticOverflow)), state, segments, decoded.1)
                } else if bits > 32 {
                    (Err(part1_packet_reader_error(decoded.1.byte_index, crate::MalformedKind::InvalidPacketHeader)), state, segments, decoded.1)
                } else {
                    let probe = part1_packet_reader_read_bits(reader, bits as u8);
                    match probe.0 {
                        Err(error) => (Err(error), state, segments, decoded.1),
                        Ok(legacy_length) => {
                            let leading_zero = length != 0 && length_bits > 0 && length < (1u32 << ((length_bits - 1) as u32));
                            let legacy = super::ht_mixed_selects_legacy(length as nat, legacy_length as nat, first_pass % 3 == 0, state.lblock > 3, leading_zero);
                            if legacy {
                                if segments.accounted_passes != 0 {
                                    (Err(part1_packet_reader_error(decoded.1.byte_index, crate::MalformedKind::InvalidPacketHeader)), state, segments, decoded.1)
                                } else {
                                    (Ok((remaining, legacy_length)),
                                        Part1CodeBlockPacketState { high_throughput: Some(false), ..state },
                                        Part1HeaderSegments { routing: Some(false), ..segments }, probe.1)
                                }
                            } else if length != 0 {
                                (Ok((passes, length)), Part1CodeBlockPacketState { high_throughput: Some(true), ..state },
                                    Part1HeaderSegments { routing: Some(true), ..segments }, decoded.1)
                            } else { (Ok((passes, length)), state, segments, decoded.1) }
                        },
                    }
                }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_header_segment_step(
    state: Part1CodeBlockPacketState, segments: Part1HeaderSegments, reader: Part1PacketReaderState,
    new_passes: u8, context: crate::packet::CodeBlockPacketContext,
) -> (Result<(), crate::DecodeError>, Part1CodeBlockPacketState, Part1HeaderSegments, Part1PacketReaderState) {
    if segments.segment_count >= segments.segment_passes.len() || segments.segment_count >= segments.segment_lengths.len() {
        (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::InvalidPacketHeader)), state, segments, reader)
    } else if state.total_passes as nat + segments.accounted_passes as nat > u32::MAX {
        (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::ArithmeticOverflow)), state, segments, reader)
    } else if segments.accounted_passes > new_passes as u32 {
        (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::ArithmeticOverflow)), state, segments, reader)
    } else {
        let first = (state.total_passes + segments.accounted_passes) as u32;
        let remaining = (new_passes as u32 - segments.accounted_passes) as u32;
        let passes = if segments.routing != Some(false) { super::ht_segment_passes((first % 3) as nat, remaining as nat) as u32 }
            else { super::part1_legacy_segment_passes(context.tier1_style, first, remaining) };
        if passes == 0 || passes > remaining || passes > u8::MAX as u32 {
            (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::InvalidPacketHeader)), state, segments, reader)
        } else {
            let bits = state.lblock as nat + part1_header_floor_log2(passes) as nat;
            if bits > u8::MAX { (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::ArithmeticOverflow)), state, segments, reader) }
            else if bits > 32 { (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::InvalidPacketHeader)), state, segments, reader) }
            else {
                let decoded = part1_header_segment_length(state, segments, reader, first, remaining, passes, bits as u8);
                let state = decoded.1; let segments = decoded.2; let reader = decoded.3;
                match decoded.0 {
                    Err(error) => (Err(error), state, segments, reader),
                    Ok((actual_passes, length)) => if length == 0 && segments.routing == Some(false) && first == 0 {
                        (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::InvalidPacketHeader)), state, segments, reader)
                    } else if actual_passes > u8::MAX as u32 {
                        (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::ArithmeticOverflow)), state, segments, reader)
                    } else {
                        let segments = Part1HeaderSegments {
                            segment_passes: segments.segment_passes.update(segments.segment_count as int, actual_passes as u8),
                            segment_lengths: segments.segment_lengths.update(segments.segment_count as int, length), ..segments
                        };
                        if segments.data_length as nat + length as nat > u32::MAX {
                            (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::ArithmeticOverflow)), state, segments, reader)
                        } else {
                            let segments = Part1HeaderSegments { data_length: (segments.data_length + length) as u32, ..segments };
                            if segments.accounted_passes as nat + actual_passes as nat > u32::MAX {
                                (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::ArithmeticOverflow)), state, segments, reader)
                            } else {
                                let segments = Part1HeaderSegments { accounted_passes: (segments.accounted_passes + actual_passes) as u32, ..segments };
                                if segments.segment_count == usize::MAX {
                                    (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::ArithmeticOverflow)), state, segments, reader)
                                } else {
                                    (Ok(()), state, Part1HeaderSegments { segment_count: (segments.segment_count + 1) as usize, ..segments }, reader)
                                }
                            }
                        }
                    },
                }
            }
        }
    }
}

pub open spec fn part1_header_segments_run(
    state: Part1CodeBlockPacketState, segments: Part1HeaderSegments, reader: Part1PacketReaderState,
    new_passes: u8, context: crate::packet::CodeBlockPacketContext, remaining: nat,
) -> (Result<(), crate::DecodeError>, Part1CodeBlockPacketState, Part1HeaderSegments, Part1PacketReaderState)
    decreases remaining,
{
    if segments.accounted_passes >= new_passes as u32 { (Ok(()), state, segments, reader) } else {
        let step = part1_header_segment_step(state, segments, reader, new_passes, context);
        match step.0 {
            Err(_) => step,
            Ok(()) => if remaining == 0 { step } else {
                part1_header_segments_run(step.1, step.2, step.3, new_passes, context, (remaining - 1) as nat)
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_header_segments(
    state: Part1CodeBlockPacketState, reader: Part1PacketReaderState,
    new_passes: u8, context: crate::packet::CodeBlockPacketContext,
) -> (Result<Part1HeaderSegments, crate::DecodeError>, Part1CodeBlockPacketState, Part1PacketReaderState) {
    let segments = part1_header_segments_initial(state, context.tier1_style);
    let run = part1_header_segments_run(state, segments, reader, new_passes, context, 165);
    (match run.0 { Err(error) => Err(error), Ok(()) => Ok(run.2) }, run.1, run.3)
}

pub open spec fn part1_header_commit(
    original: Part1CodeBlockPacketState, next: Part1CodeBlockPacketState, segments: Part1HeaderSegments,
    first: bool, new_passes: u8, reader: Part1PacketReaderState,
) -> (Result<Option<super::Part1CodeBlockContribution>, crate::DecodeError>, Part1CodeBlockPacketState) {
    if next.total_passes as nat + new_passes as nat > u32::MAX {
        (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::ArithmeticOverflow)), original)
    } else {
        let next = Part1CodeBlockPacketState { total_passes: (next.total_passes + new_passes) as u32, ..next };
        if next.total_passes > crate::tier1::MAX_TIER1_PASSES {
            (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::InvalidPacketHeader)), original)
        } else {
            match next.zero_bitplanes {
                None => (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::InvalidPacketHeader)), original),
                Some(zero) => {
                    let next = Part1CodeBlockPacketState { high_throughput: segments.routing, ..next };
                    if segments.segment_count > u8::MAX {
                        (Err(part1_packet_reader_error(reader.byte_index, crate::MalformedKind::ArithmeticOverflow)), next)
                    } else {
                        (Ok(Some(super::Part1CodeBlockContribution {
                            first_inclusion: first, zero_bitplanes: zero, new_passes, data_length: segments.data_length,
                            high_throughput: segments.routing != Some(false), segment_count: segments.segment_count as u8,
                            segment_passes: segments.segment_passes, segment_lengths: segments.segment_lengths,
                        })), next)
                    }
                },
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_header_decode(
    original: Part1CodeBlockPacketState, inclusion: super::Part1TagTree, zero: super::Part1TagTree,
    context: crate::packet::CodeBlockPacketContext, reader: Part1PacketReaderState,
) -> (Result<Option<super::Part1CodeBlockContribution>, crate::DecodeError>, Part1CodeBlockPacketState,
    super::Part1TagTree, super::Part1TagTree, Part1PacketReaderState)
{
    let prefix = part1_header_prefix(original, inclusion, zero, context, reader);
    let inclusion = prefix.2; let zero = prefix.3; let reader = prefix.4;
    match prefix.0 {
        Err(error) => (Err(error), original, inclusion, zero, reader),
        Ok(false) => (Ok(None), original, inclusion, zero, reader),
        Ok(true) => {
            let state = prefix.1;
            let passes = part1_header_new_passes(reader);
            match passes.0 {
                Err(error) => (Err(error), original, inclusion, zero, passes.1),
                Ok(new_passes) => {
                    let block = part1_header_lblock(state, passes.1, 32);
                    match block.0 {
                        Err(error) => (Err(error), original, inclusion, zero, block.2),
                        Ok(()) => {
                            let segments = part1_header_segments(block.1, block.2, new_passes, context);
                            match segments.0 {
                                Err(error) => (Err(error), original, inclusion, zero, segments.2),
                                Ok(data) => {
                                    let committed = part1_header_commit(original, segments.1, data, !original.included, new_passes, segments.2);
                                    (committed.0, committed.1, inclusion, zero, segments.2)
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}

}
