use super::{
    Part1CodeBlockContribution, Tier1DecoderState, ht_reader_error,
    part1_code_block_body_transaction,
};
use vstd::prelude::*;

verus! {

pub struct Part1PacketBodyPreflight {
    pub index: usize,
    pub end: usize,
}

pub type Part1PacketBodyPreflightResult = (Result<(), crate::DecodeError>, Part1PacketBodyPreflight);

#[verifier::opaque]
pub open spec fn part1_packet_body_preflight(
    state: Part1PacketBodyPreflight, contributions: Seq<Option<Part1CodeBlockContribution>>,
    data: Seq<u8>, error_offset: usize,
) -> Part1PacketBodyPreflightResult
{
    part1_packet_body_preflight_at(state,contributions,data,error_offset,0)
}

#[verifier::opaque]
pub open spec fn part1_packet_body_preflight_at(
    state:Part1PacketBodyPreflight,contributions:Seq<Option<Part1CodeBlockContribution>>,
    data:Seq<u8>,error_offset:usize,local_offset:usize,
) ->Part1PacketBodyPreflightResult
    decreases contributions.len() - state.index as nat,
{
    if state.index >= contributions.len() { (Ok(()), state) } else {
        let checked = match contributions[state.index as int] {
            None => (Ok(()), state),
            Some(contribution) => if contribution.data_length as nat > usize::MAX {
                (Err(super::part1_packet_reader_error(local_offset,crate::MalformedKind::ArithmeticOverflow)), state)
            } else if state.end as nat + contribution.data_length as nat > usize::MAX {
                (Err(super::part1_packet_reader_error(local_offset,crate::MalformedKind::ArithmeticOverflow)), state)
            } else {
                let state = Part1PacketBodyPreflight {
                    end: (state.end + contribution.data_length) as usize, ..state
                };
                if state.end > data.len() {
                    (Err(crate::DecodeError::MalformedInput {
                        offset: error_offset as u64, kind: crate::MalformedKind::Truncated,
                    }), state)
                } else { (Ok(()), state) }
            },
        };
        match checked.0 {
            Err(_) => checked,
            Ok(()) => if checked.1.index == usize::MAX {
                (Err(super::part1_packet_reader_error(local_offset,crate::MalformedKind::ArithmeticOverflow)), checked.1)
            } else {
                part1_packet_body_preflight_at(Part1PacketBodyPreflight {
                    index: (checked.1.index + 1) as usize, ..checked.1
                }, contributions, data, error_offset,local_offset)
            },
        }
    }
}

pub struct Part1PacketBodyExecution {
    pub decoders: Seq<Tier1DecoderState>,
    pub index: usize,
    pub offset: usize,
    pub segments: u32,
    pub passes: u32,
}

pub type Part1PacketBodyExecutionResult = (Result<(), crate::DecodeError>, Part1PacketBodyExecution);

pub struct Part1PacketSubbandState {
    pub orientation: crate::tier1::SubbandOrientation,
    pub first_decoder: usize,
    pub decoder_count: usize,
    pub code_blocks_across: u32,
    pub code_blocks_down: u32,
    pub inclusion_tree: super::Part1TagTree,
    pub zero_bitplane_tree: super::Part1TagTree,
}

pub struct Part1PacketPrecinctState {
    pub component: u16,
    pub resolution: u8,
    pub precinct: u32,
    pub states: Seq<super::Part1CodeBlockPacketState>,
    pub contexts: Seq<crate::packet::CodeBlockPacketContext>,
    pub decoders: Seq<Tier1DecoderState>,
    pub subbands: Seq<Part1PacketSubbandState>,
}

pub struct Part1PrecinctPayloadParameters {
    pub error_offset: usize,
    pub packed_offset: usize,
    pub expected_packet_length: Option<u32>,
    pub expected_sop_sequence: u16,
    pub style: crate::tier1::Tier1CodingStyle,
    pub sop: bool,
    pub eph: bool,
    pub packed: bool,
    pub decode_tier1: bool,
}

pub type Part1PrecinctPayloadResult =
    (Result<(crate::packet::PacketBodyDecode, usize, usize), crate::DecodeError>, Part1PacketPrecinctState);

pub struct Part1PrecinctPayloadReader {
    pub reader: super::Part1PacketReaderState,
    pub packet_data: Seq<u8>,
    pub present: bool,
    pub sop_bytes: usize,
}

pub open spec fn part1_precinct_payload_finish(
    state: Part1PacketPrecinctState, parameters: Part1PrecinctPayloadParameters,
    present: bool, contribution_count: u32, segments: u32, passes: u32,
    header_bytes: usize, body_start: usize, tile_offset: usize, packed_consumed: usize,
) -> Part1PrecinctPayloadResult {
    if tile_offset < body_start || tile_offset as nat + packed_consumed as nat > usize::MAX {
        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        let body_bytes = (tile_offset - body_start) as usize;
        let logical = (tile_offset + packed_consumed) as usize;
        if parameters.expected_packet_length.is_some()
            && parameters.expected_packet_length.unwrap() as nat > usize::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
        } else if parameters.expected_packet_length.is_some()
            && logical != parameters.expected_packet_length.unwrap() {
            (Err(super::part1_packet_reader_error(parameters.error_offset, crate::MalformedKind::InvalidPacketLength)), state)
        } else if state.states.len() as u64 > u32::MAX || header_bytes > u32::MAX
            || body_bytes > u32::MAX || logical > u32::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
        } else {
            (Ok((crate::packet::PacketBodyDecode {
                present, code_blocks: state.states.len() as u64 as u32, contributions: contribution_count,
                segments, passes, header_bytes: header_bytes as u32, body_bytes: body_bytes as u32,
                bytes_consumed: logical as u32,
            }, tile_offset, packed_consumed)), state)
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_precinct_payload_body(
    state: Part1PacketPrecinctState, contributions: Seq<Option<Part1CodeBlockContribution>>,
    data: Seq<u8>, parameters: Part1PrecinctPayloadParameters,
    present: bool, contribution_count: u32, header_bytes: usize, body_start: usize, packed_consumed: usize,
    pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
) -> Part1PrecinctPayloadResult {
    let preflight = part1_packet_body_preflight(
        Part1PacketBodyPreflight { index: 0, end: body_start }, contributions, data, parameters.error_offset);
    match preflight.0 {
        Err(error) => (Err(error), state),
        Ok(()) => {
            let execution = part1_packet_body_execute(Part1PacketBodyExecution {
                decoders: state.decoders, index: 0, offset: body_start, segments: 0, passes: 0,
            }, contributions, data, parameters.error_offset, parameters.decode_tier1,
                pass_limit, byte_limit, input_limit, work_limit);
            let state = Part1PacketPrecinctState { decoders: execution.1.decoders, ..state };
            match execution.0 {
                Err(error) => (Err(error), state),
                Ok(()) => part1_precinct_payload_finish(state, parameters, present, contribution_count,
                    execution.1.segments, execution.1.passes, header_bytes, body_start, preflight.1.end, packed_consumed),
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_precinct_payload_after_headers(
    state: Part1PacketPrecinctState, parameters: Part1PrecinctPayloadParameters,
    data: Seq<u8>, packet_data: Seq<u8>, reader: super::Part1PacketReaderState,
    contributions: Seq<Option<Part1CodeBlockContribution>>, contribution_count: u32,
    present: bool, sop_bytes: usize,
    pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
) -> Part1PrecinctPayloadResult {
    let finished = super::part1_packet_reader_finish(reader);
    match finished.0 {
        Err(error) => (Err(error), state),
        Ok(()) => {
    let reader = finished.1;
    let header_bytes = reader.byte_index;
    if !parameters.packed && sop_bytes as nat + header_bytes as nat > usize::MAX {
        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        let tile_offset = if parameters.packed { sop_bytes } else { (sop_bytes + header_bytes) as usize };
        let packed_consumed = if parameters.packed { header_bytes } else { 0usize };
        if !parameters.eph {
            part1_precinct_payload_body(state, contributions, data, parameters, present, contribution_count,
                header_bytes, tile_offset, packed_consumed, pass_limit, byte_limit, input_limit, work_limit)
        } else if header_bytes as nat + 2 > usize::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
        } else {
            let marker_end = (header_bytes + 2) as usize;
            if marker_end > packet_data.len() {
                (Err(super::part1_packet_reader_error(parameters.error_offset, crate::MalformedKind::Truncated)), state)
            } else if !super::part1_eph_valid(packet_data[header_bytes as int], packet_data[header_bytes as int + 1]) {
                (Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)), state)
            } else if !parameters.packed && tile_offset as nat + 2 > usize::MAX {
                (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
            } else {
                part1_precinct_payload_body(state, contributions, data, parameters, present, contribution_count,
                    header_bytes, if parameters.packed { tile_offset } else { (tile_offset + 2) as usize },
                    if parameters.packed { marker_end } else { packed_consumed },
                    pass_limit, byte_limit, input_limit, work_limit)
            }
        }
    }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_precinct_payload_headers(
    state: Part1PacketPrecinctState, parameters: Part1PrecinctPayloadParameters,
    data: Seq<u8>, prefix: Part1PrecinctPayloadReader,
    pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
) -> Part1PrecinctPayloadResult {
    let present = prefix.present;
            let initial = Part1PrecinctHeaderState {
                states: state.states, subbands: state.subbands,
                contributions: Seq::new(state.states.len(), |i: int| None),
                reader: prefix.reader, subband_index: 0, local_index: 0, contribution_count: 0,
            };
            let headers = if present && state.contexts.len() > 0 {
                part1_precinct_headers(initial, state.contexts, state.contexts[0].layer, parameters.style)
            } else { (Ok(()), initial) };
            let state = Part1PacketPrecinctState { states: headers.1.states, subbands: headers.1.subbands, ..state };
            match headers.0 {
                Err(error) => (Err(error), state),
                Ok(()) => part1_precinct_payload_after_headers(state, parameters, data, prefix.packet_data,
                    headers.1.reader,
                    headers.1.contributions, headers.1.contribution_count, present, prefix.sop_bytes,
                    pass_limit, byte_limit, input_limit, work_limit),
            }
}

pub open spec fn part1_precinct_payload_prefix(
    data: Seq<u8>, packed_headers: Seq<u8>, parameters: Part1PrecinctPayloadParameters,
    header_limit: u64, work_limit: u64,
) -> Result<Part1PrecinctPayloadReader, crate::DecodeError> {
    let sop = if !parameters.sop || data.len() < 2 || data[0] != 0xff
        || (data[1] != 0x91 && (parameters.packed || data[1] < 0x90)) { Ok(0usize) }
    else if data.len() < 4 {
        Err(super::part1_packet_reader_error(parameters.error_offset, crate::MalformedKind::Truncated))
    } else if !super::part1_sop_valid(data[0], data[1], data[2], data[3]) {
        Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader))
    } else if data.len() < 6 {
        Err(super::part1_packet_reader_error(parameters.error_offset, crate::MalformedKind::Truncated))
    } else if super::part1_sop_sequence(data[4], data[5]) != parameters.expected_sop_sequence {
        Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader))
    } else { Ok(6usize) };
    match sop {
        Err(error) => Err(error),
        Ok(sop_bytes) => {
            let packet_data = if parameters.packed {
            if parameters.packed_offset > packed_headers.len() {
                Err(super::part1_packet_reader_error(parameters.packed_offset, crate::MalformedKind::Truncated))
            } else {
                Ok(packed_headers.subrange(parameters.packed_offset as int, packed_headers.len() as int))
            }
        } else if sop_bytes > data.len() {
            Err(super::part1_packet_reader_error(parameters.error_offset, crate::MalformedKind::Truncated))
        } else {
            Ok(data.subrange(sop_bytes as int, data.len() as int))
        };
            match packet_data {
                Err(error) => Err(error),
                Ok(packet_data) => {
                    let first = super::part1_packet_reader_read(super::part1_packet_reader_prefix(packet_data, header_limit, work_limit));
                    match first.0 {
                        Err(error) => Err(error),
                        Ok(present) => Ok(Part1PrecinctPayloadReader { reader: first.1, packet_data, present, sop_bytes }),
                    }
                },
            }
        },
    }
}

pub open spec fn part1_precinct_payload(
    state: Part1PacketPrecinctState, data: Seq<u8>, packed_headers: Seq<u8>,
    parameters: Part1PrecinctPayloadParameters, header_limit: u64,
    pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
) -> Part1PrecinctPayloadResult {
    match part1_precinct_payload_prefix(data, packed_headers, parameters, header_limit, work_limit) {
        Err(error) => (Err(error), state),
        Ok(prefix) => part1_precinct_payload_headers(state, parameters, data, prefix,
            pass_limit, byte_limit, input_limit, work_limit),
    }
}

pub open spec fn part1_precinct_packet(
    state: Part1PacketPrecinctState, tile_part: &crate::codestream::TilePartPayload<'_>,
    offset: usize, packed_headers: Seq<u8>, packed_offset: usize,
    expected_packet_length: Option<u32>, expected_sop_sequence: u16, decode_tier1: bool,
    code_block_limit: u64, header_limit: u64, pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
) -> Part1PrecinctPayloadResult {
    part1_precinct_packet_owned(state,crate::codestream::tile_part_owned_view(tile_part),offset,packed_headers,
        packed_offset,expected_packet_length,expected_sop_sequence,decode_tier1,
        code_block_limit,header_limit,pass_limit,byte_limit,input_limit,work_limit)
}

pub open spec fn part1_precinct_packet_owned(
    state: Part1PacketPrecinctState, tile_part: super::Part2OwnedTilePart,
    offset: usize, packed_headers: Seq<u8>, packed_offset: usize,
    expected_packet_length: Option<u32>, expected_sop_sequence: u16, decode_tier1: bool,
    code_block_limit:u64,header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
) -> Part1PrecinctPayloadResult {
    part1_precinct_packet_fields(state,tile_part.data,&tile_part.component_coding_styles,&tile_part.coding_style,
        !matches!(tile_part.packed_packet_headers.source,super::Part1PackedHeaderSource::None),
        offset,packed_headers,packed_offset,expected_packet_length,expected_sop_sequence,decode_tier1,
        code_block_limit,header_limit,pass_limit,byte_limit,input_limit,work_limit)
}

pub open spec fn part1_precinct_packet_fields(
    state:Part1PacketPrecinctState,data:Seq<u8>,component_styles:&crate::codestream::ComponentCodingStyles,
    coding_style:&crate::codestream::CodingStyle,packed_present:bool,
    offset:usize,packed_headers:Seq<u8>,packed_offset:usize,
    expected_packet_length:Option<u32>,expected_sop_sequence:u16,decode_tier1:bool,
    code_block_limit:u64,header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
) ->Part1PrecinctPayloadResult {
    if state.states.len() != state.contexts.len() || state.states.len() != state.decoders.len()
        || (state.states.len() == 0) != (state.subbands.len() == 0) {
        (Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)), state)
    } else if state.states.len() as u64 > code_block_limit {
        (Err(super::part1_packet_reader_limit(crate::Resource::CodeBlocks,
            code_block_limit, state.states.len() as u64)), state)
    } else if state.states.len() as u64 > work_limit {
        (Err(super::part1_packet_reader_limit(crate::Resource::WorkUnits,
            work_limit, state.states.len() as u64)), state)
    } else if offset > data.len() {
        (Err(super::part1_packet_reader_error(offset, crate::MalformedKind::InvalidPacketLength)), state)
    } else {
        match crate::codestream::component_coding_style_result(component_styles, state.component) {
            Err(error) => (Err(error), state),
            Ok(style) => match crate::codestream::coding_style_tier1_result(style) {
                Err(error) => (Err(error), state),
                Ok(tier1_style) => {
                    let markers = crate::codestream::coding_style_packet_markers(coding_style);
                    part1_precinct_payload(state, data.subrange(offset as int, data.len() as int),
                        packed_headers, Part1PrecinctPayloadParameters {
                            error_offset: offset, packed_offset, expected_packet_length, expected_sop_sequence,
                            style: tier1_style, sop: markers.0, eph: markers.1,
                            packed: packed_present, decode_tier1,
                        }, header_limit, pass_limit, byte_limit, input_limit, work_limit)
                },
            },
        }
    }
}

pub struct Part1PrecinctHeaderState {
    pub states: Seq<super::Part1CodeBlockPacketState>,
    pub subbands: Seq<Part1PacketSubbandState>,
    pub contributions: Seq<Option<Part1CodeBlockContribution>>,
    pub reader: super::Part1PacketReaderState,
    pub subband_index: usize,
    pub local_index: usize,
    pub contribution_count: u32,
}

pub type Part1PrecinctHeaderResult = (Result<(), crate::DecodeError>, Part1PrecinctHeaderState);

pub open spec fn part1_packet_styles_equal(
    left: crate::tier1::Tier1CodingStyle, right: crate::tier1::Tier1CodingStyle,
) -> bool {
    left.block_coding == right.block_coding
        && left.selective_arithmetic_coding_bypass == right.selective_arithmetic_coding_bypass
        && left.reset_contexts == right.reset_contexts
        && left.terminate_all_passes == right.terminate_all_passes
        && left.vertical_causal_context == right.vertical_causal_context
        && left.predictable_termination == right.predictable_termination
        && left.segmentation_symbols == right.segmentation_symbols
}

#[verifier::opaque]
pub open spec fn part1_precinct_header_slot(
    state: Part1PrecinctHeaderState, contexts: Seq<crate::packet::CodeBlockPacketContext>,
    layer: u16, style: crate::tier1::Tier1CodingStyle,
) -> Part1PrecinctHeaderResult {
    if state.subband_index >= state.subbands.len() {
        (Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)), state)
    } else {
    let subband = state.subbands[state.subband_index as int];
    if subband.first_decoder as nat + state.local_index as nat > usize::MAX {
        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        let index = (subband.first_decoder + state.local_index) as usize;
        if index >= contexts.len() { (Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)), state) }
        else if state.local_index > u32::MAX || subband.code_blocks_across == 0 {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
        } else {
            let context = contexts[index as int];
            if context.layer != layer || context.leaf_x != (state.local_index as u32) % subband.code_blocks_across
                || context.leaf_y != (state.local_index as u32) / subband.code_blocks_across
                || !part1_packet_styles_equal(context.tier1_style, style) {
                (Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)), state)
            } else if index >= state.states.len() {
                (Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)), state)
            } else {
                let result = super::part1_packet_header_decode(state.states[index as int],
                    subband.inclusion_tree, subband.zero_bitplane_tree, context, state.reader);
                let subband = Part1PacketSubbandState {
                    inclusion_tree: result.2, zero_bitplane_tree: result.3, ..subband
                };
                let state = Part1PrecinctHeaderState {
                    states: state.states.update(index as int, result.1),
                    subbands: state.subbands.update(state.subband_index as int, subband),
                    reader: result.4, ..state
                };
                match result.0 {
                    Err(error) => (Err(error), state),
                    Ok(contribution) => if contribution.is_some() && state.contribution_count == u32::MAX {
                        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
                    } else {
                        let state = Part1PrecinctHeaderState {
                            contribution_count: if contribution.is_some() {
                                (state.contribution_count + 1) as u32
                            } else { state.contribution_count }, ..state
                        };
                        if index >= state.contributions.len() {
                            (Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)), state)
                        } else {
                            let state = Part1PrecinctHeaderState {
                                contributions: state.contributions.update(index as int, contribution), ..state
                            };
                            if state.local_index == usize::MAX {
                                (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
                            } else {
                                (Ok(()), Part1PrecinctHeaderState { local_index: (state.local_index + 1) as usize, ..state })
                            }
                        }
                    },
                }
            }
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_precinct_header_members_run(
    state: Part1PrecinctHeaderState, contexts: Seq<crate::packet::CodeBlockPacketContext>,
    layer: u16, style: crate::tier1::Tier1CodingStyle, remaining: nat,
) -> Part1PrecinctHeaderResult
    decreases remaining,
{
    if remaining == 0 { (Ok(()), state) } else {
        let step = part1_precinct_header_slot(state, contexts, layer, style);
        match step.0 {
            Err(_) => step,
            Ok(()) => part1_precinct_header_members_run(step.1, contexts, layer, style, (remaining - 1) as nat),
        }
    }
}

pub open spec fn part1_precinct_header_members(
    state: Part1PrecinctHeaderState, contexts: Seq<crate::packet::CodeBlockPacketContext>,
    layer: u16, style: crate::tier1::Tier1CodingStyle, count: usize,
) -> Part1PrecinctHeaderResult {
    part1_precinct_header_members_run(state, contexts, layer, style,
        if state.local_index >= count { 0 } else { (count - state.local_index) as nat })
}

#[verifier::opaque]
pub open spec fn part1_precinct_headers_run(
    state: Part1PrecinctHeaderState, contexts: Seq<crate::packet::CodeBlockPacketContext>,
    layer: u16, style: crate::tier1::Tier1CodingStyle, remaining: nat,
) -> Part1PrecinctHeaderResult
    decreases remaining,
{
    if remaining == 0 { (Ok(()), state) }
    else if state.subband_index >= state.subbands.len() {
        (Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)), state)
    } else {
        let subband = state.subbands[state.subband_index as int];
        let count = subband.code_blocks_across as nat * subband.code_blocks_down as nat;
        if count > u64::MAX || count > usize::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
        } else if count != subband.decoder_count {
            (Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)), state)
        } else {
            let inclusion = super::part1_tag_leaf_count(subband.inclusion_tree);
            match inclusion {
                Err(error) => (Err(error), state),
                Ok(value) => if value != count {
                    (Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)), state)
                } else {
                    let zero = super::part1_tag_leaf_count(subband.zero_bitplane_tree);
                    match zero {
                        Err(error) => (Err(error), state),
                        Ok(value) => if value != count {
                            (Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)), state)
                        } else {
                            let members = part1_precinct_header_members(
                                Part1PrecinctHeaderState { local_index: 0, ..state }, contexts, layer, style, count as usize);
                            match members.0 {
                                Err(_) => members,
                                Ok(()) => if members.1.subband_index == usize::MAX {
                                    (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), members.1)
                                } else {
                                    part1_precinct_headers_run(Part1PrecinctHeaderState {
                                        subband_index: (members.1.subband_index + 1) as usize, ..members.1
                                    }, contexts, layer, style, (remaining - 1) as nat)
                                },
                            }
                        },
                    }
                },
            }
        }
    }
}

pub open spec fn part1_precinct_headers(
    state: Part1PrecinctHeaderState, contexts: Seq<crate::packet::CodeBlockPacketContext>,
    layer: u16, style: crate::tier1::Tier1CodingStyle,
) -> Part1PrecinctHeaderResult {
    part1_precinct_headers_run(state, contexts, layer, style,
        if state.subband_index >= state.subbands.len() { 0 }
        else { (state.subbands.len() - state.subband_index as nat) as nat })
}

pub open spec fn part1_packet_body_execute_slot(
    state: Part1PacketBodyExecution, contribution: Part1CodeBlockContribution, data: Seq<u8>,
    error_offset: usize, decode_tier1: bool,
    pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
) -> Part1PacketBodyExecutionResult {
    part1_packet_body_execute_slot_at(state,contribution,data,error_offset,0,decode_tier1,
        pass_limit,byte_limit,input_limit,work_limit)
}

pub open spec fn part1_packet_body_execute_slot_at(
    state:Part1PacketBodyExecution,contribution:Part1CodeBlockContribution,data:Seq<u8>,
    error_offset:usize,local_offset:usize,decode_tier1:bool,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
) ->Part1PacketBodyExecutionResult {
    if contribution.data_length as nat > usize::MAX
        || state.offset as nat + contribution.data_length as nat > usize::MAX {
        (Err(super::part1_packet_reader_error(local_offset,crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        let end = (state.offset + contribution.data_length) as usize;
        if state.offset > end || end > data.len() {
            (Err(crate::DecodeError::MalformedInput {
                offset: error_offset as u64, kind: crate::MalformedKind::Truncated,
            }), state)
        } else {
            let decoded = if !decode_tier1 { (Ok(()), state) }
            else if state.index >= state.decoders.len() {
                (Err(super::part1_packet_reader_error(local_offset,crate::MalformedKind::InvalidPacketHeader)), state)
            } else {
                let result = part1_code_block_body_transaction(state.decoders[state.index as int],
                    contribution, data.subrange(state.offset as int, end as int),
                    pass_limit, byte_limit, input_limit, work_limit);
                let state = Part1PacketBodyExecution {
                    decoders: state.decoders.update(state.index as int, result.1), ..state
                };
                match result.0 {
                    Err(error) => (Err(error), state),
                    Ok(value) => if state.segments as nat + value.segments as nat > u32::MAX {
                        (Err(super::part1_packet_reader_error(local_offset,crate::MalformedKind::ArithmeticOverflow)), state)
                    } else {
                        let state = Part1PacketBodyExecution {
                            segments: (state.segments + value.segments) as u32, ..state
                        };
                        if state.passes as nat + value.passes as nat > u32::MAX {
                            (Err(super::part1_packet_reader_error(local_offset,crate::MalformedKind::ArithmeticOverflow)), state)
                        } else {
                            (Ok(()), Part1PacketBodyExecution {
                                passes: (state.passes + value.passes) as u32, ..state
                            })
                        }
                    },
                }
            };
            match decoded.0 {
                Err(_) => decoded,
                Ok(()) => (Ok(()), Part1PacketBodyExecution { offset: end, ..decoded.1 }),
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_body_execute(
    state: Part1PacketBodyExecution, contributions: Seq<Option<Part1CodeBlockContribution>>,
    data: Seq<u8>, error_offset: usize, decode_tier1: bool,
    pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
) -> Part1PacketBodyExecutionResult
{
    part1_packet_body_execute_at(state,contributions,data,error_offset,0,decode_tier1,
        pass_limit,byte_limit,input_limit,work_limit)
}

#[verifier::opaque]
pub open spec fn part1_packet_body_execute_at(
    state:Part1PacketBodyExecution,contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,
    error_offset:usize,local_offset:usize,decode_tier1:bool,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
) ->Part1PacketBodyExecutionResult
    decreases contributions.len() - state.index as nat,
{
    if state.index >= contributions.len() { (Ok(()), state) } else {
        let step = match contributions[state.index as int] {
            None => (Ok(()), state),
            Some(contribution) => part1_packet_body_execute_slot_at(state, contribution, data,
                error_offset, local_offset,decode_tier1, pass_limit, byte_limit, input_limit, work_limit),
        };
        match step.0 {
            Err(_) => step,
            Ok(()) => if step.1.index == usize::MAX {
                (Err(super::part1_packet_reader_error(local_offset,crate::MalformedKind::ArithmeticOverflow)), step.1)
            } else {
                part1_packet_body_execute_at(Part1PacketBodyExecution {
                    index: (step.1.index + 1) as usize, ..step.1
                }, contributions, data, error_offset,local_offset,decode_tier1,
                    pass_limit, byte_limit, input_limit, work_limit)
            },
        }
    }
}

}
