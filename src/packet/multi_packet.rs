use super::bit_reader::{packet_reader_new, packet_reader_prefix};
use super::body::{
    decode_code_block_contribution_body, execute_packet_body_contributions,
    preflight_packet_body_ranges,
};
use super::contributions::{decode_code_block_contribution, tier1_styles_equal};
use super::errors::{packet_reader_error, packet_reader_limit};
use super::{
    CodeBlockBodyDecode, CodeBlockContribution, CodeBlockPacketContext, CodeBlockPacketState,
    DecodeError, EPH_MARKER, MalformedKind, MultiHeaderParameters, MultiHeaderProgress,
    MultiPacketLayout, MultiPacketParameters, PacketBitReader, PacketBodyDecode,
    PacketBodyExecutionProgress, PacketBodyPreflight, PacketCodeBlockExecution,
    PrecinctPayloadReader, Resource, ResourceLimits, SOP_MARKER, TagTree, Tier1CodeBlockDecoder,
    Tier1CodingStyle, TilePartPayload,
};
#[cfg(verus_keep_ghost)]
use super::{
    code_block_contribution_option_view, code_block_packet_state_view, multi_admission_outcome,
    multi_header_view, multi_packet_state_view, packet_body_contributions_view,
    precinct_payload_reader_outcome, single_packet_state_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures result==crate::specs::part1_multi_contexts(contexts@,style,layer,width,0,offset),
))]
fn validate_multi_packet_contexts(
    contexts: &[CodeBlockPacketContext],
    style: Tier1CodingStyle,
    layer: u16,
    width: u32,
    offset: usize,
) -> Result<(), DecodeError> {
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_multi_contexts);}
    #[cfg_attr(verus_keep_ghost,verus_spec(
        invariant index<=contexts@.len(),
            crate::specs::part1_multi_contexts(contexts@,style,layer,width,0,offset)
                ==crate::specs::part1_multi_contexts(contexts@,style,layer,width,index,offset),
        decreases contexts@.len()-index,
    ))]
    while index < contexts.len() {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_multi_contexts);}
        let context = match contexts.get(index) {
            Some(context) => context,
            None => {
                return Err(packet_reader_error(
                    offset,
                    MalformedKind::InvalidPacketHeader,
                ));
            }
        };
        let linear = match u32::try_from(index) {
            Ok(index) => index,
            Err(_) => {
                return Err(packet_reader_error(
                    offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
        let x = match linear.checked_rem(width) {
            Some(x) => x,
            None => {
                return Err(packet_reader_error(
                    offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
        let y = match linear.checked_div(width) {
            Some(y) => y,
            None => {
                return Err(packet_reader_error(
                    offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
        if context.layer != layer
            || context.leaf_x != x
            || context.leaf_y != y
            || !tier1_styles_equal(context.tier1_style, style)
        {
            return Err(packet_reader_error(
                offset,
                MalformedKind::InvalidPacketHeader,
            ));
        }
        index = match index.checked_add(1) {
            Some(index) => index,
            None => {
                return Err(packet_reader_error(
                    offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_multi_contexts);}
    Ok(())
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures multi_admission_outcome(result)==crate::specs::part1_multi_packet_admission(
        multi_packet_state_view(states,inclusion,zero,contexts,decoders),params.part,params.offset,
        crate::limits::resource_code_block_limit(params.limits),crate::limits::resource_work_limit(params.limits)),
))]
fn validate_multi_packet_input<'a, 'data>(
    params: &MultiPacketParameters<'a, 'data>,
    states: &[CodeBlockPacketState],
    inclusion: &TagTree,
    zero: &TagTree,
    contexts: &[CodeBlockPacketContext],
    decoders: &[Tier1CodeBlockDecoder],
) -> Result<&'a [u8], DecodeError> {
    let offset = params.offset;
    if states.is_empty() || states.len() != contexts.len() || states.len() != decoders.len() {
        return Err(packet_reader_error(
            offset,
            MalformedKind::InvalidPacketHeader,
        ));
    }
    let count = states.len() as u64;
    if count > params.limits.maximum_code_blocks() {
        return Err(packet_reader_limit(
            Resource::CodeBlocks,
            params.limits.maximum_code_blocks(),
            count,
        ));
    }
    if count > params.limits.maximum_work_units() {
        return Err(packet_reader_limit(
            Resource::WorkUnits,
            params.limits.maximum_work_units(),
            count,
        ));
    }
    let leaves = match inclusion.levels.first() {
        Some(leaves) => leaves,
        None => return Err(packet_reader_error(offset, MalformedKind::InvalidTagTree)),
    };
    let zleaves = match zero.levels.first() {
        Some(leaves) => leaves,
        None => return Err(packet_reader_error(offset, MalformedKind::InvalidTagTree)),
    };
    let width = leaves.width;
    let height = leaves.height;
    if width == 0 || height == 0 {
        return Err(packet_reader_error(offset, MalformedKind::InvalidTagTree));
    }
    if inclusion.leaf_count()? != count
        || zero.leaf_count()? != count
        || width != zleaves.width
        || height != zleaves.height
    {
        return Err(packet_reader_error(offset, MalformedKind::InvalidTagTree));
    }
    let data = match params.part.data.get(offset..) {
        Some(data) => data,
        None => return Err(packet_reader_error(offset, MalformedKind::Truncated)),
    };
    let style = params.part.coding_style.tier1_coding_style()?;
    let layer = match contexts.first() {
        Some(context) => context.layer,
        None => {
            return Err(packet_reader_error(
                offset,
                MalformedKind::InvalidPacketHeader,
            ));
        }
    };
    validate_multi_packet_contexts(contexts, style, layer, width, offset)?;
    Ok(data)
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures precinct_payload_reader_outcome(result)==crate::specs::part1_multi_packet_prefix(
        data@,sop,offset,crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_work_limit(limits)),
))]
fn read_multi_packet_prefix<'a>(
    data: &'a [u8],
    sop: bool,
    offset: usize,
    limits: &ResourceLimits,
) -> Result<PrecinctPayloadReader<'a>, DecodeError> {
    let mut skip = 0_usize;
    // SOP is optional; a reserved marker prefix still needs full SOP validation.
    if sop && data.len() >= 2 && data[0] == 0xff && data[1] >= 0x90 {
        let marker = match data.get(0..2) {
            Some(marker) => marker,
            None => return Err(packet_reader_error(offset, MalformedKind::Truncated)),
        };
        let length = match data.get(2..4) {
            Some(length) => length,
            None => return Err(packet_reader_error(offset, MalformedKind::Truncated)),
        };
        if marker[0] != SOP_MARKER[0]
            || marker[1] != SOP_MARKER[1]
            || length[0] != 0
            || length[1] != 4
        {
            return Err(packet_reader_error(
                offset,
                MalformedKind::InvalidPacketHeader,
            ));
        }
        match data.get(4..6) {
            Some(_) => {}
            None => return Err(packet_reader_error(offset, MalformedKind::Truncated)),
        }
        skip = 6;
    }
    let packet_data = match data.get(skip..) {
        Some(data) => data,
        None => return Err(packet_reader_error(offset, MalformedKind::Truncated)),
    };
    let mut reader = packet_reader_prefix(packet_data, limits);
    let present = reader.read_bit()?;
    Ok(PrecinctPayloadReader {
        reader,
        packet_data,
        present,
        sop_bytes: skip,
    })
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,multi_header_view(final(states),final(inclusion),final(zero),parameters.contexts,
        final(contributions),final(reader),final(progress)))==crate::specs::part1_multi_header_slot(
            multi_header_view(old(states),old(inclusion),old(zero),parameters.contexts,old(contributions),old(reader),old(progress)),parameters.offset),
        final(states)@.len()==old(states)@.len(),final(contributions)@.len()==old(contributions)@.len(),
))]
pub(super) fn read_multi_packet_header_slot(
    states: &mut [CodeBlockPacketState],
    inclusion: &mut TagTree,
    zero: &mut TagTree,
    parameters: MultiHeaderParameters<'_>,
    contributions: &mut [Option<CodeBlockContribution>],
    reader: &mut PacketBitReader<'_>,
    progress: &mut MultiHeaderProgress,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial=multi_header_view(states,inclusion,zero,parameters.contexts,contributions,reader,progress);
        let ghost prior_states=states@;
        let ghost index=progress.index;
    }
    let context = match parameters.contexts.get(progress.index) {
        Some(context) => *context,
        None => {
            return Err(packet_reader_error(
                parameters.offset,
                MalformedKind::InvalidPacketHeader,
            ));
        }
    };
    if progress.index >= states.len() {
        return Err(packet_reader_error(
            parameters.offset,
            MalformedKind::InvalidPacketHeader,
        ));
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost header=crate::specs::part1_packet_header_decode(
    initial.states[index as int],initial.inclusion,initial.zero,context,initial.reader);}
    let result = {
        let state = &mut states[progress.index];
        decode_code_block_contribution(state, inclusion, zero, context, reader)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i:int|0<=i<states@.len() && i!=index as int implies states@[i]==prior_states[i] by {}
        assert(states@.map_values(|state:CodeBlockPacketState|code_block_packet_state_view(&state))
            =~= initial.states.update(index as int,header.1));
    }
    let contribution = result?;
    if contribution.is_some() {
        progress.count = match progress.count.checked_add(1) {
            Some(count) => count,
            None => {
                return Err(packet_reader_error(
                    parameters.offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
    }
    {
        let slot = match contributions.get_mut(progress.index) {
            Some(slot) => slot,
            None => {
                return Err(packet_reader_error(
                    parameters.offset,
                    MalformedKind::InvalidPacketHeader,
                ));
            }
        };
        *slot = contribution;
    }
    #[cfg(verus_keep_ghost)]
    proof! {assert(packet_body_contributions_view(contributions) =~=
    initial.contributions.update(index as int,code_block_contribution_option_view(contribution)));}
    progress.index = match progress.index.checked_add(1) {
        Some(index) => index,
        None => {
            return Err(packet_reader_error(
                parameters.offset,
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    Ok(())
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,multi_header_view(final(states),final(inclusion),final(zero),parameters.contexts,
        final(contributions),final(reader),final(progress)))==crate::specs::part1_multi_headers(
            multi_header_view(old(states),old(inclusion),old(zero),parameters.contexts,old(contributions),old(reader),old(progress)),parameters.offset),
        final(states)@.len()==old(states)@.len(),final(contributions)@.len()==old(contributions)@.len(),
))]
fn read_multi_packet_headers(
    states: &mut [CodeBlockPacketState],
    inclusion: &mut TagTree,
    zero: &mut TagTree,
    parameters: MultiHeaderParameters<'_>,
    contributions: &mut [Option<CodeBlockContribution>],
    reader: &mut PacketBitReader<'_>,
    progress: &mut MultiHeaderProgress,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_multi_headers);}
    #[cfg_attr(verus_keep_ghost,verus_spec(
        invariant states@.len()==old(states)@.len(),contributions@.len()==old(contributions)@.len(),
            crate::specs::part1_multi_headers(multi_header_view(old(states),old(inclusion),old(zero),
                parameters.contexts,old(contributions),old(reader),old(progress)),parameters.offset)
            ==crate::specs::part1_multi_headers(multi_header_view(states,inclusion,zero,parameters.contexts,contributions,reader,progress),parameters.offset),
        decreases parameters.contexts@.len()-progress.index,
    ))]
    while progress.index < parameters.contexts.len() {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_multi_headers);}
        read_multi_packet_header_slot(
            states,
            inclusion,
            zero,
            parameters,
            contributions,
            reader,
            progress,
        )?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_multi_headers);}
    Ok(())
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures result==crate::specs::part1_multi_body_start(data@,sop,header,eph,offset),
))]
fn multi_packet_body_start(
    data: &[u8],
    sop: usize,
    header: usize,
    eph: bool,
    offset: usize,
) -> Result<usize, DecodeError> {
    let start = match sop.checked_add(header) {
        Some(start) => start,
        None => {
            return Err(packet_reader_error(
                offset,
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    if !eph {
        return Ok(start);
    }
    let end = match start.checked_add(2) {
        Some(end) => end,
        None => {
            return Err(packet_reader_error(
                offset,
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    let marker = match data.get(start..end) {
        Some(marker) => marker,
        None => return Err(packet_reader_error(offset, MalformedKind::Truncated)),
    };
    if marker[0] != EPH_MARKER[0] || marker[1] != EPH_MARKER[1] {
        return Err(packet_reader_error(
            offset,
            MalformedKind::InvalidPacketHeader,
        ));
    }
    Ok(end)
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,final(decoders)@.map_values(|decoder:Tier1CodeBlockDecoder|crate::tier1::tier1_decoder_state(&decoder)))
        ==crate::specs::part1_multi_body_data(
            old(decoders)@.map_values(|decoder:Tier1CodeBlockDecoder|crate::tier1::tier1_decoder_state(&decoder)),
            layout.blocks,data@,packet_body_contributions_view(contributions),layout.present,layout.count,layout.header,layout.start,params.offset,
            crate::limits::resource_code_block_pass_limit(params.limits),crate::limits::resource_code_block_byte_limit(params.limits),
            crate::limits::resource_input_byte_limit(params.limits),crate::limits::resource_work_limit(params.limits)),
))]
fn decode_multi_packet_body(
    params: &MultiPacketParameters<'_, '_>,
    data: &[u8],
    contributions: &[Option<CodeBlockContribution>],
    layout: MultiPacketLayout,
    decoders: &mut [Tier1CodeBlockDecoder],
) -> Result<PacketBodyDecode, DecodeError> {
    let offset = params.offset;
    let mut preflight = PacketBodyPreflight {
        index: 0,
        end: layout.start,
    };
    preflight_packet_body_ranges(contributions, data, &mut preflight, (offset, offset))?;
    let mut execution = PacketBodyExecutionProgress {
        index: 0,
        offset: layout.start,
        segments: 0,
        passes: 0,
    };
    execute_packet_body_contributions(
        decoders,
        contributions,
        data,
        &mut execution,
        (offset, offset),
        true,
        params.limits,
    )?;
    let bytes = match preflight.end.checked_sub(layout.start) {
        Some(bytes) => bytes,
        None => {
            return Err(packet_reader_error(
                offset,
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    Ok(PacketBodyDecode {
        present: layout.present,
        code_blocks: match u32::try_from(layout.blocks) {
            Ok(n) => n,
            Err(_) => {
                return Err(packet_reader_error(
                    offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        },
        contributions: layout.count,
        segments: execution.segments,
        passes: execution.passes,
        header_bytes: match u32::try_from(layout.header) {
            Ok(n) => n,
            Err(_) => {
                return Err(packet_reader_error(
                    offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        },
        body_bytes: match u32::try_from(bytes) {
            Ok(n) => n,
            Err(_) => {
                return Err(packet_reader_error(
                    offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        },
        bytes_consumed: match u32::try_from(preflight.end) {
            Ok(n) => n,
            Err(_) => {
                return Err(packet_reader_error(
                    offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        },
    })
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,multi_packet_state_view(final(states),final(inclusion),final(zero),contexts,final(decoders)))
        ==crate::specs::part1_multi_payload(multi_packet_state_view(old(states),old(inclusion),old(zero),contexts,old(decoders)),
            data@,crate::codestream::coding_style_packet_markers(&params.part.coding_style).0,
            crate::codestream::coding_style_packet_markers(&params.part.coding_style).1,params.offset,
            crate::limits::resource_packet_header_byte_limit(params.limits),
            crate::limits::resource_code_block_pass_limit(params.limits),crate::limits::resource_code_block_byte_limit(params.limits),
            crate::limits::resource_input_byte_limit(params.limits),crate::limits::resource_work_limit(params.limits)),
        final(states)@.len()==old(states)@.len(),
))]
fn decode_multi_packet_payload(
    params: &MultiPacketParameters<'_, '_>,
    data: &[u8],
    states: &mut [CodeBlockPacketState],
    inclusion: &mut TagTree,
    zero: &mut TagTree,
    contexts: &[CodeBlockPacketContext],
    decoders: &mut [Tier1CodeBlockDecoder],
) -> Result<PacketBodyDecode, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_multi_payload);reveal(crate::specs::part1_multi_body);
        crate::codestream::coding_style_known_packet_markers(&params.part.coding_style);
    }
    let blocks = states.len() as u64;
    let prefix = read_multi_packet_prefix(
        data,
        params.part.coding_style.sop_markers,
        params.offset,
        params.limits,
    )?;
    let present = prefix.present;
    let mut reader = prefix.reader;
    let mut contributions = vec![None; states.len()];
    #[cfg(verus_keep_ghost)]
    proof! {assert(contributions@.map_values(|c:Option<CodeBlockContribution>|code_block_contribution_option_view(c))
    =~= Seq::new(states@.len(),|i:int|None));}
    let mut progress = MultiHeaderProgress { index: 0, count: 0 };
    if present {
        read_multi_packet_headers(
            states,
            inclusion,
            zero,
            MultiHeaderParameters {
                contexts,
                offset: params.offset,
            },
            &mut contributions,
            &mut reader,
            &mut progress,
        )?;
    }
    reader.finish_packet_header()?;
    let header = reader.bytes_consumed();
    let start = multi_packet_body_start(
        data,
        prefix.sop_bytes,
        header,
        params.part.coding_style.eph_markers,
        params.offset,
    )?;
    decode_multi_packet_body(
        params,
        data,
        &contributions,
        MultiPacketLayout {
            blocks,
            present,
            count: progress.count,
            header,
            start,
        },
        decoders,
    )
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,multi_packet_state_view(final(execution.states),final(execution.inclusion_tree),final(execution.zero_bitplane_tree),
        execution.contexts,final(execution.decoders)))==crate::specs::part1_multi_code_block_packet(
            multi_packet_state_view(old(execution.states),old(execution.inclusion_tree),old(execution.zero_bitplane_tree),
                execution.contexts,old(execution.decoders)),tile_part,offset,limits),
))]
pub fn decode_multi_code_block_packet(
    tile_part: &TilePartPayload<'_>,
    offset: usize,
    execution: PacketCodeBlockExecution<'_>,
    limits: &ResourceLimits,
) -> Result<PacketBodyDecode, DecodeError> {
    let states = execution.states;
    let inclusion_tree = execution.inclusion_tree;
    let zero_bitplane_tree = execution.zero_bitplane_tree;
    let contexts = execution.contexts;
    let decoders = execution.decoders;
    let params = MultiPacketParameters {
        part: tile_part,
        offset,
        limits,
    };
    let data = validate_multi_packet_input(
        &params,
        states,
        inclusion_tree,
        zero_bitplane_tree,
        contexts,
        decoders,
    )?;
    decode_multi_packet_payload(
        &params,
        data,
        states,
        inclusion_tree,
        zero_bitplane_tree,
        contexts,
        decoders,
    )
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,single_packet_state_view(final(state),final(inclusion_tree),final(zero_bitplane_tree),final(decoder)))
        ==crate::specs::part1_single_code_block_packet(
            single_packet_state_view(old(state),old(inclusion_tree),old(zero_bitplane_tree),old(decoder)),
            payload@,context,crate::limits::resource_packet_header_byte_limit(limits),
            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits)),
))]
pub fn decode_single_code_block_packet(
    payload: &[u8],
    state: &mut CodeBlockPacketState,
    inclusion_tree: &mut TagTree,
    zero_bitplane_tree: &mut TagTree,
    context: CodeBlockPacketContext,
    decoder: &mut Tier1CodeBlockDecoder,
    limits: &ResourceLimits,
) -> Result<Option<CodeBlockBodyDecode>, DecodeError> {
    let mut reader = packet_reader_new(payload, limits)?;
    if !reader.read_bit()? {
        reader.finish_packet_header()?;
        if reader.bytes_consumed() != payload.len() {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::TrailingData,
            ));
        }
        return Ok(None);
    }
    let contribution = match decode_code_block_contribution(
        state,
        inclusion_tree,
        zero_bitplane_tree,
        context,
        &mut reader,
    )? {
        Some(contribution) => contribution,
        None => {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::InvalidPacketHeader,
            ));
        }
    };
    reader.finish_packet_header()?;
    let body_offset = reader.bytes_consumed();
    let body = match payload.get(body_offset..) {
        Some(body) => body,
        None => return Err(packet_reader_error(body_offset, MalformedKind::Truncated)),
    };
    Ok(Some(decode_code_block_contribution_body(
        decoder,
        &contribution,
        body,
        limits,
    )?))
}
