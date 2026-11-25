use super::errors::{invalid_packet_header, packet_arithmetic_overflow, packet_reader_error};
use super::{
    CodeBlockPacketContext, CodeBlockPacketState, PacketBodyDecode, PacketBodyExecutionProgress,
    PacketBodyPreflight, PacketSubbandState, PrecinctHeaderParameters, PrecinctHeaderProgress,
    PrecinctPayloadHeader, PrecinctPayloadParameters, PrecinctPayloadReader,
};
use crate::tier1::PrivateHtDecoder;
use crate::tier1::Tier1CodingStyle;
use crate::{DecodeError, MalformedKind, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(crate) struct PrivateHtPrecinct {
    resolution: u8,
    states: Vec<CodeBlockPacketState>,
    contexts: Vec<CodeBlockPacketContext>,
    subbands: Vec<PacketSubbandState>,
    decoders: Vec<PrivateHtDecoder>,
}

pub(crate) struct PrivateHtSubbandExecution {
    pub(crate) orientation: crate::tier1::SubbandOrientation,
    pub(crate) across: u32,
    pub(crate) down: u32,
    pub(crate) maximum_zero: u16,
    pub(crate) decoders: Vec<PrivateHtDecoder>,
}

pub(crate) fn new_private_ht_resolution_precinct(
    resolution: u8,
    style: Tier1CodingStyle,
    mut executions: Vec<PrivateHtSubbandExecution>,
    limits: &ResourceLimits,
) -> Result<PrivateHtPrecinct, DecodeError> {
    if executions.len() > 3 {
        return Err(invalid_packet_header());
    }
    let mut precinct = PrivateHtPrecinct {
        resolution,
        states: Vec::new(),
        contexts: Vec::new(),
        subbands: if executions.is_empty() {
            Vec::new()
        } else {
            crate::allocation::empty_with_capacity(executions.len())?
        },
        decoders: Vec::new(),
    };
    let mut total = 0_u64;
    let mut index = 0;
    while index < executions.len() {
        let execution = executions
            .get_mut(index)
            .ok_or_else(invalid_packet_header)?;
        if execution.across == 0
            || execution.down == 0
            || execution.maximum_zero == 0
            || execution.maximum_zero > crate::tier1::MAX_TIER1_BITPLANES
        {
            return Err(invalid_packet_header());
        }
        let count = u64::from(execution.across)
            .checked_mul(u64::from(execution.down))
            .ok_or_else(packet_arithmetic_overflow)?;
        total = total
            .checked_add(count)
            .ok_or_else(packet_arithmetic_overflow)?;
        if total > limits.maximum_code_blocks() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlocks,
                limit: limits.maximum_code_blocks(),
                actual: total,
            });
        }
        if total > limits.maximum_work_units() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: limits.maximum_work_units(),
                actual: total,
            });
        }
        if count > usize::MAX as u64 {
            return Err(packet_arithmetic_overflow());
        }
        let count = count as usize;
        if execution.decoders.len() != count {
            return Err(invalid_packet_header());
        }
        let first_decoder = precinct.decoders.len();
        let (states, contexts) = super::precinct::prepare_precinct_contexts(
            precinct.states,
            precinct.contexts,
            count,
            execution.across,
            execution.maximum_zero,
            style,
        )?;
        precinct.states = states;
        precinct.contexts = contexts;
        if !execution.decoders.is_empty() {
            crate::allocation::reserve_additional(
                &mut precinct.decoders,
                execution.decoders.len(),
            )?;
        }
        precinct.decoders.append(&mut execution.decoders);
        let inclusion_tree =
            super::tag_tree::tag_tree_new(execution.across, execution.down, limits)?;
        let zero_bitplane_tree =
            super::tag_tree::tag_tree_new(execution.across, execution.down, limits)?;
        precinct.subbands.push(PacketSubbandState {
            orientation: execution.orientation,
            first_decoder,
            decoder_count: count,
            code_blocks_across: execution.across,
            code_blocks_down: execution.down,
            inclusion_tree,
            zero_bitplane_tree,
        });
        index += 1;
    }
    Ok(precinct)
}

pub(crate) fn decode_private_ht_resolution_packets(
    parts: &[crate::codestream::TilePartPayload<'_>],
    grid: &super::PacketGrid,
    precincts: &mut [PrivateHtPrecinct],
    selection: Option<&[u8]>,
    limits: &ResourceLimits,
) -> Result<super::TilePacketDecode, DecodeError> {
    super::tile::validate_progression_layout(parts, grid, selection, limits)?;
    let first = parts
        .first()
        .ok_or_else(|| packet_reader_error(0, MalformedKind::InvalidTilePart))?;
    let input = super::tile::prepare_progression_payloads(parts, first.tile_index, limits)?;
    if input.all_lengths && input.declared_packets > grid.packet_count {
        return Err(packet_reader_error(0, MalformedKind::InvalidPacketLength));
    }
    let count = grid.total_precinct_count()?;
    if count > usize::MAX as u64 || precincts.len() != count as usize {
        return Err(invalid_packet_header());
    }
    let mut index = 0;
    while index < precincts.len() {
        if grid.precinct_index(0, precincts[index].resolution, 0)? != index {
            return Err(invalid_packet_header());
        }
        index += 1;
    }
    let params = super::ProgressionTileParameters {
        tile_parts: parts,
        grid,
        input: &input,
        selection,
        limits,
    };
    let mut p = super::tile::progression_tile_progress_new(&params)?;
    loop {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        super::tile::advance_progression_tile_part(&params, &mut p)?;
        if p.current_tile_part == parts.len()
            && p.packets == grid.packet_count
            && super::tile::all_progression_packets_seen(&p.seen)
        {
            break;
        }
        let Some(coordinate) = p.iterator.next_packet()? else {
            break;
        };
        if p.remaining_packets == 0 {
            return Err(packet_reader_error(
                0,
                MalformedKind::InvalidProgressionOrderChange,
            ));
        }
        p.remaining_packets -= 1;
        if p.current_tile_part == parts.len() {
            super::tile::omit_progression_packet(&params, &mut p, coordinate, precincts.len())?;
            continue;
        }
        execute_private_resolution_packet(&params, precincts, &mut p, coordinate)?;
    }
    super::tile::finish_progression_tile_packets(&params, &mut p)
}

fn execute_private_resolution_packet<'a, 'data>(
    params: &super::ProgressionTileParameters<'a, 'data>,
    precincts: &mut [PrivateHtPrecinct],
    p: &mut super::ProgressionTileProgress<'a>,
    coordinate: super::PacketCoordinate,
) -> Result<(), DecodeError> {
    let part = params
        .tile_parts
        .get(p.current_tile_part)
        .ok_or(DecodeError::MalformedInput {
            offset: params.input.payload_bytes,
            kind: MalformedKind::Truncated,
        })?;
    let slot = super::tile::progression_packet_slot(params.grid, coordinate);
    let duplicate = match slot {
        Ok((_, seen)) => match p.seen.get(seen) {
            Some(value) => *value,
            None => false,
        },
        Err(_) => false,
    };
    if duplicate {
        return Ok(());
    }
    if p.length_tile_part != p.current_tile_part {
        p.length_iterator = part.packet_lengths.iter();
        p.length_tile_part = p.current_tile_part;
    }
    let (index, seen) = slot?;
    let already = *p
        .seen
        .get(seen)
        .ok_or_else(|| packet_reader_error(p.offset, MalformedKind::InvalidPacketHeader))?;
    if !crate::refinement::progression_emit_allowed(already) {
        return Ok(());
    }
    let row = precincts
        .get_mut(index)
        .ok_or_else(|| packet_reader_error(p.offset, MalformedKind::InvalidPacketHeader))?;
    super::tile::set_progression_context_layer(&mut row.contexts, coordinate.layer)?;
    params
        .input
        .packed
        .get(p.current_tile_part)
        .ok_or_else(|| packet_reader_error(0, MalformedKind::InvalidTilePart))?;
    if let Some(counts) = params.selection {
        counts
            .get(usize::from(coordinate.component))
            .ok_or_else(|| packet_reader_error(0, MalformedKind::InvalidCodingStyle))?;
    }
    let sequence = (p.packets & u64::from(u16::MAX)) as u16;
    let (decoded, tile_bytes, packed_bytes) =
        row.decode_packet(part, p.offset, sequence, params.limits)?;
    super::tile::account_progression_packet(p, decoded, tile_bytes, packed_bytes, None, seen)
}

#[cfg(verus_keep_ghost)]
verus! {
    impl PrivateHtPrecinct {
        pub(crate) closed spec fn view(&self)->crate::specs::Part1PacketPrecinctState {
            crate::specs::Part1PacketPrecinctState {
                component:0,resolution:self.resolution,precinct:0,
                states:self.states@.map_values(|state:CodeBlockPacketState|super::code_block_packet_state_view(&state)),
                contexts:self.contexts@,
                decoders:self.decoders@.map_values(|decoder:PrivateHtDecoder|decoder.view()),
                subbands:self.subbands@.map_values(|subband:PacketSubbandState|super::packet_subband_view(&subband)),
            }
        }
        pub(crate) closed spec fn storage_view(&self)->crate::specs::PrivateHtPrecinctState {
            crate::specs::PrivateHtPrecinctState {
                logical:self.view(),
                packed:self.decoders@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view().packed),
            }
        }
        pub(crate) closed spec fn invariant(&self)->bool {
            forall|i:int|0<=i<self.decoders.len() ==> #[trigger] self.decoders@[i].invariant()
        }
        pub(crate) proof fn known_fields(&self)
            ensures self.storage_view().logical==self.view(),
                self.view().component==0,self.view().resolution==self.resolution,self.view().precinct==0,
                self.storage_view().packed.len()==self.view().decoders.len(),
                self.invariant() ==> forall|i:int|0<=i<self.view().decoders.len() ==>
                    #[trigger] crate::specs::private_ht_state_wf(crate::specs::PrivateHtDecoderState {
                        logical:self.view().decoders[i],packed:self.storage_view().packed[i],
                    }),
        {
            reveal(PrivateHtPrecinct::view);reveal(PrivateHtPrecinct::storage_view);reveal(PrivateHtPrecinct::invariant);
            assert forall|i:int|0<=i<self.view().decoders.len() && self.invariant() implies
                #[trigger] crate::specs::private_ht_state_wf(crate::specs::PrivateHtDecoderState {
                    logical:self.view().decoders[i],packed:self.storage_view().packed[i],
                }) by {
                self.decoders@[i].known_fields();
            }
        }
    }

    pub(crate) open spec fn private_precinct_outcome(result:Result<PrivateHtPrecinct,DecodeError>)
        ->Result<crate::specs::PrivateHtPrecinctState,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok(value.storage_view())}
    }
    closed spec fn private_execution_view(decoders:Seq<PrivateHtDecoder>,progress:&PacketBodyExecutionProgress)
        ->crate::specs::PrivatePacketBodyExecution {
        crate::specs::PrivatePacketBodyExecution {
            logical:crate::specs::Part1PacketBodyExecution {
                decoders:decoders.map_values(|d:PrivateHtDecoder|d.view()),index:progress.index,
                offset:progress.offset,segments:progress.segments,passes:progress.passes,
            },packed:decoders.map_values(|d:PrivateHtDecoder|d.storage_view().packed),
        }
    }
    closed spec fn private_packet_caps(limits:&ResourceLimits)->(u64,u64,u32,u64,u64,u64) {
        (crate::limits::resource_code_block_limit(limits),crate::limits::resource_packet_header_byte_limit(limits),
            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits))
    }
    closed spec fn private_header_view(header:PrecinctPayloadHeader<'_>)->crate::specs::Part2PlanePayloadHeader {
        let value=super::precinct_payload_header_view(header);
        crate::specs::Part2PlanePayloadHeader {
            packet:value.0.packet_data,reader:value.0.reader,contributions:value.1,count:value.2,
            present:value.0.present,sop:value.0.sop_bytes,
        }
    }
    impl PrivateHtPrecinct {
        closed spec fn tile_view(&self,p:&super::ProgressionTileProgress<'_>)->crate::specs::PrivateTileExecution {
            crate::specs::PrivateTileExecution {precinct:self.storage_view(),progress:super::progression_tile_progress_view(p)}
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires progress.index<=contributions.len(),
        forall|i:int|0<=i<decoders.len() ==> #[trigger] decoders@[i].invariant(),
    ensures final(decoders).len()==old(decoders).len(),
        forall|i:int|0<=i<final(decoders).len() ==> #[trigger] final(decoders)@[i].invariant(),
        crate::specs::private_packet_body_result(private_execution_view(old(decoders)@,old(progress)),
            super::packet_body_contributions_view(contributions),data@,error_offset,
            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),
            (result,private_execution_view(final(decoders)@,final(progress)))),
        result!=Err(DecodeError::AllocationFailed) ==>
            (result,private_execution_view(final(decoders)@,final(progress)))==crate::specs::private_packet_body_value(
                private_execution_view(old(decoders)@,old(progress)),super::packet_body_contributions_view(contributions),data@,error_offset,
                crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits)),
))]
fn execute_private_body(
    decoders: &mut [PrivateHtDecoder],
    contributions: &[Option<super::CodeBlockContribution>],
    data: &[u8],
    progress: &mut PacketBodyExecutionProgress,
    error_offset: usize,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial=private_execution_view(decoders@,progress);
        let ghost headers=super::packet_body_contributions_view(contributions);
        let ghost caps=(crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));
        let ghost mut prefix=Seq::<crate::specs::Part2Tier1StorageEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(private_execution_view);
        reveal(super::packet_body_contributions_view);reveal(super::code_block_contribution_view);
        assert forall|i:int|0<=i<decoders.len() implies #[trigger] crate::specs::private_ht_state_wf(
            crate::specs::PrivateHtDecoderState{logical:initial.logical.decoders[i],packed:initial.packed[i]}) by {
            decoders@[i].known_fields();
        }
        crate::specs::private_packet_body_value_fields(initial,headers,data@,error_offset,caps.0,caps.1,caps.2,caps.3);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant progress.index<=contributions.len(),
            decoders.len()==initial.logical.decoders.len(),
            decoders.len()==old(decoders).len(),
            initial==private_execution_view(old(decoders)@,old(progress)),
            headers==super::packet_body_contributions_view(contributions),
            caps==(crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits)),
            forall|i:int|0<=i<decoders.len() ==> #[trigger] decoders@[i].invariant(),
            crate::specs::private_packet_prefix(initial,private_execution_view(decoders@,progress),
                headers,data@,error_offset,caps.0,caps.1,caps.2,caps.3,prefix),
            crate::specs::private_packet_body_value(initial,headers,data@,error_offset,caps.0,caps.1,caps.2,caps.3)
                ==crate::specs::private_packet_body_value(private_execution_view(decoders@,progress),headers,data@,error_offset,caps.0,caps.1,caps.2,caps.3),
        decreases contributions.len()-progress.index,
    ))]
    while progress.index < contributions.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=private_execution_view(decoders@,progress);}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(private_execution_view);reveal(super::packet_body_contributions_view);
            reveal(super::code_block_contribution_view);
            reveal_with_fuel(crate::specs::private_packet_body_value,1);
        }
        if let Some(contribution) = contributions[progress.index] {
            let length = if contribution.data_length as u64 > usize::MAX as u64 {
                #[cfg(verus_keep_ghost)]
                proof! {crate::specs::private_packet_scalar_error(initial,before,headers,data@,error_offset,
                caps.0,caps.1,caps.2,caps.3,prefix,super::code_block_contribution_view(&contribution),
                crate::specs::part1_packet_reader_error(0,MalformedKind::ArithmeticOverflow));}
                return Err(packet_arithmetic_overflow());
            } else {
                contribution.data_length as usize
            };
            let end = match progress.offset.checked_add(length) {
                Some(end) => end,
                None => {
                    #[cfg(verus_keep_ghost)]
                    proof! {crate::specs::private_packet_scalar_error(initial,before,headers,data@,error_offset,
                    caps.0,caps.1,caps.2,caps.3,prefix,super::code_block_contribution_view(&contribution),
                    crate::specs::part1_packet_reader_error(0,MalformedKind::ArithmeticOverflow));}
                    return Err(packet_arithmetic_overflow());
                }
            };
            let body = match data.get(progress.offset..end) {
                Some(body) => body,
                None => {
                    #[cfg(verus_keep_ghost)]
                    proof! {crate::specs::private_packet_scalar_error(initial,before,headers,data@,error_offset,
                    caps.0,caps.1,caps.2,caps.3,prefix,super::code_block_contribution_view(&contribution),
                    DecodeError::MalformedInput{offset:error_offset as u64,kind:MalformedKind::Truncated});}
                    return Err(DecodeError::MalformedInput {
                        offset: error_offset as u64,
                        kind: MalformedKind::Truncated,
                    });
                }
            };
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost prior=decoders@;let ghost selected=progress.index;}
            #[cfg(verus_keep_ghost)]
            proof! {if selected<prior.len(){prior[selected as int].known_fields();}}
            let decoded = {
                let decoder = match decoders.get_mut(progress.index) {
                    Some(decoder) => decoder,
                    None => {
                        #[cfg(verus_keep_ghost)]
                        proof! {crate::specs::private_packet_scalar_error(initial,before,headers,data@,error_offset,
                        caps.0,caps.1,caps.2,caps.3,prefix,super::code_block_contribution_view(&contribution),
                        crate::specs::part1_packet_reader_error(0,MalformedKind::InvalidPacketHeader));}
                        return Err(invalid_packet_header());
                    }
                };
                decoder.decode(&contribution, body, limits)
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|i:int|0<=i<decoders.len() && i!=selected as int implies decoders@[i]==prior[i] by {};
                decoders@[selected as int].known_fields();
                let effect=(decoded,decoders@[selected as int].storage_view());
                assert(decoders@.map_values(|decoder:PrivateHtDecoder|decoder.view()) =~=
                    before.logical.decoders.update(selected as int,effect.1.logical));
                assert(decoders@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view().packed) =~=
                    before.packed.update(selected as int,effect.1.packed));
                crate::specs::private_packet_slot_observed(before,super::code_block_contribution_view(&contribution),data@,error_offset,
                    caps.0,caps.1,caps.2,caps.3,effect);
                let step=crate::specs::private_packet_after_body(before,super::code_block_contribution_view(&contribution),effect);
                prefix=crate::specs::private_packet_step(initial,before,headers,data@,error_offset,caps.0,caps.1,caps.2,caps.3,prefix,step);
                if decoded.is_err(){assert(private_execution_view(decoders@,progress)==step.1);}
            }
            let decoded = decoded?;
            progress.segments = progress
                .segments
                .checked_add(u32::from(decoded.segments))
                .ok_or_else(packet_arithmetic_overflow)?;
            progress.passes = progress
                .passes
                .checked_add(decoded.passes)
                .ok_or_else(packet_arithmetic_overflow)?;
            progress.offset = end;
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {prefix=crate::specs::private_packet_step(initial,before,headers,data@,error_offset,
            caps.0,caps.1,caps.2,caps.3,prefix,(Ok(()),before));}
        }
        progress.index = progress
            .index
            .checked_add(1)
            .ok_or_else(packet_arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::private_packet_finish(initial,private_execution_view(decoders@,progress),headers,data@,error_offset,
            caps.0,caps.1,caps.2,caps.3,prefix);
        reveal_with_fuel(crate::specs::private_packet_body_value,1);
    }
    Ok(())
}

#[allow(
    clippy::too_many_arguments,
    reason = "This decoder-free header stage binds the existing independent reader and source ranges."
)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires !parameters.packed,
    ensures result==crate::specs::part2_plane_payload_admit(super::precinct_payload_parameters_view(parameters),
        data@,packet_data@,super::packet_bit_reader_view(old(reader)),super::packet_body_contributions_view(contributions),sop_bytes),
))]
fn prepare_private_payload(
    reader: &mut super::PacketBitReader<'_>,
    packet_data: &[u8],
    data: &[u8],
    parameters: PrecinctPayloadParameters,
    contributions: &[Option<super::CodeBlockContribution>],
    sop_bytes: usize,
) -> Result<(usize, usize, usize, usize), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost initial=super::packet_bit_reader_view(reader);}
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(super::precinct_payload_parameters_view);reveal(super::packet_bit_reader_view);
        reveal(super::packet_body_contributions_view);
        reveal(crate::specs::part2_plane_payload_admit);
    }
    let finished = reader.finish_packet_header();
    #[cfg(verus_keep_ghost)]
    proof! {assert((finished,super::packet_bit_reader_view(reader))==crate::specs::part1_packet_reader_finish(initial));}
    finished?;
    let header = reader.bytes_consumed();
    #[cfg(verus_keep_ghost)]
    proof! {assert(header==crate::specs::part1_packet_reader_finish(initial).1.byte_index);}
    let mut tile = if parameters.packed {
        sop_bytes
    } else {
        sop_bytes
            .checked_add(header)
            .ok_or_else(packet_arithmetic_overflow)?
    };
    let mut packed = if parameters.packed { header } else { 0 };
    if parameters.eph {
        let end = header
            .checked_add(2)
            .ok_or_else(packet_arithmetic_overflow)?;
        let marker = match packet_data.get(header..end) {
            Some(marker) => marker,
            None => {
                #[cfg(verus_keep_ghost)]
                proof! {assert(end>packet_data.len());}
                return Err(packet_reader_error(
                    parameters.error_offset,
                    MalformedKind::Truncated,
                ));
            }
        };
        if !crate::refinement::eph_valid(marker[0], marker[1]) {
            return Err(invalid_packet_header());
        }
        if parameters.packed {
            packed = end;
        } else {
            tile = tile.checked_add(2).ok_or_else(packet_arithmetic_overflow)?;
        }
    }
    let mut preflight = PacketBodyPreflight {
        index: 0,
        end: tile,
    };
    super::body::preflight_packet_body_ranges(
        contributions,
        data,
        &mut preflight,
        (parameters.error_offset, 0),
    )?;
    Ok((header, tile, packed, preflight.end))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires _precinct.invariant(),crate::specs::private_grid_shape(super::packet_grid_view(grid)),
    ensures crate::specs::part2_packet_input_result(crate::codestream::tile_parts_owned_view(parts@),super::packet_grid_view(grid),
            seq![_precinct.view()],super::packet_selection_view(selection),limits,super::progression_tile_preparation_outcome(result)),
        super::progression_tile_preparation_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
            super::progression_tile_preparation_outcome(result)==crate::specs::part1_progression_tile_input_owned(
                crate::codestream::tile_parts_owned_view(parts@),super::packet_grid_view(grid),seq![_precinct.view()],
                super::packet_selection_view(selection),limits),
))]
fn prepare_private_input(
    parts: &[crate::codestream::TilePartPayload<'_>],
    grid: &super::PacketGrid,
    _precinct: &PrivateHtPrecinct,
    selection: Option<&[u8]>,
    limits: &ResourceLimits,
) -> Result<super::ProgressionTilePreparation, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        _precinct.known_fields();
        reveal(super::packet_grid_view);reveal(super::progression_tile_preparation_view);
        crate::specs::private_grid_layout_fields(super::packet_grid_view(grid),_precinct.view());
        crate::specs::part2_packet_input_normal(crate::codestream::tile_parts_owned_view(parts@),
            super::packet_grid_view(grid),seq![_precinct.view()],super::packet_selection_view(selection),limits);
    }
    super::tile::validate_progression_layout(parts, grid, selection, limits)?;
    let first = parts
        .first()
        .ok_or_else(|| packet_reader_error(0, MalformedKind::InvalidTilePart))?;
    let prepared = super::tile::prepare_progression_payloads(parts, first.tile_index, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=prepared {
            crate::specs::part2_packet_input_payload_error(crate::codestream::tile_parts_owned_view(parts@),
                super::packet_grid_view(grid),seq![_precinct.view()],super::packet_selection_view(selection),limits,error);
        }
    }
    let input = prepared?;
    if input.all_lengths && input.declared_packets > grid.packet_count {
        return Err(packet_reader_error(0, MalformedKind::InvalidPacketLength));
    }
    if grid.total_precinct_count()? != 1 || grid.precinct_index(0, 0, 0)? != 0 {
        return Err(invalid_packet_header());
    }
    Ok(input)
}

#[cfg(test)]
#[allow(
    clippy::items_after_test_module,
    reason = "Keep private transaction regressions adjacent to the owner definition."
)]
mod tests {
    use super::*;

    fn decoder() -> PrivateHtDecoder {
        let mut style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
        style.set_force_high_throughput(true);
        crate::tier1::new_private_ht_decoder(
            1,
            1,
            2,
            crate::tier1::SubbandOrientation::Ll,
            style,
            true,
            74,
        )
        .unwrap()
    }

    fn contribution() -> super::super::CodeBlockContribution {
        let mut segment_passes = [0; super::super::MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
        let mut segment_lengths = [0; super::super::MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION];
        segment_passes[0] = 1;
        segment_lengths[0] = 3;
        super::super::CodeBlockContribution {
            first_inclusion: true,
            zero_bitplanes: 0,
            new_passes: 1,
            data_length: 3,
            high_throughput: true,
            segment_count: 1,
            segment_passes,
            segment_lengths,
        }
    }

    #[test]
    fn private_primary_transaction_retention_and_materialization_refusals_roll_back() {
        let limits = ResourceLimits::default();
        let contribution = contribution();
        let mut observed_refusal = false;
        let mut observed_success = false;
        for after in 0..16 {
            let mut actual = decoder();
            let before = format!("{actual:?}");
            let result = crate::allocation::with_refusal(after, || {
                actual.decode(&contribution, &[0, 0x63, 0], &limits)
            });
            match result {
                Err(DecodeError::AllocationFailed) => {
                    observed_refusal = true;
                    assert_eq!(format!("{actual:?}"), before);
                }
                Ok(_) => {
                    observed_success = true;
                    assert_eq!(actual.dimensions(), (1, 1));
                    assert_eq!(actual.collect().unwrap().len(), 1);
                }
                Err(error) => panic!("unexpected refusal result: {error:?}"),
            }
        }
        assert!(observed_refusal && observed_success);
        let mut actual = decoder();
        let before = format!("{actual:?}");
        assert!(
            actual
                .decode(&contribution, &[0xff, 0xff, 0xff], &limits)
                .is_err()
        );
        assert_eq!(format!("{actual:?}"), before);
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires forall|i:int|0<=i<decoders.len() ==> #[trigger] decoders@[i].invariant(),
    ensures crate::specs::private_precinct_initial_result(crate::specs::PrivatePrecinctInitialContext {
            across,down,maximum_zero,style,decoders:decoders@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view()),
            blocks:crate::limits::resource_code_block_limit(limits),work:crate::limits::resource_work_limit(limits),
            tag_nodes:crate::limits::resource_tag_tree_node_limit(limits),
        },private_precinct_outcome(result)),
        private_precinct_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
            private_precinct_outcome(result)==crate::specs::private_precinct_initial_value(crate::specs::PrivatePrecinctInitialContext {
                across,down,maximum_zero,style,decoders:decoders@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view()),
                blocks:crate::limits::resource_code_block_limit(limits),work:crate::limits::resource_work_limit(limits),
                tag_nodes:crate::limits::resource_tag_tree_node_limit(limits),
            }),
        match result{Ok(value)=>value.invariant(),Err(_)=>true},
))]
pub(crate) fn new_private_ht_precinct(
    across: u32,
    down: u32,
    maximum_zero: u16,
    style: Tier1CodingStyle,
    decoders: Vec<PrivateHtDecoder>,
    limits: &ResourceLimits,
) -> Result<PrivateHtPrecinct, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost ctx=crate::specs::PrivatePrecinctInitialContext {
            across,down,maximum_zero,style,decoders:decoders@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view()),
            blocks:crate::limits::resource_code_block_limit(limits),work:crate::limits::resource_work_limit(limits),
            tag_nodes:crate::limits::resource_tag_tree_node_limit(limits),
        };
        let ghost root=|events|crate::specs::private_precinct_initial_run(ctx,events);
        let ghost mut prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::private_precinct_initial_normal(ctx);
        assert forall|i:int|0<=i<decoders.len() implies #[trigger] decoders@[i].storage_view().logical==decoders@[i].view() by {
            decoders@[i].known_fields();
        }
        assert(ctx.decoders.map_values(|decoder:crate::specs::PrivateHtDecoderState|decoder.logical) =~=
            decoders@.map_values(|decoder:PrivateHtDecoder|decoder.view()));
        assert(ctx.decoders.map_values(|decoder:crate::specs::PrivateHtDecoderState|decoder.packed) =~=
            decoders@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view().packed));
        assert((across as int)*(down as int)<=u64::MAX) by(nonlinear_arith)
            requires across<=u32::MAX,down<=u32::MAX;
    }
    if across == 0
        || down == 0
        || maximum_zero == 0
        || maximum_zero > crate::tier1::MAX_TIER1_BITPLANES
    {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateHtPrecinctState>(
        Err(crate::specs::part1_packet_header_error()));}
        return Err(invalid_packet_header());
    }
    let count = u64::from(across)
        .checked_mul(u64::from(down))
        .ok_or_else(packet_arithmetic_overflow)?;
    if count > limits.maximum_code_blocks() {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateHtPrecinctState>(Err(DecodeError::LimitExceeded {
            resource:Resource::CodeBlocks,limit:ctx.blocks,actual:count,
        }));}
        return Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlocks,
            limit: limits.maximum_code_blocks(),
            actual: count,
        });
    }
    if count > limits.maximum_work_units() {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateHtPrecinctState>(Err(DecodeError::LimitExceeded {
            resource:Resource::WorkUnits,limit:ctx.work,actual:count,
        }));}
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: count,
        });
    }
    if count > usize::MAX as u64 {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateHtPrecinctState>(Err(crate::specs::part1_packet_reader_error(0,MalformedKind::ArithmeticOverflow)));}
        return Err(packet_arithmetic_overflow());
    }
    let count = count as usize;
    if count != decoders.len() {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateHtPrecinctState>(
        Err(crate::specs::part1_packet_header_error()));}
        return Err(invalid_packet_header());
    }
    #[cfg(verus_keep_ghost)]
    proof! {assert(crate::specs::private_precinct_admit(ctx)==Ok(count));}
    let prepared = super::precinct::prepare_precinct_contexts(
        Vec::new(),
        Vec::new(),
        count,
        across,
        maximum_zero,
        style,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_precinct_contexts_result);
        reveal(super::precinct_contexts_outcome);
        assert(super::packet_states_view(Seq::<CodeBlockPacketState>::empty()) =~= Seq::empty());
        crate::specs::part2_decode_eta(
            |events|crate::specs::part2_precinct_contexts_run(Seq::empty(),Seq::empty(),count,across,maximum_zero,style,events),
            super::precinct_contexts_outcome(prepared));
        let child=|events|crate::specs::part2_precinct_contexts_run(Seq::empty(),Seq::empty(),count,across,maximum_zero,style,events);
        let next=|value,rest|crate::specs::private_precinct_after_contexts(ctx,value,rest);
        if let Err(error)=prepared {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(value)=super::precinct_contexts_outcome(prepared) {
            prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,value);
        }
    }
    let (states, contexts) = prepared?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost initial=(super::packet_states_view(states@),contexts@);}
    let reserved = crate::allocation::empty_with_capacity(1);
    #[cfg(verus_keep_ghost)]
    proof! {
        let context=crate::specs::PrivateOwnerCapacityContext::PrecinctSubband{source:ctx};
        crate::specs::private_owner_capacity_observed(context,match reserved{Ok(_)=>Ok(()),Err(error)=>Err(error)});
        let child=|events|crate::specs::private_owner_capacity_run(context,events);
        let next=|_:(),rest|crate::specs::private_precinct_after_capacity(ctx,initial,rest);
        if let Err(error)=reserved {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if reserved.is_ok(){prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,());}
    }
    let mut subbands = reserved?;
    let inclusion = super::tag_tree::tag_tree_new(across, down, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::private_precinct_tree_observed(ctx,true,super::tag_tree_outcome(inclusion));
        let child=|events|crate::specs::private_precinct_tree_run(ctx,true,events);
        let next=|tree,rest|crate::specs::private_precinct_after_inclusion(ctx,initial,tree,rest);
        if let Err(error)=inclusion {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(tree)=super::tag_tree_outcome(inclusion) {
            prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,tree);
        }
    }
    let inclusion_tree = inclusion?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost inclusion=super::tag_tree_view(&inclusion_tree);}
    let zero = super::tag_tree::tag_tree_new(across, down, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::private_precinct_tree_observed(ctx,false,super::tag_tree_outcome(zero));
        let child=|events|crate::specs::private_precinct_tree_run(ctx,false,events);
        let next=|tree,rest|Some((Ok::<crate::specs::PrivateHtPrecinctState,DecodeError>(crate::specs::private_precinct_initial_state(ctx,initial,inclusion,tree)),rest));
        if let Err(error)=zero {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
    }
    let zero_bitplane_tree = zero?;
    subbands.push(PacketSubbandState {
        orientation: crate::tier1::SubbandOrientation::Ll,
        first_decoder: 0,
        decoder_count: count,
        code_blocks_across: across,
        code_blocks_down: down,
        inclusion_tree,
        zero_bitplane_tree,
    });
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(PrivateHtPrecinct::view);reveal(PrivateHtPrecinct::storage_view);reveal(PrivateHtPrecinct::invariant);
        reveal(super::packet_subband_view);
        let result=Ok(crate::specs::private_precinct_initial_state(ctx,initial,inclusion,super::tag_tree_view(&subbands@[0].zero_bitplane_tree)));
        let child=|events|crate::specs::private_precinct_tree_run(ctx,false,events);
        crate::specs::part2_cold_pure(result);
        let calls=crate::specs::part2_cold_witness(child,Ok(super::tag_tree_view(&subbands@[0].zero_bitplane_tree)));
        assert forall|tail|root((prefix+calls)+tail)==Some((result,tail)) by {
            assert((prefix+calls)+tail =~= prefix+(calls+tail));
            crate::specs::part2_cold_prefix_at(child,calls,Ok(super::tag_tree_view(&subbands@[0].zero_bitplane_tree)),tail);
        }
        assert(crate::specs::part2_cold_prefix(root,prefix+calls,result));
    }
    let precinct = PrivateHtPrecinct {
        resolution: 0,
        states,
        contexts,
        subbands,
        decoders,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        precinct.known_fields();
        let expected=crate::specs::private_precinct_initial_state(ctx,initial,inclusion,
            super::tag_tree_view(&precinct.subbands@[0].zero_bitplane_tree));
        assert(precinct.view().decoders =~= expected.logical.decoders);
        assert(precinct.storage_view().packed =~= expected.packed);
        assert(precinct.view().subbands =~= expected.logical.subbands);
        assert(precinct.storage_view()==expected);
    }
    Ok(precinct)
}

impl PrivateHtPrecinct {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures match result{Ok(decoder)=>index<self.view().decoders.len()
            && decoder.view()==self.view().decoders[index as int]
            && decoder.storage_view().packed==self.storage_view().packed[index as int]
            && (self.invariant() ==> decoder.invariant()),
            Err(error)=>index>=self.view().decoders.len() && error==crate::specs::part1_packet_header_error()},
    ))]
    pub(crate) fn decoder(&self, index: usize) -> Result<&PrivateHtDecoder, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(PrivateHtPrecinct::view);reveal(PrivateHtPrecinct::storage_view);reveal(PrivateHtPrecinct::invariant);}
        self.decoders.get(index).ok_or_else(invalid_packet_header)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.invariant(),
            matches!(crate::codestream::tile_part_owned_view(part).packed_packet_headers.source,crate::specs::Part1PackedHeaderSource::None),
        ensures final(self).invariant(),
            crate::specs::private_precinct_packet_result(crate::specs::PrivatePrecinctPacketContext {
                before:old(self).storage_view(),part:crate::codestream::tile_part_owned_view(part),offset:error_offset,sequence,caps:private_packet_caps(limits),
            },(result,final(self).storage_view())),
            result!=Err(DecodeError::AllocationFailed) ==> (result,final(self).storage_view())==
                crate::specs::private_precinct_packet_value(crate::specs::PrivatePrecinctPacketContext {
                    before:old(self).storage_view(),part:crate::codestream::tile_part_owned_view(part),offset:error_offset,sequence,caps:private_packet_caps(limits),
                }),
    ))]
    fn decode_packet(
        &mut self,
        part: &crate::codestream::TilePartPayload<'_>,
        error_offset: usize,
        sequence: u16,
        limits: &ResourceLimits,
    ) -> Result<(PacketBodyDecode, usize, usize), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost ctx=crate::specs::PrivatePrecinctPacketContext {
            before:self.storage_view(),part:crate::codestream::tile_part_owned_view(part),offset:error_offset,
            sequence,caps:private_packet_caps(limits),
        };}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(PrivateHtPrecinct::view);reveal(PrivateHtPrecinct::storage_view);reveal(PrivateHtPrecinct::invariant);
            reveal(crate::codestream::tile_part_owned_view);reveal(private_packet_caps);
            crate::codestream::coding_style_known_packet_markers(&part.coding_style);
            self.known_fields();
            crate::specs::private_precinct_packet_normal(ctx);
        }
        if self.states.len() != self.contexts.len()
            || self.states.len() != self.decoders.len()
            || self.states.is_empty() != self.subbands.is_empty()
        {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::private_packet_admit_error(ctx,crate::specs::part1_packet_header_error());}
            return Err(invalid_packet_header());
        }
        let count = self.decoders.len() as u64;
        if count > limits.maximum_code_blocks() {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::private_packet_admit_error(ctx,DecodeError::LimitExceeded {
                resource:Resource::CodeBlocks,limit:ctx.caps.0,actual:count,
            });}
            return Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlocks,
                limit: limits.maximum_code_blocks(),
                actual: count,
            });
        }
        if count > limits.maximum_work_units() {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::private_packet_admit_error(ctx,DecodeError::LimitExceeded {
                resource:Resource::WorkUnits,limit:ctx.caps.5,actual:count,
            });}
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: limits.maximum_work_units(),
                actual: count,
            });
        }
        let data = match part.data.get(error_offset..) {
            Some(data) => data,
            None => {
                #[cfg(verus_keep_ghost)]
                proof! {crate::specs::private_packet_admit_error(ctx,
                crate::specs::part1_packet_reader_error(error_offset,MalformedKind::InvalidPacketLength));}
                return Err(packet_reader_error(
                    error_offset,
                    MalformedKind::InvalidPacketLength,
                ));
            }
        };
        let style = part
            .component_coding_styles
            .style(0)?
            .tier1_coding_style()?;
        let parameters = PrecinctPayloadParameters {
            error_offset,
            packed_offset: 0,
            expected_packet_length: None,
            expected_sop_sequence: sequence,
            style,
            sop: part.coding_style.sop_markers,
            eph: part.coding_style.eph_markers,
            packed: false,
            decode_tier1: true,
        };
        let result = self.decode_payload(data, parameters, limits);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::private_packet_payload_observed(ctx,super::precinct_payload_parameters_view(parameters),(result,self.storage_view()));}
        result
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.invariant(),!parameters.packed,parameters.decode_tier1,parameters.expected_packet_length.is_none(),
        ensures final(self).invariant(),
            crate::specs::private_payload_result(old(self).storage_view(),data@,super::precinct_payload_parameters_view(parameters),
                private_packet_caps(limits),(result,final(self).storage_view())),
            result!=Err(DecodeError::AllocationFailed) ==> (result,final(self).storage_view())==
                crate::specs::private_payload_value(old(self).storage_view(),data@,super::precinct_payload_parameters_view(parameters),private_packet_caps(limits)),
    ))]
    fn decode_payload(
        &mut self,
        data: &[u8],
        parameters: PrecinctPayloadParameters,
        limits: &ResourceLimits,
    ) -> Result<(PacketBodyDecode, usize, usize), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before=self.storage_view();
            let ghost p=super::precinct_payload_parameters_view(parameters);
            let ghost caps=private_packet_caps(limits);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(PrivateHtPrecinct::view);reveal(PrivateHtPrecinct::storage_view);reveal(PrivateHtPrecinct::invariant);
            reveal(private_packet_caps);
            reveal(super::precinct_payload_parameters_view);reveal(super::precinct_payload_reader_view);
            reveal(super::precinct_header_view);reveal(super::packet_body_contributions_view);
            reveal(super::packet_subband_view);reveal(super::packet_bit_reader_view);
            reveal(private_header_view);reveal(super::precinct_payload_header_view);
        }
        let prefixed =
            super::precinct::decode_precinct_packet_payload_prefix(data, &[], parameters, limits);
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=prefixed {crate::specs::private_payload_prefix_error(before,data@,p,caps,error);}}
        let prefix = prefixed?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost input=super::precinct_payload_reader_view(prefix);}
        let mut reader = prefix.reader;
        let allocated = if self.states.is_empty() {
            Ok(Vec::new())
        } else {
            crate::allocation::none_values(self.states.len())
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let context=crate::specs::Part2PrecinctContributionsContext {
                state:before.logical,data:data@,packed:Seq::empty(),parameters:p,header_limit:caps.1,work:caps.5,
            };
            crate::specs::part2_precinct_contributions_observed(context,match allocated{Ok(_)=>Ok(()),Err(error)=>Err(error)});
            if let Err(error)=allocated {crate::specs::private_payload_capacity_error(before,data@,p,caps,error);}
        }
        let mut contributions = allocated?;
        let mut progress = PrecinctHeaderProgress {
            subband_index: 0,
            local_index: 0,
            contribution_count: 0,
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial=crate::specs::Part1PrecinctHeaderState {
                states:before.logical.states,subbands:before.logical.subbands,
                contributions:Seq::new(before.logical.states.len(),|_:int|None),
                reader:input.reader,subband_index:0,local_index:0,contribution_count:0,
            };
            let ghost headers=if input.present && before.logical.contexts.len()>0 {
                crate::specs::part1_precinct_headers(initial,before.logical.contexts,before.logical.contexts[0].layer,p.style)
            }else{(Ok(()),initial)};
        }
        if prefix.present && !self.contexts.is_empty() {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(super::packet_states_view(self.states@)==initial.states);
                assert(self.subbands@.map_values(|band:PacketSubbandState|super::packet_subband_view(&band))==initial.subbands);
                assert(contributions@.map_values(|value:Option<super::CodeBlockContribution>|super::code_block_contribution_option_view(value))==
                    initial.contributions);
                assert(super::packet_bit_reader_view(&reader)==initial.reader);
            }
            let layer = self
                .contexts
                .first()
                .ok_or_else(invalid_packet_header)?
                .layer;
            let decoded = super::precinct::decode_precinct_contribution_headers(
                &mut self.states,
                &self.contexts,
                &mut self.subbands,
                &mut contributions,
                &mut reader,
                PrecinctHeaderParameters {
                    layer,
                    style: parameters.style,
                },
                &mut progress,
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::private_unit_result_fields(decoded);
                if let Err(error)=decoded {
                    crate::specs::private_prepared_header_error(before,data@,p,caps,self.storage_view(),error);
                    crate::specs::private_payload_capacity_observed(before,data@,p,caps,(Err(error),self.storage_view()));
                }else{assert(headers.0==Ok(()));
                }
            }
            decoded?;
        }
        let header = PrecinctPayloadHeader {
            prefix: PrecinctPayloadReader {
                reader,
                packet_data: prefix.packet_data,
                present: prefix.present,
                sop_bytes: prefix.sop_bytes,
            },
            contributions,
            contribution_count: progress.contribution_count,
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost h=private_header_view(header);let ghost prepared=self.storage_view();}
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(h.packet==input.packet_data && h.present==input.present && h.sop==input.sop_bytes);
            assert(h.reader==headers.1.reader);
            assert(h.contributions==headers.1.contributions && h.count==headers.1.contribution_count);
            assert(prepared.logical.states==headers.1.states && prepared.logical.subbands==headers.1.subbands);
        }
        let result = self.decode_after_headers(data, parameters, header, limits);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::private_payload_prepared_observed(before,data@,p,caps,h,prepared,(result,self.storage_view()));
            crate::specs::private_payload_capacity_observed(before,data@,p,caps,(result,self.storage_view()));
        }
        result
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.invariant(),!parameters.packed,parameters.decode_tier1,parameters.expected_packet_length.is_none(),
        ensures final(self).invariant(),
            crate::specs::private_payload_after_result(old(self).storage_view(),super::precinct_payload_parameters_view(parameters),data@,
                private_header_view(header),private_packet_caps(limits),(result,final(self).storage_view())),
            result!=Err(DecodeError::AllocationFailed) ==> (result,final(self).storage_view())==
                crate::specs::private_payload_after_value(old(self).storage_view(),super::precinct_payload_parameters_view(parameters),data@,
                    private_header_view(header),private_packet_caps(limits)),
    ))]
    fn decode_after_headers(
        &mut self,
        data: &[u8],
        parameters: PrecinctPayloadParameters,
        header: PrecinctPayloadHeader<'_>,
        limits: &ResourceLimits,
    ) -> Result<(PacketBodyDecode, usize, usize), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before=self.storage_view();let ghost h=private_header_view(header);
            let ghost p=super::precinct_payload_parameters_view(parameters);let ghost caps=private_packet_caps(limits);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(PrivateHtPrecinct::view);reveal(PrivateHtPrecinct::storage_view);reveal(PrivateHtPrecinct::invariant);
            reveal(private_packet_caps);reveal(private_header_view);reveal(super::precinct_payload_header_view);
            reveal(super::precinct_payload_reader_view);
        }
        let count = self.states.len() as u64;
        let error_offset = parameters.error_offset;
        let mut reader = header.prefix.reader;
        let packet_data = header.prefix.packet_data;
        let packet_present = header.prefix.present;
        let sop_bytes = header.prefix.sop_bytes;
        let contributions = header.contributions;
        let contribution_count = header.contribution_count;
        let prepared = prepare_private_payload(
            &mut reader,
            packet_data,
            data,
            parameters,
            &contributions,
            sop_bytes,
        );
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=prepared{crate::specs::private_payload_after_error(before,p,data@,h,caps,error);}}
        let args = prepared?;
        let header_bytes = args.0;
        let body_start = args.1;
        let offset = args.3;
        let mut execution = PacketBodyExecutionProgress {
            index: 0,
            offset: body_start,
            segments: 0,
            passes: 0,
        };
        let executed = execute_private_body(
            &mut self.decoders,
            &contributions,
            data,
            &mut execution,
            error_offset,
            limits,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::private_after_executed(before,p,data@,h,caps,args,
                (executed,private_execution_view(self.decoders@,&execution)));
        }
        executed?;
        if count > u64::from(u32::MAX) {
            return Err(packet_arithmetic_overflow());
        }
        if header_bytes > u32::MAX as usize {
            return Err(packet_arithmetic_overflow());
        }
        let body_bytes = offset
            .checked_sub(body_start)
            .ok_or_else(packet_arithmetic_overflow)?;
        if body_bytes > u32::MAX as usize {
            return Err(packet_arithmetic_overflow());
        }
        if offset > u32::MAX as usize {
            return Err(packet_arithmetic_overflow());
        }
        Ok((
            PacketBodyDecode {
                present: packet_present,
                code_blocks: count as u32,
                contributions: contribution_count,
                segments: execution.segments,
                passes: execution.passes,
                header_bytes: header_bytes as u32,
                body_bytes: body_bytes as u32,
                bytes_consumed: offset as u32,
            },
            offset,
            0,
        ))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.invariant(),
            crate::specs::private_tile_parameters(super::progression_tile_parameters_view(params)),
            super::progression_tile_progress_view(p).packed_offset==0,
        ensures final(self).invariant(),super::progression_tile_progress_view(final(p)).packed_offset==0,
            crate::specs::private_tile_packet_result(super::progression_tile_parameters_view(params),
                old(self).tile_view(old(p)),coordinate,(result,final(self).tile_view(final(p)))),
            result!=Err(DecodeError::AllocationFailed) ==>
                (result,final(self).tile_view(final(p)))==crate::specs::private_tile_packet_value(
                    super::progression_tile_parameters_view(params),old(self).tile_view(old(p)),coordinate),
    ))]
    fn execute_packet<'a, 'data>(
        &mut self,
        params: &super::ProgressionTileParameters<'a, 'data>,
        p: &mut super::ProgressionTileProgress<'a>,
        coordinate: super::PacketCoordinate,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before=self.tile_view(p);
            let ghost context=super::progression_tile_parameters_view(params);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(PrivateHtPrecinct::tile_view);self.known_fields();
            crate::specs::private_tile_packet_value_fields(context,before,coordinate);
            if let crate::specs::Part2PlaneTileAdmission::Return(result)=
                crate::specs::part2_plane_tile_packet_admit(context,crate::specs::private_tile_logical(before),coordinate) {
                crate::specs::private_tile_packet_scalar(context,before,coordinate,result);
            }
        }
        let part =
            params
                .tile_parts
                .get(p.current_tile_part)
                .ok_or(DecodeError::MalformedInput {
                    offset: params.input.payload_bytes,
                    kind: MalformedKind::Truncated,
                })?;
        let slot = super::tile::progression_packet_slot(params.grid, coordinate);
        let duplicate = match slot {
            Ok((_, seen)) => match p.seen.get(seen) {
                Some(seen) => *seen,
                None => false,
            },
            Err(_) => false,
        };
        if duplicate {
            return Ok(());
        }
        if p.length_tile_part != p.current_tile_part {
            p.length_iterator = part.packet_lengths.iter();
            p.length_tile_part = p.current_tile_part;
        }
        let (index, seen) = slot?;
        let already = match p.seen.get(seen) {
            Some(seen) => *seen,
            None => {
                return Err(packet_reader_error(
                    p.offset,
                    MalformedKind::InvalidPacketHeader,
                ));
            }
        };
        if !crate::refinement::progression_emit_allowed(already) {
            return Ok(());
        }
        if index != 0 {
            return Err(packet_reader_error(
                p.offset,
                MalformedKind::InvalidPacketHeader,
            ));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost admitted=crate::specs::private_tile_logical(self.tile_view(p));}
        super::tile::set_progression_context_layer(&mut self.contexts, coordinate.layer)?;
        let _packed = params
            .input
            .packed
            .get(p.current_tile_part)
            .ok_or_else(|| packet_reader_error(0, MalformedKind::InvalidTilePart))?;
        if let Some(counts) = params.selection {
            let _count = counts
                .get(usize::from(coordinate.component))
                .ok_or_else(|| packet_reader_error(0, MalformedKind::InvalidCodingStyle))?;
        }
        let packet_number = p.packets;
        #[cfg(verus_keep_ghost)]
        proof! {assert(packet_number&65535u64<=65535u64) by(bit_vector);}
        let sequence = u16::try_from(packet_number & u64::from(u16::MAX))
            .map_err(|_| packet_arithmetic_overflow())?;
        let packet = self.decode_packet(part, p.offset, sequence, params.limits);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::private_tile_packet_observed(context,before,coordinate,admitted,
        crate::codestream::tile_part_owned_view(part),seen,(packet,self.storage_view()));}
        let (decoded, tile_bytes, packed_bytes) = packet?;
        super::tile::account_progression_packet(p, decoded, tile_bytes, packed_bytes, None, seen)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.invariant(),crate::specs::private_tile_parameters(super::progression_tile_parameters_view(params)),
            super::progression_tile_progress_view(p).packed_offset==0,
        ensures final(self).invariant(),super::progression_tile_progress_view(final(p)).packed_offset==0,
            crate::specs::private_tile_run_result(super::progression_tile_parameters_view(params),
                old(self).tile_view(old(p)),(result,final(self).tile_view(final(p)))),
            result!=Err(DecodeError::AllocationFailed) ==> (result,final(self).tile_view(final(p)))==
                crate::specs::private_tile_value(super::progression_tile_parameters_view(params),old(self).tile_view(old(p))),
    ))]
    fn run_tile<'a, 'data>(
        &mut self,
        params: &super::ProgressionTileParameters<'a, 'data>,
        p: &mut super::ProgressionTileProgress<'a>,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial=self.tile_view(p);
            let ghost context=super::progression_tile_parameters_view(params);
            let ghost mut prefix=Seq::<crate::specs::Part2Tier1StorageEvent>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            self.known_fields();reveal(PrivateHtPrecinct::tile_view);
            reveal(super::progression_tile_progress_view);reveal(super::progression_tile_parameters_view);
            crate::specs::private_tile_value_fields(context,initial);
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant self.invariant(),super::progression_tile_progress_view(p).packed_offset==0,
                initial==old(self).tile_view(old(p)),
                context==super::progression_tile_parameters_view(params),
                crate::specs::private_tile_parameters(context),
                forall|calls| #[trigger] crate::specs::private_tile_run(context,initial,prefix+calls)
                    ==crate::specs::private_tile_run(context,self.tile_view(p),calls),
                crate::specs::private_tile_value(context,initial)==crate::specs::private_tile_value(context,self.tile_view(p)),
            decreases p.remaining_packets,
        ))]
        loop {
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before=self.tile_view(p);}
            #[cfg(verus_keep_ghost)]
            proof! {
                self.known_fields();
                reveal(PrivateHtPrecinct::tile_view);
                reveal(super::progression_tile_progress_view);reveal(super::progression_tile_parameters_view);
                crate::specs::private_tile_step_fields(context,before);
                reveal_with_fuel(crate::specs::private_tile_value,1);
                if let crate::specs::Part2PlaneTileStep::Return(result)=
                    crate::specs::part2_plane_tile_run_admit(context,crate::specs::private_tile_logical(before)) {
                    crate::specs::private_tile_run_scalar(context,before,result);
                    assert(crate::specs::part2_tier1_phase(|calls|crate::specs::private_tile_run(context,initial,calls),prefix,
                        |calls|Some((Ok((result.0,crate::specs::PrivateTileExecution{precinct:before.precinct,progress:result.1.progress})),calls))));
                    crate::specs::part2_tier1_prefix_finish(|calls|crate::specs::private_tile_run(context,initial,calls),prefix,
                        Ok((result.0,crate::specs::PrivateTileExecution{precinct:before.precinct,progress:result.1.progress})));
                }
            }
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint()?;
            super::tile::advance_progression_tile_part(params, p)?;
            if p.current_tile_part == params.tile_parts.len()
                && p.packets == params.grid.packet_count
                && super::tile::all_progression_packets_seen(&p.seen)
            {
                return Ok(());
            }
            let Some(coordinate) = p.iterator.next_packet()? else {
                return Ok(());
            };
            if p.remaining_packets == 0 {
                return Err(packet_reader_error(
                    0,
                    MalformedKind::InvalidProgressionOrderChange,
                ));
            }
            p.remaining_packets -= 1;
            if p.current_tile_part == params.tile_parts.len() {
                super::tile::omit_progression_packet(params, p, coordinate, 1)?;
                #[cfg(verus_keep_ghost)]
                proof! {crate::specs::private_tile_run_continue(context,before,crate::specs::private_tile_logical(self.tile_view(p)));}
                continue;
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost packet_before=self.tile_view(p);}
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::private_tile_run_packet_step(context,before,coordinate,crate::specs::private_tile_logical(packet_before));}
            let decoded = self.execute_packet(params, p, coordinate);
            #[cfg(verus_keep_ghost)]
            proof! {prefix=crate::specs::private_tile_prefix_observed(context,initial,packet_before,coordinate,
            before.progress.remaining_packets,prefix,(decoded,self.tile_view(p)));}
            decoded?;
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.invariant(),parts.len()==1,crate::specs::private_grid_shape(super::packet_grid_view(grid)),
            (match crate::codestream::tile_parts_owned_view(parts@)[0].packed_packet_headers.source{crate::specs::Part1PackedHeaderSource::None=>true,_=>false}),
            (match crate::codestream::tile_parts_owned_view(parts@)[0].packet_lengths.source{crate::specs::Part1PacketLengthSource::None=>true,_=>false}),
            selection.is_none() || super::packet_selection_view(selection)==Some(seq![1u8]),
        ensures final(self).invariant(),
            crate::specs::private_packet_decode_result(crate::codestream::tile_parts_owned_view(parts@),super::packet_grid_view(grid),
                old(self).storage_view(),super::packet_selection_view(selection),limits,(result,final(self).storage_view())),
            result!=Err(DecodeError::AllocationFailed) ==> (result,final(self).storage_view())==
                crate::specs::private_packet_decode_value(crate::codestream::tile_parts_owned_view(parts@),super::packet_grid_view(grid),
                    old(self).storage_view(),super::packet_selection_view(selection),limits),
            result!=Err(DecodeError::AllocationFailed) ==> (result,seq![final(self).view()])==
                crate::specs::part1_progression_tile_decode_owned(crate::codestream::tile_parts_owned_view(parts@),super::packet_grid_view(grid),
                    seq![old(self).view()],super::packet_selection_view(selection),limits),
    ))]
    pub(crate) fn decode_tile(
        &mut self,
        parts: &[crate::codestream::TilePartPayload<'_>],
        grid: &super::PacketGrid,
        selection: Option<&[u8]>,
        limits: &ResourceLimits,
    ) -> Result<super::TilePacketDecode, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before=self.storage_view();let ghost source=crate::codestream::tile_parts_owned_view(parts@);
            let ghost shape=super::packet_grid_view(grid);let ghost selected=super::packet_selection_view(selection);
        }
        #[cfg(verus_keep_ghost)]
        proof! {self.known_fields();crate::specs::private_packet_decode_value_fields(source,shape,before,selected,limits);}
        let prepared = prepare_private_input(parts, grid, self, selection, limits);
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=prepared{crate::specs::private_packet_input_error(source,shape,before,selected,limits,error);}}
        let input = prepared?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost input_value=super::progression_tile_preparation_view(&input);}
        let params = super::ProgressionTileParameters {
            tile_parts: parts,
            grid,
            input: &input,
            selection,
            limits,
        };
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::private_packet_input_parameters(source,shape,before,selected,limits,input_value);}
        let initialized = super::tile::progression_tile_progress_new(&params);
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=initialized{crate::specs::private_packet_progress_error(source,shape,before,selected,limits,input_value,error);}}
        let mut p = initialized?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost initial=super::progression_tile_progress_view(&p);}
        let decoded = self.run_tile(&params, &mut p);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::private_packet_decode_observed(source,shape,before,selected,limits,input_value,initial,(decoded,self.tile_view(&p)));}
        decoded?;
        super::tile::finish_progression_tile_packets(&params, &mut p)
    }
}
