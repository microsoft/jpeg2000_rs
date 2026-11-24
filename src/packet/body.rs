use super::errors::{packet_arithmetic_overflow, packet_invalid_code_block, packet_reader_error};
use super::{
    CodeBlockBodyDecode, CodeBlockContribution, CodeBlockSegmentContribution, DecodeError,
    HtBodyProgress, MalformedKind, PacketBodyExecutionProgress, PacketBodyPreflight,
    ResourceLimits, Tier1CodeBlockDecoder,
};
#[cfg(verus_keep_ghost)]
use super::{
    code_block_contribution_view, ht_body_progress_view, legacy_packet_progress_view,
    packet_body_contributions_view, packet_body_execution_view, packet_body_preflight_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, packet_body_preflight_view(final(progress))) == crate::specs::part1_packet_body_preflight_at(
        packet_body_preflight_view(old(progress)), packet_body_contributions_view(contributions), data@, error_offsets.0,error_offsets.1),
        error_offsets.1==0 ==> (result,packet_body_preflight_view(final(progress)))==crate::specs::part1_packet_body_preflight(
            packet_body_preflight_view(old(progress)),packet_body_contributions_view(contributions),data@,error_offsets.0),
))]
pub(super) fn preflight_packet_body_ranges(
    contributions: &[Option<CodeBlockContribution>],
    data: &[u8],
    progress: &mut PacketBodyPreflight,
    error_offsets: (usize, usize),
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial=packet_body_preflight_view(progress);
        let ghost expected=crate::specs::part1_packet_body_preflight_at(initial,packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1);
    }
    #[cfg(verus_keep_ghost)]
    proof! {assert(initial==packet_body_preflight_view(old(progress)));}
    let error_offset = error_offsets.0;
    let local_offset = error_offsets.1;
    let slots = contributions.len();
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_packet_body_preflight); reveal(crate::specs::part1_packet_body_preflight_at); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            slots == contributions.len(),
            initial==packet_body_preflight_view(old(progress)),
            expected==crate::specs::part1_packet_body_preflight_at(initial,
                packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1),
            error_offset==error_offsets.0,local_offset==error_offsets.1,
            expected == crate::specs::part1_packet_body_preflight_at(packet_body_preflight_view(progress),
                packet_body_contributions_view(contributions), data@, error_offsets.0,error_offsets.1),
        decreases slots as int - progress.index as int,
    ))]
    while progress.index < slots {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost prior=packet_body_preflight_view(progress);}
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_packet_body_preflight); reveal(crate::specs::part1_packet_body_preflight_at); }
        if let Some(contribution) = contributions[progress.index] {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(packet_body_contributions_view(contributions)[prior.index as int]==
                    Some(code_block_contribution_view(&contribution)));
            }
            let length = match usize::try_from(contribution.data_length) {
                Ok(length) => length,
                Err(_) => {
                    return Err(packet_reader_error(
                        local_offset,
                        MalformedKind::ArithmeticOverflow,
                    ));
                }
            };
            progress.end = match progress.end.checked_add(length) {
                Some(end) => end,
                None => {
                    let error =
                        packet_reader_error(local_offset, MalformedKind::ArithmeticOverflow);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(packet_body_preflight_view(progress)==prior);
                        assert(crate::specs::part1_packet_body_preflight_at(prior,
                            packet_body_contributions_view(contributions),data@,error_offset,local_offset)
                            ==(Err(crate::specs::part1_packet_reader_error(local_offset,MalformedKind::ArithmeticOverflow)),prior));
                        assert(expected==(Err(error),packet_body_preflight_view(progress)));
                        assert(crate::specs::part1_packet_body_preflight_at(packet_body_preflight_view(old(progress)),
                            packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1)==expected);
                    }
                    return Err(error);
                }
            };
            if progress.end > data.len() {
                let error = packet_reader_error(error_offset, MalformedKind::Truncated);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(crate::specs::part1_packet_body_preflight_at(prior,
                        packet_body_contributions_view(contributions),data@,error_offset,local_offset)
                        ==(Err(crate::specs::part1_packet_reader_error(error_offset,MalformedKind::Truncated)),packet_body_preflight_view(progress)));
                    assert(expected==(Err(error),packet_body_preflight_view(progress)));
                    assert(crate::specs::part1_packet_body_preflight_at(packet_body_preflight_view(old(progress)),
                        packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1)==expected);
                }
                return Err(error);
            }
        }
        progress.index = match progress.index.checked_add(1) {
            Some(index) => index,
            None => {
                return Err(packet_reader_error(
                    local_offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_packet_body_preflight); reveal(crate::specs::part1_packet_body_preflight_at); }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_plane_execute_result(packet_body_execution_view(old(decoders),old(progress)),packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),
        (result,packet_body_execution_view(final(decoders),final(progress)))),
        (!decode_tier1 || result!=Err(DecodeError::AllocationFailed)) ==> (result, packet_body_execution_view(final(decoders), final(progress)))
        == crate::specs::part1_packet_body_execute_at(packet_body_execution_view(old(decoders), old(progress)),
            packet_body_contributions_view(contributions), data@, error_offsets.0,error_offsets.1,decode_tier1,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
        ((!decode_tier1 || result!=Err(DecodeError::AllocationFailed)) && error_offsets.1==0) ==> (result,packet_body_execution_view(final(decoders),final(progress)))
            ==crate::specs::part1_packet_body_execute(packet_body_execution_view(old(decoders),old(progress)),
                packet_body_contributions_view(contributions),data@,error_offsets.0,decode_tier1,
                crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits)),
        !decode_tier1 ==> final(decoders)@==old(decoders)@,
))]
pub(super) fn execute_packet_body_contributions(
    decoders: &mut [Tier1CodeBlockDecoder],
    contributions: &[Option<CodeBlockContribution>],
    data: &[u8],
    progress: &mut PacketBodyExecutionProgress,
    error_offsets: (usize, usize),
    decode_tier1: bool,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial=packet_body_execution_view(decoders,progress);
        let ghost expected=crate::specs::part1_packet_body_execute_at(initial,
            packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));
        let ghost root=|calls:Seq<crate::specs::Part2Tier1StorageEvent>|crate::specs::part2_plane_execute_run(initial,
            packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls);
        let ghost mut prefix=Seq::<crate::specs::Part2Tier1StorageEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_plane_execute_normal(initial,packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
    crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));}
    let error_offset = error_offsets.0;
    let local_offset = error_offsets.1;
    let slots = contributions.len();
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_packet_body_execute); reveal(crate::specs::part1_packet_body_execute_at); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            slots == contributions.len(),
            !decode_tier1 ==> decoders@==old(decoders)@,
            initial==packet_body_execution_view(old(decoders),old(progress)),
            forall|calls:Seq<crate::specs::Part2Tier1StorageEvent>| #[trigger] root(calls)==crate::specs::part2_plane_execute_run(initial,
                packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls),
            crate::specs::part2_tier1_phase(root,prefix,|calls|crate::specs::part2_plane_execute_run(packet_body_execution_view(decoders,progress),
                packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls)),
            crate::specs::part2_plane_execute_result(initial,packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
                crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),expected),
            expected==crate::specs::part1_packet_body_execute_at(initial,
                packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
                crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
                crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
            error_offset==error_offsets.0,local_offset==error_offsets.1,
            expected == crate::specs::part1_packet_body_execute_at(packet_body_execution_view(decoders, progress),
                packet_body_contributions_view(contributions), data@, error_offsets.0,error_offsets.1,decode_tier1,
                crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
                crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
        decreases slots as int - progress.index as int,
    ))]
    while progress.index < slots {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost prior=packet_body_execution_view(decoders,progress);}
        #[cfg(verus_keep_ghost)]
        proof! {if !decode_tier1 || contributions@[progress.index as int].is_none(){
            crate::specs::part2_plane_execute_pure_step(prior,packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
                crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));
        }}
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_packet_body_execute); reveal(crate::specs::part1_packet_body_execute_at); }
        if let Some(contribution) = contributions[progress.index] {
            let length = match usize::try_from(contribution.data_length) {
                Ok(length) => length,
                Err(_) => {
                    return Err(packet_reader_error(
                        local_offset,
                        MalformedKind::ArithmeticOverflow,
                    ));
                }
            };
            let body_end = match progress.offset.checked_add(length) {
                Some(end) => end,
                None => {
                    return Err(packet_reader_error(
                        local_offset,
                        MalformedKind::ArithmeticOverflow,
                    ));
                }
            };
            let body = data
                .get(progress.offset..body_end)
                .ok_or(DecodeError::MalformedInput {
                    offset: error_offset as u64,
                    kind: MalformedKind::Truncated,
                })?;
            if decode_tier1 {
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost prior_decoders = decoders@;
                    let ghost prior_states = packet_body_execution_view(decoders, progress).decoders;
                    let ghost selected_index = progress.index;
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    if prior.index<prior.decoders.len(){
                    crate::specs::part2_plane_execute_body_step(prior,packet_body_contributions_view(contributions),code_block_contribution_view(&contribution),data@,error_offsets.0,error_offsets.1,
                        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));
                    assert forall|calls:Seq<crate::specs::Part2Tier1StorageEvent>| #[trigger] root(prefix+calls)
                        ==crate::specs::part2_tier1_storage_bind(crate::specs::part2_plane_body_transaction_run(prior.decoders[prior.index as int],code_block_contribution_view(&contribution),body@,
                            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls),
                            |decoded:crate::specs::HtCodeBlockBodyResult,rest|crate::specs::part2_plane_execute_next(
                                crate::specs::part2_plane_execute_finish(prior,code_block_contribution_view(&contribution),error_offsets.1,decoded),prior.index,packet_body_contributions_view(contributions),data@,
                                error_offsets.0,error_offsets.1,true,crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                                crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),rest)) by {}
                    }
                }
                let decoded_result = {
                    let decoder = match decoders.get_mut(progress.index) {
                        Some(decoder) => decoder,
                        None => {
                            return Err(packet_reader_error(
                                local_offset,
                                MalformedKind::InvalidPacketHeader,
                            ));
                        }
                    };
                    decode_code_block_contribution_body(decoder, &contribution, body, limits)
                };
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(decoders@.len() == prior_decoders.len());
                    assert forall |i: int| 0 <= i < decoders@.len() && i != selected_index as int implies
                        decoders@[i] == prior_decoders[i] by {}
                    assert(packet_body_execution_view(decoders, progress).decoders =~=
                        prior_states.update(selected_index as int,
                            crate::tier1::tier1_decoder_state(&decoders@[selected_index as int])));
                    let decoded=(decoded_result,crate::tier1::tier1_decoder_state(&decoders@[selected_index as int]));
                    let child=|calls|crate::specs::part2_plane_body_transaction_run(prior.decoders[prior.index as int],code_block_contribution_view(&contribution),body@,
                        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls);
                    let next=|decoded:crate::specs::HtCodeBlockBodyResult,rest|crate::specs::part2_plane_execute_next(
                        crate::specs::part2_plane_execute_finish(prior,code_block_contribution_view(&contribution),error_offsets.1,decoded),prior.index,packet_body_contributions_view(contributions),data@,
                        error_offsets.0,error_offsets.1,true,crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                        crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),rest);
                    crate::specs::part2_plane_body_transaction_frames(prior.decoders[prior.index as int],code_block_contribution_view(&contribution),body@,
                        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),decoded);
                    assert forall|calls|root(prefix+calls)==crate::specs::part2_tier1_storage_bind(child(calls),next) by {}
                    prefix=crate::specs::part2_tier1_prefix_advance(root,child,next,prefix,decoded);
                    if let Err(error)=decoded_result {
                        let result=(Err(error),packet_body_execution_view(decoders,progress));
                        crate::specs::part2_tier1_prefix_finish(root,prefix,Ok(result));
                        crate::specs::part2_plane_execute_join(initial,packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
                            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),root,result);
                    }
                }
                let decoded = decoded_result?;
                progress.segments = match progress.segments.checked_add(u32::from(decoded.segments))
                {
                    Some(total) => total,
                    None => {
                        return Err(packet_reader_error(
                            local_offset,
                            MalformedKind::ArithmeticOverflow,
                        ));
                    }
                };
                progress.passes = match progress.passes.checked_add(decoded.passes) {
                    Some(total) => total,
                    None => {
                        return Err(packet_reader_error(
                            local_offset,
                            MalformedKind::ArithmeticOverflow,
                        ));
                    }
                };
            }
            progress.offset = body_end;
        }
        progress.index = match progress.index.checked_add(1) {
            Some(index) => index,
            None => {
                return Err(packet_reader_error(
                    local_offset,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_packet_body_execute); reveal(crate::specs::part1_packet_body_execute_at); }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_plane_body_transaction_result(crate::tier1::tier1_decoder_state(old(decoder)),code_block_contribution_view(contribution),body@,
        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),
        (result,crate::tier1::tier1_decoder_state(final(decoder)))),
        result!=Err(DecodeError::AllocationFailed) ==> (result, crate::tier1::tier1_decoder_state(final(decoder))) == crate::specs::part1_code_block_body_transaction(
            crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution), body@,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
        (result!=Err(DecodeError::AllocationFailed) && code_block_contribution_view(contribution).high_throughput) ==>
        (result, crate::tier1::tier1_decoder_state(final(decoder))) == crate::specs::ht_packet_body(
            crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution), body@,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_work_limit(limits)),
        (result!=Err(DecodeError::AllocationFailed) && !code_block_contribution_view(contribution).high_throughput) ==>
        (result, crate::tier1::tier1_decoder_state(final(decoder))) == crate::specs::part1_legacy_code_block_transaction(
            crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution), body@,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
))]
pub fn decode_code_block_contribution_body(
    decoder: &mut Tier1CodeBlockDecoder,
    contribution: &CodeBlockContribution,
    body: &[u8],
    limits: &ResourceLimits,
) -> Result<CodeBlockBodyDecode, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before=crate::tier1::tier1_decoder_state(decoder);}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_plane_body_transaction_normal(before,code_block_contribution_view(contribution),body@,crate::limits::resource_code_block_pass_limit(limits),
    crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));}
    let duplicated = decoder.try_duplicate(crate::tier1::HtRefinementCopyRole::PacketStaging);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=duplicated{crate::specs::part2_plane_body_duplicate_error(before,code_block_contribution_view(contribution),body@,crate::limits::resource_code_block_pass_limit(limits),
    crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),error);}}
    let mut staged = duplicated?;
    let decoded_result =
        decode_code_block_contribution_body_staged(&mut staged, contribution, body, limits);
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_plane_body_transaction_observed(before,code_block_contribution_view(contribution),body@,crate::limits::resource_code_block_pass_limit(limits),
    crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),(decoded_result,crate::tier1::tier1_decoder_state(&staged)));}
    let decoded = decoded_result?;
    *decoder = staged;
    Ok(decoded)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, crate::tier1::tier1_decoder_state(final(decoder))) == crate::specs::part1_code_block_body_prepare(
        crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution), body@),
))]
pub(super) fn prepare_code_block_contribution_body(
    decoder: &mut Tier1CodeBlockDecoder,
    contribution: &CodeBlockContribution,
    body: &[u8],
) -> Result<(), DecodeError> {
    let declared_length = match usize::try_from(contribution.data_length) {
        Ok(length) => length,
        Err(_) => return Err(packet_arithmetic_overflow()),
    };
    if !crate::refinement::exact_consumption(body.len(), declared_length) {
        return Err(packet_invalid_code_block());
    }
    if !decoder.accepts_high_throughput_route(contribution.high_throughput) {
        return Err(packet_invalid_code_block());
    }
    decoder.set_zero_bitplanes(contribution.zero_bitplanes)?;
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_plane_body_staged_result(crate::tier1::tier1_decoder_state(old(decoder)),code_block_contribution_view(contribution),body@,
        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),
        (result,crate::tier1::tier1_decoder_state(final(decoder)))),
        result!=Err(DecodeError::AllocationFailed) ==> (result, crate::tier1::tier1_decoder_state(final(decoder))) == crate::specs::part1_code_block_body_staged(
            crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution), body@,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
        (result!=Err(DecodeError::AllocationFailed) && code_block_contribution_view(contribution).high_throughput) ==>
        (result, crate::tier1::tier1_decoder_state(final(decoder))) == crate::specs::ht_packet_body_staged(
            crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution), body@,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_work_limit(limits)),
        (result!=Err(DecodeError::AllocationFailed) && !code_block_contribution_view(contribution).high_throughput) ==>
        (result, crate::tier1::tier1_decoder_state(final(decoder))) == crate::specs::part1_legacy_code_block_staged(
            crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution), body@,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
))]
pub(super) fn decode_code_block_contribution_body_staged(
    decoder: &mut Tier1CodeBlockDecoder,
    contribution: &CodeBlockContribution,
    body: &[u8],
    limits: &ResourceLimits,
) -> Result<CodeBlockBodyDecode, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before=crate::tier1::tier1_decoder_state(decoder);}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_plane_body_staged_normal(before,code_block_contribution_view(contribution),body@,crate::limits::resource_code_block_pass_limit(limits),
    crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));}
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_code_block_staged); }
    prepare_code_block_contribution_body(decoder, contribution, body)?;
    if contribution.high_throughput {
        let decoded = decode_ht_contribution_segments(decoder, contribution, body, limits);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_plane_body_staged_observed(before,code_block_contribution_view(contribution),body@,crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),(decoded,crate::tier1::tier1_decoder_state(decoder)));}
        return decoded;
    }
    let decoded = decode_legacy_code_block_contribution_body(decoder, contribution, body, limits);
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_plane_body_staged_legacy_observed(before,code_block_contribution_view(contribution),body@,crate::limits::resource_code_block_pass_limit(limits),
    crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),(decoded,crate::tier1::tier1_decoder_state(decoder)));}
    decoded
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_legacy_packet_body_result(crate::tier1::tier1_decoder_state(old(decoder)),code_block_contribution_view(contribution),body@,
        crate::tier1::legacy_storage_limits(limits),(result,crate::tier1::tier1_decoder_state(final(decoder)))),
        result!=Err(DecodeError::AllocationFailed) ==> (result, crate::tier1::tier1_decoder_state(final(decoder))) == crate::specs::part1_legacy_code_block_body(
        crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution), body@,
        crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
        crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
))]
pub(super) fn decode_legacy_code_block_contribution_body(
    decoder: &mut Tier1CodeBlockDecoder,
    contribution: &CodeBlockContribution,
    body: &[u8],
    limits: &ResourceLimits,
) -> Result<CodeBlockBodyDecode, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_code_block_body); }
    let segment_count = contribution.segment_count();
    let mut segment_index = 0_u8;
    let mut offset = 0_usize;
    let mut decoded_passes = 0_u32;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = legacy_packet_progress_view(decoder, 0, 0, 0);
        let ghost caps=crate::tier1::legacy_storage_limits(limits);
        let ghost root=|calls|crate::specs::part2_legacy_packet_body_run(initial.decoder,code_block_contribution_view(contribution),body@,caps,calls);
        let ghost mut prefix=Seq::<crate::specs::Part2Tier1StorageEvent>::empty();
        let ghost goal = crate::specs::part1_legacy_code_block_run(initial, code_block_contribution_view(contribution), body@,
            segment_count as nat, crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits), crate::limits::resource_input_byte_limit(limits),
            crate::limits::resource_work_limit(limits));
    }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_legacy_packet_body_start(initial.decoder,code_block_contribution_view(contribution),body@,caps);}
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant segment_index <= segment_count,
                caps==crate::tier1::legacy_storage_limits(limits),
                forall|calls:Seq<crate::specs::Part2Tier1StorageEvent>| #[trigger] root(calls)==crate::specs::part2_legacy_packet_body_run(initial.decoder,code_block_contribution_view(contribution),body@,caps,calls),
                crate::specs::part2_tier1_phase(root,prefix,|calls|crate::specs::part2_tier1_storage_bind(
                    crate::specs::part2_legacy_packet_fold(legacy_packet_progress_view(decoder,segment_index,offset,decoded_passes),code_block_contribution_view(contribution),body@,
                        (segment_count-segment_index) as nat,caps,calls),
                    |run:crate::specs::Part1LegacyPacketEffect,rest|Some((Ok(crate::specs::part1_legacy_code_block_finish(run,code_block_contribution_view(contribution),body@)),rest)))),
                segment_count == code_block_contribution_view(contribution).segment_count,
                initial == legacy_packet_progress_view(old(decoder), 0, 0, 0),
                goal == crate::specs::part1_legacy_code_block_run(initial, code_block_contribution_view(contribution), body@,
                    segment_count as nat, crate::limits::resource_code_block_pass_limit(limits),
                    crate::limits::resource_code_block_byte_limit(limits), crate::limits::resource_input_byte_limit(limits),
                    crate::limits::resource_work_limit(limits)),
                goal == crate::specs::part1_legacy_code_block_run(
                    legacy_packet_progress_view(decoder, segment_index, offset, decoded_passes),
                    code_block_contribution_view(contribution), body@, (segment_count - segment_index) as nat,
                    crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
                    crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
            decreases segment_count - segment_index,
        )
    )]
    while segment_index < segment_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_code_block_body);
            reveal(crate::specs::part1_legacy_code_block_run);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before_step=legacy_packet_progress_view(decoder,segment_index,offset,decoded_passes);let ghost remaining=(segment_count-segment_index) as nat;}
        #[cfg(verus_keep_ghost)]
        proof! {
            let source_root=|calls|crate::specs::part2_legacy_packet_body_run(initial.decoder,code_block_contribution_view(contribution),body@,caps,calls);
            crate::specs::part2_tier1_phase_eta(root,source_root,prefix,
                |calls|crate::specs::part2_tier1_storage_bind(crate::specs::part2_legacy_packet_fold(before_step,code_block_contribution_view(contribution),body@,remaining,caps,calls),
                    |run:crate::specs::Part1LegacyPacketEffect,rest|Some((Ok(crate::specs::part1_legacy_code_block_finish(run,code_block_contribution_view(contribution),body@)),rest))));
        }
        let step = decode_legacy_code_block_segment(
            decoder,
            contribution,
            body,
            limits,
            &mut segment_index,
            &mut offset,
            &mut decoded_passes,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            let effect=(step,legacy_packet_progress_view(decoder,segment_index,offset,decoded_passes));
            assert(crate::specs::part2_legacy_packet_step_result(before_step,code_block_contribution_view(contribution),body@,caps,effect));
            prefix=crate::specs::part2_legacy_packet_body_step(initial.decoder,code_block_contribution_view(contribution),body@,caps,before_step,remaining,prefix,effect);
            if step.is_err(){crate::specs::part2_legacy_packet_body_finish(initial.decoder,code_block_contribution_view(contribution),body@,caps,prefix,effect);}
            else{
                let source_root=|calls|crate::specs::part2_legacy_packet_body_run(initial.decoder,code_block_contribution_view(contribution),body@,caps,calls);
                crate::specs::part2_tier1_phase_eta(source_root,root,prefix,
                    |calls|crate::specs::part2_tier1_storage_bind(crate::specs::part2_legacy_packet_fold(effect.1,code_block_contribution_view(contribution),body@,(remaining-1) as nat,caps,calls),
                        |run:crate::specs::Part1LegacyPacketEffect,rest|Some((Ok(crate::specs::part1_legacy_code_block_finish(run,code_block_contribution_view(contribution),body@)),rest))));
            }
        }
        step?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_legacy_code_block_run);
        crate::specs::part2_legacy_packet_body_end(initial.decoder,code_block_contribution_view(contribution),body@,caps,legacy_packet_progress_view(decoder,segment_index,offset,decoded_passes),prefix);
    }
    if !crate::refinement::exact_consumption(offset, body.len())
        || decoded_passes != u32::from(contribution.new_passes)
    {
        return Err(packet_invalid_code_block());
    }
    Ok(CodeBlockBodyDecode {
        segments: contribution.segment_count(),
        passes: decoded_passes,
        bytes: contribution.data_length,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_packet_ht_segments_result(crate::tier1::tier1_decoder_state(old(decoder)),code_block_contribution_view(contribution),body@,
        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),(result,crate::tier1::tier1_decoder_state(final(decoder)))),
        result!=Err(DecodeError::AllocationFailed) ==> (result, crate::tier1::tier1_decoder_state(final(decoder))) == crate::specs::ht_packet_body_segments(
        crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution), body@,
        crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
        crate::limits::resource_work_limit(limits)),
))]
fn decode_ht_contribution_segments(
    decoder: &mut Tier1CodeBlockDecoder,
    contribution: &CodeBlockContribution,
    body: &[u8],
    limits: &ResourceLimits,
) -> Result<CodeBlockBodyDecode, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before=crate::tier1::tier1_decoder_state(decoder);}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_packet_ht_segments_normal(before,code_block_contribution_view(contribution),body@,crate::limits::resource_code_block_pass_limit(limits),
    crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits));}
    let segment_count = contribution.segment_count();
    if segment_count == 0 {
        return Err(packet_invalid_code_block());
    }
    let mut progress = HtBodyProgress {
        segment_index: 0,
        offset: 0,
        decoded_passes: 0,
    };
    let decoded = run_ht_contribution_segments(decoder, contribution, body, &mut progress, limits);
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_packet_ht_segments_observed(before,code_block_contribution_view(contribution),body@,crate::limits::resource_code_block_pass_limit(limits),
    crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),(decoded,crate::tier1::tier1_decoder_state(decoder),ht_body_progress_view(&progress)));}
    decoded?;
    if !crate::refinement::exact_consumption(progress.offset, body.len())
        || progress.decoded_passes != u32::from(contribution.new_passes)
    {
        return Err(packet_invalid_code_block());
    }
    Ok(CodeBlockBodyDecode {
        segments: segment_count,
        passes: progress.decoded_passes,
        bytes: contribution.data_length,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_packet_ht_body_result(crate::tier1::tier1_decoder_state(old(decoder)),code_block_contribution_view(contribution),body@,ht_body_progress_view(old(progress)),
        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),
        (result,crate::tier1::tier1_decoder_state(final(decoder)),ht_body_progress_view(final(progress)))),
        result!=Err(DecodeError::AllocationFailed) ==> (result, crate::tier1::tier1_decoder_state(final(decoder)), ht_body_progress_view(final(progress)))
        == crate::specs::ht_packet_body_run(crate::tier1::tier1_decoder_state(old(decoder)),
            code_block_contribution_view(contribution), body@, ht_body_progress_view(old(progress)),
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_work_limit(limits)),
))]
fn run_ht_contribution_segments(
    decoder: &mut Tier1CodeBlockDecoder,
    contribution: &CodeBlockContribution,
    body: &[u8],
    progress: &mut HtBodyProgress,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial=crate::tier1::tier1_decoder_state(decoder);
        let ghost original_progress=ht_body_progress_view(progress);
        let ghost root=|calls:Seq<crate::specs::Part2Tier1StorageEvent>|crate::specs::part2_packet_ht_body_run(initial,code_block_contribution_view(contribution),body@,original_progress,
            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),calls);
        let ghost mut prefix=Seq::<crate::specs::Part2Tier1StorageEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_packet_ht_body_normal(initial,code_block_contribution_view(contribution),body@,original_progress,
    crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits));}
    let segment_count = contribution.segment_count();
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::ht_packet_body_run); }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant
                segment_count == code_block_contribution_view(contribution).segment_count,
                initial==crate::tier1::tier1_decoder_state(old(decoder)),original_progress==ht_body_progress_view(old(progress)),
                forall|calls:Seq<crate::specs::Part2Tier1StorageEvent>| #[trigger] root(calls)==crate::specs::part2_packet_ht_body_run(initial,code_block_contribution_view(contribution),body@,original_progress,
                    crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),calls),
                crate::specs::part2_tier1_phase(root,prefix,|calls|crate::specs::part2_packet_ht_body_run(crate::tier1::tier1_decoder_state(decoder),code_block_contribution_view(contribution),body@,ht_body_progress_view(progress),
                    crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),calls)),
                crate::specs::part2_packet_ht_body_result(initial,code_block_contribution_view(contribution),body@,original_progress,
                    crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),
                    crate::specs::ht_packet_body_run(initial,code_block_contribution_view(contribution),body@,original_progress,
                        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits))),
                crate::specs::ht_packet_body_run(crate::tier1::tier1_decoder_state(old(decoder)),
                    code_block_contribution_view(contribution), body@, ht_body_progress_view(old(progress)),
                    crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
                    crate::limits::resource_work_limit(limits))
                    == crate::specs::ht_packet_body_run(crate::tier1::tier1_decoder_state(decoder),
                        code_block_contribution_view(contribution), body@, ht_body_progress_view(progress),
                        crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
                        crate::limits::resource_work_limit(limits)),
            decreases segment_count as int - progress.segment_index as int,
        )
    )]
    while progress.segment_index < segment_count {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_packet_body_run); }
        let segment = contribution.segment(progress.segment_index)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=crate::tier1::tier1_decoder_state(decoder);let ghost position=ht_body_progress_view(progress);}
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_packet_ht_body_step(before,code_block_contribution_view(contribution),body@,position,
                crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),segment);
            assert forall|calls:Seq<crate::specs::Part2Tier1StorageEvent>| #[trigger] root(prefix+calls)
                ==crate::specs::part2_tier1_storage_bind(crate::specs::part2_packet_ht_segment_run(before,segment,body@,position.offset,position.decoded_passes,
                    crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),calls),
                    |step:crate::specs::HtPacketSegmentResult,rest|crate::specs::part2_packet_ht_body_next(before,code_block_contribution_view(contribution),body@,position,
                        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),step,rest)) by {}
        }
        let decoded = decode_ht_segment_body(
            decoder,
            segment,
            body,
            &mut progress.offset,
            &mut progress.decoded_passes,
            limits,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            let step=(decoded,crate::tier1::tier1_decoder_state(decoder),progress.offset,progress.decoded_passes);
            let child=|calls|crate::specs::part2_packet_ht_segment_run(before,segment,body@,position.offset,position.decoded_passes,
                crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),calls);
            let next=|step:crate::specs::HtPacketSegmentResult,rest|crate::specs::part2_packet_ht_body_next(before,code_block_contribution_view(contribution),body@,position,
                crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),step,rest);
            crate::specs::part2_packet_ht_segment_frames(before,segment,body@,position.offset,position.decoded_passes,
                crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),step);
            assert forall|calls|root(prefix+calls)==crate::specs::part2_tier1_storage_bind(child(calls),next) by {}
            prefix=crate::specs::part2_tier1_prefix_advance(root,child,next,prefix,step);
            if let Err(error)=decoded {
                let result=(Err(error),step.1,ht_body_progress_view(progress));
                crate::specs::part2_tier1_prefix_finish(root,prefix,Ok(result));
                crate::specs::part2_packet_ht_body_join(initial,code_block_contribution_view(contribution),body@,original_progress,
                    crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),root,result);
            }
        }
        decoded?;
        progress.segment_index = progress
            .segment_index
            .checked_add(1)
            .ok_or_else(packet_arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::ht_packet_body_run); }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_packet_ht_segment_result(crate::tier1::tier1_decoder_state(old(decoder)),segment,body@,*old(offset),*old(decoded_passes),
        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),
        (result,crate::tier1::tier1_decoder_state(final(decoder)),*final(offset),*final(decoded_passes))),
        result!=Err(DecodeError::AllocationFailed) ==> (result, crate::tier1::tier1_decoder_state(final(decoder)), *final(offset), *final(decoded_passes))
        == crate::specs::ht_packet_segment_body(crate::tier1::tier1_decoder_state(old(decoder)), segment, body@,
            *old(offset), *old(decoded_passes), crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits), crate::limits::resource_work_limit(limits)),
))]
pub(super) fn decode_ht_segment_body(
    decoder: &mut Tier1CodeBlockDecoder,
    segment: CodeBlockSegmentContribution,
    body: &[u8],
    offset: &mut usize,
    decoded_passes: &mut u32,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before=crate::tier1::tier1_decoder_state(decoder);let ghost original_offset=*offset;let ghost original_passes=*decoded_passes;}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_packet_ht_segment_normal(before,segment,body@,original_offset,original_passes,crate::limits::resource_code_block_pass_limit(limits),
    crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits));}
    if segment.passes == 0 || segment.passes > 2 {
        return Err(packet_invalid_code_block());
    }
    let segment_length =
        usize::try_from(segment.data_length).map_err(|_| packet_arithmetic_overflow())?;
    let end = offset
        .checked_add(segment_length)
        .ok_or_else(packet_arithmetic_overflow)?;
    let segment_body = body
        .get(*offset..end)
        .ok_or_else(packet_invalid_code_block)?;
    let routed = decode_ht_segment_route(decoder, segment_body, segment.passes, limits);
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_packet_ht_segment_observed(before,segment,body@,original_offset,original_passes,crate::limits::resource_code_block_pass_limit(limits),
    crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),end,(routed,crate::tier1::tier1_decoder_state(decoder)));}
    routed?;
    *decoded_passes = decoded_passes
        .checked_add(u32::from(segment.passes))
        .ok_or_else(packet_arithmetic_overflow)?;
    *offset = end;
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_packet_ht_route_result(crate::tier1::tier1_decoder_state(old(decoder)),body@,passes,crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),(result,crate::tier1::tier1_decoder_state(final(decoder)))),
        result!=Err(DecodeError::AllocationFailed) ==> (result, crate::tier1::tier1_decoder_state(final(decoder))) == crate::specs::ht_packet_segment_route(
        crate::tier1::tier1_decoder_state(old(decoder)), body@, passes,
        crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
        crate::limits::resource_work_limit(limits)),
))]
fn decode_ht_segment_route(
    decoder: &mut Tier1CodeBlockDecoder,
    body: &[u8],
    passes: u8,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before=crate::tier1::tier1_decoder_state(decoder);}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_packet_ht_route_normal(before,body@,passes,crate::limits::resource_code_block_pass_limit(limits),
    crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits));}
    if decoder.next_pass().is_multiple_of(3) {
        if passes != 1 {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodeBlock,
            });
        }
        if body.is_empty() {
            decoder.skip_high_throughput_segment(1, limits)?;
        } else {
            let decoded = decoder.decode_high_throughput_segments(body, 1, None, 0, limits);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_packet_ht_route_observed(before,body@,passes,crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),(decoded,crate::tier1::tier1_decoder_state(decoder)));}
            decoded?;
        }
    } else if decoder.ht_current_set_has_cleanup() {
        let decoded = decoder.decode_high_throughput_refinement(body, passes, limits);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_packet_ht_route_observed(before,body@,passes,crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),(decoded,crate::tier1::tier1_decoder_state(decoder)));}
        decoded?;
    } else {
        if !body.is_empty() {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodeBlock,
            });
        }
        decoder.skip_high_throughput_segment(passes, limits)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_legacy_packet_step_result(legacy_packet_progress_view(old(decoder),*old(segment_index),*old(offset),*old(decoded_passes)),
        code_block_contribution_view(contribution),body@,crate::tier1::legacy_storage_limits(limits),
        (result,legacy_packet_progress_view(final(decoder),*final(segment_index),*final(offset),*final(decoded_passes)))),
        result!=Err(DecodeError::AllocationFailed) ==> (result, legacy_packet_progress_view(final(decoder), *final(segment_index), *final(offset), *final(decoded_passes)))
        == crate::specs::part1_legacy_code_block_segment(
            legacy_packet_progress_view(old(decoder), *old(segment_index), *old(offset), *old(decoded_passes)),
            code_block_contribution_view(contribution), body@,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
        result.is_ok() ==> *old(segment_index) < code_block_contribution_view(contribution).segment_count
            && *final(segment_index) as nat == *old(segment_index) as nat + 1,
))]
pub(super) fn decode_legacy_code_block_segment(
    decoder: &mut Tier1CodeBlockDecoder,
    contribution: &CodeBlockContribution,
    body: &[u8],
    limits: &ResourceLimits,
    segment_index: &mut u8,
    offset: &mut usize,
    decoded_passes: &mut u32,
) -> Result<(), DecodeError> {
    decode_legacy_code_block_segment_mode(
        decoder,
        contribution,
        body,
        limits,
        segment_index,
        offset,
        decoded_passes,
        false,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures
        terminal ==> crate::specs::part2_tier1_storage_framed(
            |calls| crate::specs::terminal_packet_segment_run(
                legacy_packet_progress_view(old(decoder), *old(segment_index), *old(offset), *old(decoded_passes)),
                code_block_contribution_view(contribution), body@, crate::tier1::legacy_storage_limits(limits), calls),
            Ok((result, legacy_packet_progress_view(final(decoder), *final(segment_index), *final(offset), *final(decoded_passes))))),
        terminal && result != Err(DecodeError::AllocationFailed) ==>
            (result, legacy_packet_progress_view(final(decoder), *final(segment_index), *final(offset), *final(decoded_passes)))
                == crate::specs::terminal_packet_segment_normal(
                    legacy_packet_progress_view(old(decoder), *old(segment_index), *old(offset), *old(decoded_passes)),
                    code_block_contribution_view(contribution), body@, crate::tier1::legacy_storage_limits(limits)),
        !terminal ==> crate::specs::part2_legacy_packet_step_result(
            legacy_packet_progress_view(old(decoder), *old(segment_index), *old(offset), *old(decoded_passes)),
            code_block_contribution_view(contribution), body@, crate::tier1::legacy_storage_limits(limits),
            (result, legacy_packet_progress_view(final(decoder), *final(segment_index), *final(offset), *final(decoded_passes)))),
        !terminal && result!=Err(DecodeError::AllocationFailed) ==>
            (result, legacy_packet_progress_view(final(decoder), *final(segment_index), *final(offset), *final(decoded_passes)))
                == crate::specs::part1_legacy_code_block_segment(
                    legacy_packet_progress_view(old(decoder), *old(segment_index), *old(offset), *old(decoded_passes)),
                    code_block_contribution_view(contribution), body@,
                    crate::limits::resource_code_block_pass_limit(limits),
                    crate::limits::resource_code_block_byte_limit(limits),
                    crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
        result.is_ok() ==> *old(segment_index) < code_block_contribution_view(contribution).segment_count
            && *final(segment_index) as nat == *old(segment_index) as nat + 1,
))]
#[allow(
    clippy::too_many_arguments,
    reason = "the segment frame and final mode are explicit"
)]
fn decode_legacy_code_block_segment_mode(
    decoder: &mut Tier1CodeBlockDecoder,
    contribution: &CodeBlockContribution,
    body: &[u8],
    limits: &ResourceLimits,
    segment_index: &mut u8,
    offset: &mut usize,
    decoded_passes: &mut u32,
    terminal: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_code_block_segment); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before=legacy_packet_progress_view(decoder,*segment_index,*offset,*decoded_passes);}
    #[cfg(verus_keep_ghost)]
    proof! {
        let header = code_block_contribution_view(contribution);
        let caps = crate::tier1::legacy_storage_limits(limits);
        crate::specs::part2_legacy_packet_step_normal(before, header, body@, caps);
        if let Err(error) = crate::specs::part2_legacy_packet_admit(before, header, body@) {
            crate::specs::part2_tier1_storage_pure(Ok::<crate::specs::Part1LegacyPacketEffect, DecodeError>((Err(error), before)));
        }
    }
    let segment = contribution.segment(*segment_index)?;
    let segment_length = match usize::try_from(segment.data_length) {
        Ok(length) => length,
        Err(_) => return Err(packet_arithmetic_overflow()),
    };
    let end = offset
        .checked_add(segment_length)
        .ok_or_else(packet_arithmetic_overflow)?;
    if end > body.len() {
        return Err(packet_invalid_code_block());
    }
    let decoded = if terminal {
        decoder.decode_legacy_contribution_mode(&body[*offset..end], segment.passes, limits, true)
    } else {
        decoder.decode_legacy_contribution(&body[*offset..end], segment.passes, limits)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let header = code_block_contribution_view(contribution);
        let caps = crate::tier1::legacy_storage_limits(limits);
        let effect = (decoded, crate::tier1::tier1_decoder_state(decoder));
        if terminal {
            crate::specs::terminal_packet_segment_observed(before, header, body@, caps, segment, end, effect);
        } else {
            crate::specs::part2_legacy_packet_step_observed(before, header, body@, caps, segment, end, effect);
        }
    }
    decoded?;
    *decoded_passes = decoded_passes
        .checked_add(u32::from(segment.passes))
        .ok_or_else(packet_arithmetic_overflow)?;
    *offset = end;
    *segment_index = segment_index
        .checked_add(1)
        .ok_or_else(packet_arithmetic_overflow)?;
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires !contribution.high_throughput, code_block_contribution_view(contribution).segment_count == 1,
    ensures crate::specs::part2_tier1_storage_framed(
        |calls| crate::specs::terminal_packet_single_body_run(
            crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution), body@,
            crate::tier1::legacy_storage_limits(limits), calls),
        Ok((result, crate::tier1::tier1_decoder_state(final(decoder))))),
        result != Err(DecodeError::AllocationFailed) ==>
            (result, crate::tier1::tier1_decoder_state(final(decoder))) ==
                crate::specs::terminal_packet_single_body_normal(
                    crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution),
                    body@, crate::tier1::legacy_storage_limits(limits)),
))]
fn decode_terminal_single_legacy_body(
    decoder: &mut Tier1CodeBlockDecoder,
    contribution: &CodeBlockContribution,
    body: &[u8],
    limits: &ResourceLimits,
) -> Result<CodeBlockBodyDecode, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = crate::tier1::tier1_decoder_state(decoder);
        let ghost header = code_block_contribution_view(contribution);
        let ghost caps = crate::tier1::legacy_storage_limits(limits);
    }
    let prepared = prepare_code_block_contribution_body(decoder, contribution, body);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = prepared {
            crate::specs::part2_tier1_storage_pure(
                Ok::<crate::specs::HtCodeBlockBodyResult, DecodeError>((Err(error), crate::tier1::tier1_decoder_state(decoder))));
        }
    }
    prepared?;
    let mut segment = 0;
    let mut offset = 0;
    let mut passes = 0;
    let step = decode_legacy_code_block_segment_mode(
        decoder,
        contribution,
        body,
        limits,
        &mut segment,
        &mut offset,
        &mut passes,
        true,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::terminal_packet_single_body_observed(
            before, header, body@, caps, (step, legacy_packet_progress_view(decoder, segment, offset, passes)));
    }
    step?;
    if !crate::refinement::exact_consumption(offset, body.len())
        || passes != u32::from(contribution.new_passes)
    {
        return Err(packet_invalid_code_block());
    }
    Ok(CodeBlockBodyDecode {
        segments: contribution.segment_count(),
        passes,
        bytes: contribution.data_length,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_tier1_storage_framed(
        |calls| crate::specs::terminal_body_mode_run(
            true, crate::tier1::tier1_decoder_state(old(decoder)), code_block_contribution_view(contribution), body@,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits), calls),
        Ok((result,crate::tier1::tier1_decoder_state(final(decoder))))),
        result != Err(DecodeError::AllocationFailed) ==>
            (result,crate::tier1::tier1_decoder_state(final(decoder))) == crate::specs::terminal_body_mode_value(
                true,crate::tier1::tier1_decoder_state(old(decoder)),code_block_contribution_view(contribution),body@,
                crate::tier1::legacy_storage_limits(limits)),
))]
fn decode_terminal_code_block_body(
    decoder: &mut Tier1CodeBlockDecoder,
    contribution: &CodeBlockContribution,
    body: &[u8],
    limits: &ResourceLimits,
) -> Result<CodeBlockBodyDecode, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before=crate::tier1::tier1_decoder_state(decoder);
        let ghost header=code_block_contribution_view(contribution);
        let ghost caps=crate::tier1::legacy_storage_limits(limits);
    }
    if contribution.high_throughput || contribution.segment_count() != 1 {
        let decoded = decode_code_block_contribution_body(decoder, contribution, body, limits);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_plane_body_transaction_frames(before,header,body@,caps.passes,caps.bytes,caps.input,
                caps.work,(decoded,crate::tier1::tier1_decoder_state(decoder)));
        }
        return decoded;
    }
    let duplicated = decoder.try_duplicate(crate::tier1::HtRefinementCopyRole::PacketStaging);
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost copy=crate::tier1::tier1_initial_decoder_outcome(duplicated); }
    #[cfg(verus_keep_ghost)]
    proof! { if let Err(error)=duplicated {
        crate::specs::terminal_body_duplicate_observed(before,header,body@,caps,copy,(Err(error),before));
    }}
    let mut staged = duplicated?;
    let decoded = decode_terminal_single_legacy_body(&mut staged, contribution, body, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::terminal_body_duplicate_observed(before,header,body@,caps,copy,
            (decoded,crate::tier1::tier1_decoder_state(&staged)));
    }
    let decoded = decoded?;
    *decoder = staged;
    Ok(decoded)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(progress).index < contributions@.len(),
    ensures
        crate::specs::terminal_exact_observed(
            (result, packet_body_execution_view(final(decoders), final(progress))),
            |effect: crate::specs::Part1PacketBodyExecutionResult| crate::specs::part2_tier1_storage_framed(
                |calls| crate::specs::terminal_body_optional_slot_run(
                    packet_body_execution_view(old(decoders), old(progress)),
                    packet_body_contributions_view(contributions)[old(progress).index as int],
                    data@, offsets, true, crate::tier1::legacy_storage_limits(limits), calls), Ok(effect))),
        result != Err(DecodeError::AllocationFailed) ==> crate::specs::terminal_exact_matches(
            (result, packet_body_execution_view(final(decoders), final(progress))),
            crate::specs::terminal_body_optional_slot_value(
                packet_body_execution_view(old(decoders), old(progress)),
                packet_body_contributions_view(contributions)[old(progress).index as int],
                data@, offsets, true, crate::tier1::legacy_storage_limits(limits))),
        final(progress).index == old(progress).index,
))]
fn execute_terminal_body_slot(
    decoders: &mut [Tier1CodeBlockDecoder],
    contributions: &[Option<CodeBlockContribution>],
    data: &[u8],
    progress: &mut PacketBodyExecutionProgress,
    offsets: (usize, usize),
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = packet_body_execution_view(decoders, progress);
        let ghost original = decoders@;
        let ghost slot = packet_body_contributions_view(contributions)[before.index as int];
        let ghost caps = crate::tier1::legacy_storage_limits(limits);
        let ghost run = |calls| crate::specs::terminal_body_optional_slot_run(before, slot, data@, offsets, true, caps, calls);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_packet_body_execute_slot_at);
        if slot.is_none() || !crate::specs::part2_plane_execute_admit(before, slot.unwrap(), data@, true) {
            let output = crate::specs::terminal_body_optional_slot_value(before, slot, data@, offsets, true, caps);
            crate::specs::terminal_body_slot_pure(before, slot, data@, offsets, true, caps);
            crate::specs::part2_tier1_storage_pure(Ok(output));
        }
    }
    let Some(contribution) = contributions[progress.index] else {
        return Ok(());
    };
    let length = match usize::try_from(contribution.data_length) {
        Ok(length) => length,
        Err(_) => {
            return Err(packet_reader_error(
                offsets.1,
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    let end = match progress.offset.checked_add(length) {
        Some(end) => end,
        None => {
            return Err(packet_reader_error(
                offsets.1,
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    let body = data
        .get(progress.offset..end)
        .ok_or(DecodeError::MalformedInput {
            offset: offsets.0 as u64,
            kind: MalformedKind::Truncated,
        })?;
    let Some(decoder) = decoders.get_mut(progress.index) else {
        return Err(packet_reader_error(
            offsets.1,
            MalformedKind::InvalidPacketHeader,
        ));
    };
    let decoded = decode_terminal_code_block_body(decoder, &contribution, body, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        let index = before.index as int;
        assert forall|i: int| 0 <= i < decoders@.len() && i != index
            implies #[trigger] decoders@[i] == original[i] by {};
        let actual = packet_body_execution_view(decoders, progress);
        assert(actual.decoders =~= before.decoders.update(index, crate::tier1::tier1_decoder_state(&decoders@[index])));
        let effect = (decoded, actual.decoders[index]);
        crate::specs::terminal_body_slot_observed(before, slot.unwrap(), data@, offsets, caps, effect);
        if let Err(error) = decoded {
            crate::specs::terminal_exact_publish(
                (Err(error), actual), crate::specs::part2_plane_execute_finish(before, slot.unwrap(), offsets.1, effect),
                |output| crate::specs::part2_tier1_storage_framed(run, Ok(output)));
        }
    }
    let decoded = decoded?;
    progress.segments = match progress.segments.checked_add(u32::from(decoded.segments)) {
        Some(total) => total,
        None => {
            return Err(packet_reader_error(
                offsets.1,
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    progress.passes = match progress.passes.checked_add(decoded.passes) {
        Some(total) => total,
        None => {
            return Err(packet_reader_error(
                offsets.1,
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    progress.offset = end;
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures
        crate::specs::terminal_exact_observed(
            (result, packet_body_execution_view(final(decoders), final(progress))),
            |effect: crate::specs::Part1PacketBodyExecutionResult|
                crate::specs::terminal_body_frame(
                    packet_body_execution_view(old(decoders), old(progress)),
                    packet_body_contributions_view(contributions), data@, offsets, true,
                    crate::tier1::legacy_storage_limits(limits), effect)),
        result != Err(DecodeError::AllocationFailed) ==> crate::specs::terminal_exact_matches(
            (result, packet_body_execution_view(final(decoders), final(progress))),
            crate::specs::terminal_body_value(true,
                packet_body_execution_view(old(decoders), old(progress)),
                packet_body_contributions_view(contributions), data@, offsets.0, offsets.1, true,
                crate::tier1::legacy_storage_limits(limits))),
))]
pub(super) fn execute_terminal_packet_body_contributions(
    decoders: &mut [Tier1CodeBlockDecoder],
    contributions: &[Option<CodeBlockContribution>],
    data: &[u8],
    progress: &mut PacketBodyExecutionProgress,
    offsets: (usize, usize),
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = packet_body_execution_view(decoders, progress);
        let ghost cs = packet_body_contributions_view(contributions);
        let ghost caps = crate::tier1::legacy_storage_limits(limits);
        let ghost root = |calls| crate::specs::terminal_body_run(true, initial, cs, data@, offsets.0, offsets.1, true, caps, calls);
        let ghost mut prefix = Seq::<crate::specs::Part2Tier1StorageEvent>::empty();
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant initial == packet_body_execution_view(old(decoders), old(progress)),
            cs == packet_body_contributions_view(contributions), caps == crate::tier1::legacy_storage_limits(limits),
            forall|calls| #[trigger] root(calls) == crate::specs::terminal_body_run(
                true, initial, cs, data@, offsets.0, offsets.1, true, caps, calls),
            crate::specs::part2_tier1_phase(root, prefix, |calls| crate::specs::terminal_body_run(
                true, packet_body_execution_view(decoders, progress), cs, data@, offsets.0, offsets.1, true, caps, calls)),
            crate::specs::terminal_body_value(true, initial, cs, data@, offsets.0, offsets.1, true, caps)
                == crate::specs::terminal_body_value(true, packet_body_execution_view(decoders, progress), cs,
                    data@, offsets.0, offsets.1, true, caps),
        decreases contributions.len() - progress.index,
    ))]
    while progress.index < contributions.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before = packet_body_execution_view(decoders, progress);}
        let result =
            execute_terminal_body_slot(decoders, contributions, data, progress, offsets, limits);
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::terminal_body_value);
            let actual = (result, packet_body_execution_view(decoders, progress));
            let child = |calls| crate::specs::terminal_body_optional_slot_run(
                before, cs[before.index as int], data@, offsets, true, caps, calls);
            let next = |effect: crate::specs::Part1PacketBodyExecutionResult, rest|
                crate::specs::terminal_body_next(true, effect, before.index, cs, data@, offsets.0, offsets.1, true, caps, rest);
            let effect = crate::specs::terminal_exact_witness(
                actual, |effect| crate::specs::part2_tier1_storage_framed(child, Ok(effect)));
            crate::specs::terminal_body_slot_keeps_index(before, cs[before.index as int], data@, offsets, caps, effect);
            crate::specs::terminal_body_unfold(before, cs, data@, offsets, true, caps);
            assert forall|calls| root(prefix + calls) == crate::specs::part2_tier1_storage_bind(child(calls), next) by {}
            prefix = crate::specs::part2_tier1_prefix_advance(root, child, next, prefix, effect);
            if actual.0.is_err() {
                assert forall|calls| next(effect, calls) == Some((Ok(effect), calls)) by {
                    // Consumed failure effects still have the same slot cursor.
                    assert(effect.1.index == before.index);
                }
                crate::specs::part2_tier1_prefix_finish(root, prefix, Ok(effect));
                crate::specs::part2_tier1_storage_eta(root, Ok(effect));
                crate::specs::terminal_exact_publish(actual, effect,
                    |effect| crate::specs::terminal_body_frame(initial, cs, data@, offsets, true, caps, effect));
            }
        }
        result?;
        progress.index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::terminal_body_value);
        let effect = (Ok(()), packet_body_execution_view(decoders, progress));
        crate::specs::terminal_body_unfold(effect.1, cs, data@, offsets, true, caps);
        crate::specs::part2_tier1_prefix_finish(root, prefix, Ok(effect));
        crate::specs::part2_tier1_storage_eta(root, Ok(effect));
    }
    Ok(())
}
