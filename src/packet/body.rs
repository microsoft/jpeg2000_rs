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
    ensures crate::specs::part2_packet_effect_observed(owned_body,(result,packet_body_execution_view(final(decoders),final(progress))),|effect:crate::specs::Part1PacketBodyExecutionResult| crate::specs::part2_plane_execute_result(owned_body,packet_body_execution_view(old(decoders),old(progress)),packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),effect)),
        (!decode_tier1 || result!=Err(DecodeError::AllocationFailed)) ==> crate::specs::part2_packet_effect_matches(owned_body,(result, packet_body_execution_view(final(decoders), final(progress))),crate::specs::part1_packet_body_execute_at(packet_body_execution_view(old(decoders), old(progress)),
            packet_body_contributions_view(contributions), data@, error_offsets.0,error_offsets.1,decode_tier1,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits))),
        ((!decode_tier1 || result!=Err(DecodeError::AllocationFailed)) && error_offsets.1==0) ==> crate::specs::part2_packet_effect_matches(owned_body,(result,packet_body_execution_view(final(decoders),final(progress))),crate::specs::part1_packet_body_execute(packet_body_execution_view(old(decoders),old(progress)),
                packet_body_contributions_view(contributions),data@,error_offsets.0,decode_tier1,
                crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits))),
        !decode_tier1 ==> final(decoders)@==old(decoders)@,
))]
#[allow(
    clippy::too_many_arguments,
    reason = "keep body progress, offsets, limits, and transaction mode explicit"
)]
pub(super) fn execute_packet_body_contributions(
    decoders: &mut [Tier1CodeBlockDecoder],
    contributions: &[Option<CodeBlockContribution>],
    data: &[u8],
    progress: &mut PacketBodyExecutionProgress,
    error_offsets: (usize, usize),
    decode_tier1: bool,
    limits: &ResourceLimits,
    owned_body: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial=packet_body_execution_view(decoders,progress);
        let ghost expected=crate::specs::part1_packet_body_execute_at(initial,
            packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));
        let ghost root=|calls:Seq<crate::specs::Part2Tier1StorageEvent>|crate::specs::part2_plane_execute_run(owned_body,initial,
            packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls);
        let ghost mut prefix=Seq::<crate::specs::Part2Tier1StorageEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_plane_execute_normal(owned_body,initial,packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
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
            forall|calls:Seq<crate::specs::Part2Tier1StorageEvent>| #[trigger] root(calls)==crate::specs::part2_plane_execute_run(owned_body,initial,
                packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls),
            crate::specs::part2_tier1_phase(root,prefix,|calls|crate::specs::part2_plane_execute_run(owned_body,packet_body_execution_view(decoders,progress),
                packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls)),
            crate::specs::part2_plane_execute_result(owned_body,initial,packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
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
            crate::specs::part2_plane_execute_pure_step(owned_body,prior,packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
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
                    crate::specs::part2_plane_execute_body_step(owned_body,prior,packet_body_contributions_view(contributions),code_block_contribution_view(&contribution),data@,error_offsets.0,error_offsets.1,
                        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));
                    assert forall|calls:Seq<crate::specs::Part2Tier1StorageEvent>| #[trigger] root(prefix+calls)
                        ==crate::specs::part2_tier1_storage_bind(crate::specs::part2_plane_body_mode_run(owned_body,prior.decoders[prior.index as int],code_block_contribution_view(&contribution),body@,
                            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls),
                            |decoded:crate::specs::HtCodeBlockBodyResult,rest|crate::specs::part2_plane_execute_next(owned_body,
                                crate::specs::part2_plane_execute_finish(prior,code_block_contribution_view(&contribution),error_offsets.1,decoded),prior.index,packet_body_contributions_view(contributions),data@,
                                error_offsets.0,error_offsets.1,true,crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                                crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),rest)) by {}
                    }
                }
                let in_place;
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
                    in_place = owned_body && decoder.next_pass() != 0;
                    if in_place {
                        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
                        crate::deadline::checkpoint()?;
                        decode_code_block_contribution_body_staged(
                            decoder,
                            &contribution,
                            body,
                            limits,
                        )
                    } else {
                        decode_code_block_contribution_body(decoder, &contribution, body, limits)
                    }
                };
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(decoders@.len() == prior_decoders.len());
                    assert forall |i: int| 0 <= i < decoders@.len() && i != selected_index as int implies
                        decoders@[i] == prior_decoders[i] by {}
                    assert(packet_body_execution_view(decoders, progress).decoders =~=
                        prior_states.update(selected_index as int,
                            crate::tier1::tier1_decoder_state(&decoders@[selected_index as int])));
                    let actual=(decoded_result,crate::tier1::tier1_decoder_state(&decoders@[selected_index as int]));
                    let decoded=crate::specs::part2_plane_body_effect(in_place,prior.decoders[prior.index as int],actual);
                    if decoded_result!=Err(DecodeError::AllocationFailed) {
                        assert(decoded==crate::specs::part1_code_block_body_transaction(prior.decoders[prior.index as int],code_block_contribution_view(&contribution),body@,
                            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                            crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits)));
                    }
                    let child=|calls|crate::specs::part2_plane_body_mode_run(owned_body,prior.decoders[prior.index as int],code_block_contribution_view(&contribution),body@,
                        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls);
                    let next=|decoded:crate::specs::HtCodeBlockBodyResult,rest|crate::specs::part2_plane_execute_next(owned_body,
                        crate::specs::part2_plane_execute_finish(prior,code_block_contribution_view(&contribution),error_offsets.1,decoded),prior.index,packet_body_contributions_view(contributions),data@,
                        error_offsets.0,error_offsets.1,true,crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                        crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),rest);
                    crate::specs::part2_plane_body_mode_observed(owned_body,prior.decoders[prior.index as int],code_block_contribution_view(&contribution),body@,
                        crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),actual);
                    assert forall|calls|root(prefix+calls)==crate::specs::part2_tier1_storage_bind(child(calls),next) by {}
                    prefix=crate::specs::part2_tier1_prefix_advance(root,child,next,prefix,decoded);
                    if let Err(error)=decoded_result {
                        let result=crate::specs::part2_plane_execute_finish(prior,code_block_contribution_view(&contribution),error_offsets.1,decoded);
                        let actual=(Err(error),packet_body_execution_view(decoders,progress));
                        assert(result.0==actual.0);
                        assert(!owned_body ==> result.1==actual.1);
                        crate::specs::part2_tier1_prefix_finish(root,prefix,Ok(result));
                        crate::specs::part2_plane_execute_join(owned_body,initial,packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
                            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),root,result);
                        crate::specs::part2_packet_effect_publish(owned_body,actual,result,|effect:crate::specs::Part1PacketBodyExecutionResult|
                            crate::specs::part2_plane_execute_result(owned_body,initial,packet_body_contributions_view(contributions),data@,error_offsets.0,error_offsets.1,decode_tier1,
                            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),effect));
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
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_code_block_segment); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before=legacy_packet_progress_view(decoder,*segment_index,*offset,*decoded_passes);}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_legacy_packet_step_normal(before,code_block_contribution_view(contribution),body@,crate::tier1::legacy_storage_limits(limits));}
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
    let decoded = decoder.decode_legacy_contribution(&body[*offset..end], segment.passes, limits);
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_legacy_packet_step_observed(before,code_block_contribution_view(contribution),body@,crate::tier1::legacy_storage_limits(limits),
    segment,end,(decoded,crate::tier1::tier1_decoder_state(decoder)));}
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
