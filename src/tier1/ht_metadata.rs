use super::ht_cleanup_readers::ht_cleanup_readers_from_inputs;
use super::ht_segments::parse_ht_block_segments;
use super::state::{arithmetic_overflow, invalid_code_block};
use super::{
    HtCleanupMetadata, HtCleanupReaders, HtCleanupSegment, HtQuadMetadata, MAX_HT_MAGSGN_BITS,
};
#[cfg(verus_keep_ghost)]
use super::{
    ht_cleanup_metadata_outcome, ht_cleanup_readers_view, ht_cleanup_segment_view,
    ht_metadata_pair_view, ht_metadata_quad_input, ht_metadata_row_view, ht_metadata_words_outcome,
};
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        requires 0 < quads_per_row <= 32768, pair < quads_per_row,
            previous_patterns.len() == quads_per_row, old(current_patterns).len() == quads_per_row,
        ensures (ht_metadata_words_outcome(result), ht_cleanup_readers_view(final(readers)),
            final(current_patterns)@, *final(left_context))
            == crate::specs::ht_metadata_words(ht_cleanup_readers_view(old(readers)),
                old(current_patterns)@, *old(left_context), previous_patterns@, pair as nat, initial),
            final(current_patterns).len() == old(current_patterns).len(),
    )
)]
pub(super) fn decode_ht_metadata_words(
    readers: &mut HtCleanupReaders<'_>,
    current_patterns: &mut [u8],
    left_context: &mut u8,
    previous_patterns: &[u8],
    quads_per_row: usize,
    pair: usize,
    initial: bool,
) -> Result<([u16; 2], [u8; 2]), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost start_readers = ht_cleanup_readers_view(readers);
        let ghost start_current = current_patterns@;
        let ghost start_left = *left_context;
    }
    let mut words = [0_u16; 2];
    let mut contexts = [0_u8; 2];
    let mut member = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(words@ =~= Seq::new(2, |i: int| 0u16));
        assert(contexts@ =~= Seq::new(2, |i: int| 0u8));
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant member <= 2, 0 < quads_per_row <= 32768, pair < quads_per_row,
                previous_patterns.len() == quads_per_row, current_patterns.len() == quads_per_row,
                old(current_patterns).len() == quads_per_row, start_current.len() == quads_per_row,
                start_readers == ht_cleanup_readers_view(old(readers)),
                start_current == old(current_patterns)@, start_left == *old(left_context),
                crate::specs::ht_metadata_words(start_readers, start_current, start_left, previous_patterns@, pair as nat, initial)
                    == crate::specs::ht_metadata_words_finish(crate::specs::ht_metadata_words_run(
                        crate::specs::HtMetadataWordsState {
                            readers: ht_cleanup_readers_view(readers), current: current_patterns@,
                            left: *left_context, words: words@, contexts: contexts@,
                        }, previous_patterns@, pair as nat, initial, member as nat)),
            ensures member == 2 || pair + member >= quads_per_row,
            decreases 2 - member,
        )
    )]
    while member < 2 {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_metadata_words_unfold(
                crate::specs::HtMetadataWordsState {
                    readers: ht_cleanup_readers_view(readers), current: current_patterns@,
                    left: *left_context, words: words@, contexts: contexts@,
                }, previous_patterns@, pair as nat, initial, member as nat,
            );
        }
        let quad_index = pair.checked_add(member).ok_or_else(arithmetic_overflow)?;
        if quad_index >= quads_per_row {
            break;
        }
        let context = if initial {
            *left_context
        } else {
            let north_pattern = *previous_patterns
                .get(quad_index)
                .ok_or_else(invalid_code_block)?;
            let north_west_pattern = match quad_index.checked_sub(1) {
                Some(index) => *previous_patterns
                    .get(index)
                    .ok_or_else(invalid_code_block)?,
                None => 0,
            };
            let north_east_index = quad_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            let north_east_pattern = match previous_patterns.get(north_east_index) {
                Some(pattern) => *pattern,
                None => 0,
            };
            crate::refinement::ht_noninitial_vlc_context(
                *left_context,
                north_west_pattern,
                north_pattern,
                north_east_pattern,
            )
        };
        let word = readers.decode_quad_word(initial, context)?;
        let significance = ((word >> 4) & 0x0f) as u8;
        *words.get_mut(member).ok_or_else(invalid_code_block)? = word;
        *contexts.get_mut(member).ok_or_else(invalid_code_block)? = context;
        *current_patterns
            .get_mut(quad_index)
            .ok_or_else(invalid_code_block)? = significance;
        *left_context = if initial {
            (significance & 0x01) | ((significance & 0x0e) >> 1)
        } else if significance & 0x0c != 0 {
            2
        } else {
            0
        };
        member = member.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_ht_metadata_words_unfold(
            crate::specs::HtMetadataWordsState {
                readers: ht_cleanup_readers_view(readers), current: current_patterns@,
                left: *left_context, words: words@, contexts: contexts@,
            }, previous_patterns@, pair as nat, initial, member as nat,
        );
    }
    Ok((words, contexts))
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        requires quad_index < 32768, quad_row < 32768,
        ensures (result, ht_cleanup_readers_view(final(readers)), final(quads)@, *final(significant_samples))
            == crate::specs::ht_metadata_emit(ht_cleanup_readers_view(old(readers)), old(quads)@,
                *old(significant_samples), ht_metadata_quad_input(quad_index, quad_row, width, height,
                    maximum_u, word, context, significance, u_value, initial)),
            result.is_ok() ==> final(quads).len() == old(quads).len() + 1,
    )
)]
#[allow(
    clippy::too_many_arguments,
    reason = "Explicit codec inputs and disjoint mutable outputs keep state frames auditable."
)]
pub(super) fn append_ht_metadata_quad(
    readers: &mut HtCleanupReaders<'_>,
    quads: &mut Vec<HtQuadMetadata>,
    significant_samples: &mut u16,
    quad_index: usize,
    quad_row: usize,
    width: u16,
    height: u16,
    maximum_u: u8,
    word: u16,
    context: u8,
    significance: u8,
    u_value: u8,
    initial: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost start_readers = ht_cleanup_readers_view(readers);
        let ghost start_quads = quads@;
        let ghost start_significant = *significant_samples;
        let ghost input = ht_metadata_quad_input(quad_index, quad_row, width, height, maximum_u, word, context, significance, u_value, initial);
    }
    if u_value > maximum_u {
        return Err(invalid_code_block());
    }
    let x = u16::try_from(quad_index.checked_mul(2).ok_or_else(arithmetic_overflow)?)
        .map_err(|_| arithmetic_overflow())?;
    let y = u16::try_from(quad_row.checked_mul(2).ok_or_else(arithmetic_overflow)?)
        .map_err(|_| arithmetic_overflow())?;
    if !crate::refinement::ht_quad_origin_valid(x, y, width, height) {
        return Err(invalid_code_block());
    }
    let mut sample = 0_u8;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant sample <= 4, x == quad_index * 2, y == quad_row * 2,
                quad_index < 32768, quad_row < 32768, x <= 65534, y <= 65534,
                start_readers == ht_cleanup_readers_view(old(readers)),
                start_readers == ht_cleanup_readers_view(readers),
                start_quads == old(quads)@, start_quads == quads@,
                start_significant == *old(significant_samples),
                input == ht_metadata_quad_input(quad_index, quad_row, width, height, maximum_u, word, context, significance, u_value, initial),
                crate::specs::ht_quad_origin_valid(x as nat, y as nat, width as nat, height as nat),
                u_value <= maximum_u,
                crate::specs::ht_metadata_emit(start_readers, start_quads, start_significant, input)
                    == crate::specs::ht_metadata_emit_after_samples(
                        crate::specs::ht_metadata_samples(*significant_samples, significance, x, y, width, height, sample),
                        start_readers, start_quads, input),
            decreases 4 - sample,
        )
    )]
    while sample < 4 {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_metadata_samples_unfold(*significant_samples, significance, x, y, width, height, sample);
            assert(sample >> 1u8 <= 1) by(bit_vector) requires sample < 4;
            assert(sample & 1u8 <= 1) by(bit_vector);
            assert(sample >> 1u8 == sample / 2u8) by(bit_vector);
            assert(sample & 1u8 == sample % 2u8) by(bit_vector);
        }
        if significance & (1_u8 << sample) != 0 {
            let sample_x = x
                .checked_add(u16::from(sample >> 1))
                .ok_or_else(arithmetic_overflow)?;
            let sample_y = y
                .checked_add(u16::from(sample & 1))
                .ok_or_else(arithmetic_overflow)?;
            if !crate::refinement::ht_quad_sample_in_bounds(x, y, sample, width, height)
                || sample_x >= width
                || sample_y >= height
            {
                return Err(invalid_code_block());
            }
            *significant_samples = significant_samples
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        sample = sample.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_ht_metadata_samples_unfold(*significant_samples, significance, x, y, width, height, sample);
    }
    quads.push(HtQuadMetadata {
        x,
        y,
        context,
        initial_row: initial,
        significance,
        embedded_magnitude: ((word >> 8) & 0x0f) as u8,
        embedded_bit_mask: ((word >> 12) & 0x0f) as u8,
        u_offset: word & 0x08 != 0,
        u_base: u_value,
        codeword_bits: (word & 0x07) as u8,
    });
    readers.tick()?;
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        requires 0 < quads_per_row <= 32768, pair < quads_per_row, quad_row < 32768,
            previous_patterns.len() == quads_per_row, old(current_patterns).len() == quads_per_row,
        ensures (result, ht_metadata_pair_view(final(readers), final(quads), final(current_patterns)@,
                *final(significant_samples), *final(left_context)))
            == crate::specs::ht_metadata_pair(
                ht_metadata_pair_view(old(readers), old(quads), old(current_patterns)@,
                    *old(significant_samples), *old(left_context)),
                previous_patterns@, pair as nat, quad_row as nat, width, height, maximum_u, initial),
            final(current_patterns).len() == old(current_patterns).len(),
            result.is_ok() ==> final(quads).len() == old(quads).len() + if pair + 1 < quads_per_row { 2int } else { 1int },
            result == Ok(()) || result.is_err(),
    )
)]
#[allow(
    clippy::too_many_arguments,
    reason = "Explicit codec inputs and disjoint mutable outputs keep state frames auditable."
)]
fn decode_ht_metadata_pair(
    readers: &mut HtCleanupReaders<'_>,
    quads: &mut Vec<HtQuadMetadata>,
    current_patterns: &mut [u8],
    significant_samples: &mut u16,
    left_context: &mut u8,
    previous_patterns: &[u8],
    quads_per_row: usize,
    pair: usize,
    quad_row: usize,
    width: u16,
    height: u16,
    maximum_u: u8,
    initial: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost start = ht_metadata_pair_view(readers, quads, current_patterns@, *significant_samples, *left_context);
    }
    let (words, contexts) = decode_ht_metadata_words(
        readers,
        current_patterns,
        left_context,
        previous_patterns,
        quads_per_row,
        pair,
        initial,
    )?;
    let mut mode = if words[0] & 0x08 != 0 { 1_u8 } else { 0_u8 };
    mode |= if words[1] & 0x08 != 0 { 2_u8 } else { 0_u8 };
    if initial && mode == 3 && readers.mel_event()? {
        mode = 4;
    }
    let u_values = if initial {
        readers.decode_initial_u(mode)?
    } else {
        readers.decode_non_initial_u(mode)?
    };
    let mut member = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant member <= 2, pair + member <= quads_per_row,
                0 < quads_per_row <= 32768, pair < quads_per_row, quad_row < 32768,
                previous_patterns.len() == quads_per_row, current_patterns.len() == quads_per_row,
                old(current_patterns).len() == quads_per_row,
                start == ht_metadata_pair_view(old(readers), old(quads), old(current_patterns)@, *old(significant_samples), *old(left_context)),
                quads.len() == start.quads.len() + member,
                crate::specs::ht_metadata_pair(start, previous_patterns@, pair as nat, quad_row as nat, width, height, maximum_u, initial)
                    == crate::specs::ht_metadata_emits_run(
                        ht_metadata_pair_view(readers, quads, current_patterns@, *significant_samples, *left_context),
                        words@, contexts@, u_values, pair as nat, quad_row as nat, width, height, maximum_u, initial, member as nat),
            ensures member == 2 || pair + member == quads_per_row,
            decreases 2 - member,
        )
    )]
    while member < 2 {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_metadata_emits_unfold(
                ht_metadata_pair_view(readers, quads, current_patterns@, *significant_samples, *left_context),
                words@, contexts@, u_values, pair as nat, quad_row as nat, width, height, maximum_u, initial, member as nat,
            );
        }
        let quad_index = pair.checked_add(member).ok_or_else(arithmetic_overflow)?;
        if quad_index >= quads_per_row {
            break;
        }
        let word = *words.get(member).ok_or_else(invalid_code_block)?;
        let significance = *current_patterns
            .get(quad_index)
            .ok_or_else(invalid_code_block)?;
        let u_value = *u_values.get(member).ok_or_else(invalid_code_block)?;
        append_ht_metadata_quad(
            readers,
            quads,
            significant_samples,
            quad_index,
            quad_row,
            width,
            height,
            maximum_u,
            word,
            *contexts.get(member).ok_or_else(invalid_code_block)?,
            significance,
            u_value,
            initial,
        )?;
        member = member.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_ht_metadata_emits_unfold(
            ht_metadata_pair_view(readers, quads, current_patterns@, *significant_samples, *left_context),
            words@, contexts@, u_values, pair as nat, quad_row as nat, width, height, maximum_u, initial, member as nat,
        );
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        requires 0 < quads_per_row <= 32768, quad_row < 32768,
            old(previous_patterns).len() == quads_per_row,
        ensures crate::specs::part2_ht_metadata_row_result(
                ht_metadata_row_view(old(readers), old(quads), old(previous_patterns), *old(significant_samples)),
                quad_row as nat, width, height, maximum_u,
                (result, ht_metadata_row_view(final(readers), final(quads), final(previous_patterns), *final(significant_samples)))),
            result != Err(DecodeError::AllocationFailed) ==> (result, ht_metadata_row_view(final(readers), final(quads), final(previous_patterns), *final(significant_samples)))
            == crate::specs::ht_metadata_row(
                ht_metadata_row_view(old(readers), old(quads), old(previous_patterns), *old(significant_samples)),
                quad_row as nat, width, height, maximum_u),
            final(previous_patterns).len() == old(previous_patterns).len(),
            result.is_ok() ==> final(quads).len() == old(quads).len() + quads_per_row,
            result == Ok(()) || result.is_err(),
    )
)]
#[allow(
    clippy::too_many_arguments,
    reason = "Explicit geometry and disjoint mutable outputs keep state frames auditable."
)]
pub(super) fn decode_ht_metadata_row(
    readers: &mut HtCleanupReaders<'_>,
    quads: &mut Vec<HtQuadMetadata>,
    previous_patterns: &mut Vec<u8>,
    significant_samples: &mut u16,
    quads_per_row: usize,
    quad_row: usize,
    width: u16,
    height: u16,
    maximum_u: u8,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost start = ht_metadata_row_view(readers, quads, previous_patterns, *significant_samples);
        let ghost start_pair = crate::specs::ht_metadata_row_initial(start);
    }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_ht_metadata_row_normal(start,quad_row as nat,width,height,maximum_u);}
    let initial = quad_row == 0;
    let allocated = crate::allocation::filled_values(0_u8, quads_per_row);
    #[cfg(verus_keep_ghost)]
    proof! {
        let result=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_ht_metadata_capacity_observed(crate::specs::part2_ht_metadata_row_context(start,quad_row as nat,width,height,maximum_u),
            crate::specs::Part2HtMetadataRole::Current,result);
        if let Err(error)=allocated{crate::specs::part2_ht_metadata_row_refused(start,quad_row as nat,width,height,maximum_u,error);}
    }
    let mut current_patterns = allocated?;
    let mut left_context = 0_u8;
    let mut pair = 0_usize;
    let mut pair_passes = quads_per_row
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?
        / 2;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(current_patterns@ =~= Seq::new(quads_per_row as nat, |i: int| 0u8));
        reveal_with_fuel(crate::specs::ht_metadata_pairs, 1);
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant 0 < quads_per_row <= 32768, quad_row < 32768,
                pair <= quads_per_row + 1, pair % 2 == 0,
                pair + pair_passes * 2 >= quads_per_row,
                pair + pair_passes * 2 <= quads_per_row + 1,
                pair / 2 <= (quads_per_row + 1) / 2,
                current_patterns.len() == quads_per_row,
                previous_patterns.len() == quads_per_row,
                old(previous_patterns).len() == quads_per_row,
                start == ht_metadata_row_view(old(readers), old(quads), old(previous_patterns), *old(significant_samples)),
                start.previous == previous_patterns@, start.previous.len() == quads_per_row,
                start_pair == crate::specs::ht_metadata_row_initial(start),
                crate::specs::part2_ht_metadata_row_result(start,quad_row as nat,width,height,maximum_u,
                    crate::specs::ht_metadata_row(start,quad_row as nat,width,height,maximum_u)),
                initial == (quad_row == 0),
                quads.len() == start.quads.len() + if pair <= quads_per_row { pair as int } else { quads_per_row as int },
                crate::specs::ht_metadata_pairs(start_pair, start.previous, quad_row as nat,
                    width, height, maximum_u, (pair / 2) as nat)
                    == (Ok(()), ht_metadata_pair_view(readers, quads, current_patterns@, *significant_samples, left_context)),
            decreases pair_passes,
        )
    )]
    while pair < quads_per_row {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before = ht_metadata_pair_view(readers, quads, current_patterns@, *significant_samples, left_context);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((pair / 2) * 2 == pair);
            crate::proofs::production_impl::production_ht_metadata_pairs_step(start_pair, start.previous, quad_row as nat,
                width, height, maximum_u, (pair / 2) as nat);
        }
        let result = decode_ht_metadata_pair(
            readers,
            quads,
            &mut current_patterns,
            significant_samples,
            &mut left_context,
            previous_patterns,
            quads_per_row,
            pair,
            quad_row,
            width,
            height,
            maximum_u,
            initial,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::ht_metadata_pair(before, start.previous, pair as nat, quad_row as nat,
                width, height, maximum_u, initial)
                == (result, ht_metadata_pair_view(readers, quads, current_patterns@, *significant_samples, left_context)));
        }
        match result {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_ht_metadata_pairs_error(start_pair, start.previous,
                        quad_row as nat, width, height, maximum_u, (pair / 2 + 1) as nat, ((quads_per_row + 1) / 2) as nat);
                }
                return Err(error);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(result == Ok(()));
            assert(crate::specs::ht_metadata_pairs(start_pair, start.previous, quad_row as nat,
                width, height, maximum_u, (pair / 2 + 1) as nat)
                == (Ok(()), ht_metadata_pair_view(readers, quads, current_patterns@, *significant_samples, left_context)));
        }
        pair = pair.checked_add(2).ok_or_else(arithmetic_overflow)?;
        pair_passes = pair_passes.checked_sub(1).ok_or_else(arithmetic_overflow)?;
    }
    *previous_patterns = current_patterns;
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::specs::part1_ht_decode_metadata_storage_result(cleanup@,width,height,maximum_u,
                crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),ht_cleanup_metadata_outcome(result)),
            ht_cleanup_metadata_outcome(result) != Err(DecodeError::AllocationFailed) ==> ht_cleanup_metadata_outcome(result) == crate::specs::ht_decode_cleanup_metadata(
            cleanup@, width, height, maximum_u, crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_work_limit(limits),
        ),
    )
)]
pub fn decode_ht_cleanup_metadata(
    cleanup: &[u8],
    width: u16,
    height: u16,
    maximum_u: u8,
    limits: &ResourceLimits,
) -> Result<HtCleanupMetadata, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_ht_decode_metadata_normal(cleanup@,width,height,maximum_u,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits));}
    let segments = parse_ht_block_segments(cleanup, None, limits)?;
    let result =
        decode_ht_cleanup_segment_metadata(segments.cleanup(), width, height, maximum_u, limits);
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_ht_decode_metadata_observed(cleanup@,width,height,maximum_u,crate::limits::resource_code_block_byte_limit(limits),
    crate::limits::resource_work_limit(limits),super::ht_block_segments_view(&segments),ht_cleanup_metadata_outcome(result));}
    result
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::specs::part2_ht_metadata_result(ht_cleanup_segment_view(&cleanup),width,height,maximum_u,
                crate::limits::resource_work_limit(limits),ht_cleanup_metadata_outcome(result)),
            ht_cleanup_metadata_outcome(result) != Err(DecodeError::AllocationFailed) ==> ht_cleanup_metadata_outcome(result) == crate::specs::ht_cleanup_segment_metadata(
            ht_cleanup_segment_view(&cleanup), width, height, maximum_u, crate::limits::resource_work_limit(limits),
        ),
    )
)]
pub(super) fn decode_ht_cleanup_segment_metadata(
    cleanup: HtCleanupSegment<'_>,
    width: u16,
    height: u16,
    maximum_u: u8,
    limits: &ResourceLimits,
) -> Result<HtCleanupMetadata, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_ht_metadata_normal(ht_cleanup_segment_view(&cleanup),width,height,maximum_u,crate::limits::resource_work_limit(limits));}
    if width == 0 || height == 0 || maximum_u == 0 || maximum_u > MAX_HT_MAGSGN_BITS {
        return Err(invalid_code_block());
    }
    let samples = u32::from(width)
        .checked_mul(u32::from(height))
        .ok_or_else(arithmetic_overflow)?;
    if samples > 4_096 {
        return Err(invalid_code_block());
    }
    let quads_per_row = usize::from(width)
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?
        / 2;
    let quad_rows = usize::from(height)
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?
        / 2;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::spec_properties::ht_quad_count_is_bounded_by_samples(width as nat, height as nat);
        assert(quads_per_row as nat * quad_rows as nat <= 4096);
    }
    let quad_count = quads_per_row
        .checked_mul(quad_rows)
        .ok_or_else(arithmetic_overflow)?;
    let mut readers = ht_cleanup_readers_from_inputs(
        cleanup.mel().bytes(),
        cleanup.vlc().bytes(),
        limits.maximum_work_units(),
    )?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost input=ht_cleanup_segment_view(&cleanup);let ghost work=crate::limits::resource_work_limit(limits);let ghost initial_readers=ht_cleanup_readers_view(&readers);}
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_ht_metadata_admit(input,width,height,maximum_u,work)==Ok(initial_readers));
        assert(quads_per_row>0 && quad_rows>0);
        assert(quad_count>0) by(nonlinear_arith) requires
            quads_per_row>0,quad_rows>0,
            quad_count as nat==quads_per_row as nat*quad_rows as nat;
    }
    let allocated = crate::allocation::empty_with_capacity::<HtQuadMetadata>(quad_count);
    #[cfg(verus_keep_ghost)]
    proof! {
        let result=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_ht_metadata_capacity_observed(crate::specs::part2_ht_metadata_context(input,width,height,maximum_u,work),crate::specs::Part2HtMetadataRole::Quads,result);
        if let Err(error)=allocated{crate::specs::part2_ht_metadata_initial_error(input,width,height,maximum_u,work,initial_readers,false,error);}
    }
    let mut quads = allocated?;
    let allocated = crate::allocation::filled_values(0_u8, quads_per_row);
    #[cfg(verus_keep_ghost)]
    proof! {
        let result=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_ht_metadata_capacity_observed(crate::specs::part2_ht_metadata_context(input,width,height,maximum_u,work),crate::specs::Part2HtMetadataRole::Previous,result);
        if let Err(error)=allocated{crate::specs::part2_ht_metadata_initial_error(input,width,height,maximum_u,work,initial_readers,true,error);}
    }
    let mut previous_patterns = allocated?;
    let mut significant_samples = 0_u16;
    let mut quad_row = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost start = ht_metadata_row_view(&readers, &quads, &previous_patterns, significant_samples);
        let ghost segment = ht_cleanup_segment_view(&cleanup);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(previous_patterns@ =~= Seq::new(quads_per_row as nat, |i: int| 0u8));
        assert(quads@ =~= Seq::<HtQuadMetadata>::empty());
        reveal_with_fuel(crate::specs::ht_metadata_rows, 1);
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant quad_row <= quad_rows, 0 < quads_per_row <= 32768, 0 < quad_rows <= 32768,
                width > 0, height > 0, 0 < maximum_u <= 75,
                width as nat * height as nat <= 4096,
                previous_patterns.len() == quads_per_row,
                quads_per_row as nat == (width as nat + 1) / 2,
                quad_rows as nat == (height as nat + 1) / 2,
                segment == ht_cleanup_segment_view(&cleanup),
                crate::specs::ht_cleanup_readers_initial(segment.mel.bytes,
                    segment.vlc.bytes, crate::limits::resource_work_limit(limits)) == Ok(start.readers),
                start.quads == Seq::<HtQuadMetadata>::empty(), start.significant == 0,
                start.readers==initial_readers,
                input==ht_cleanup_segment_view(&cleanup),
                work==crate::limits::resource_work_limit(limits),
                crate::specs::part2_ht_metadata_admit(input,width,height,maximum_u,work)==Ok(initial_readers),
                crate::specs::part2_ht_metadata_result(input,width,height,maximum_u,work,
                    crate::specs::ht_cleanup_segment_metadata(input,width,height,maximum_u,work)),
                start.previous == Seq::new(quads_per_row as nat, |i: int| 0u8),
                crate::specs::ht_metadata_rows(start, width, height, maximum_u, quad_row as nat)
                    == (Ok(()), ht_metadata_row_view(&readers, &quads, &previous_patterns, significant_samples)),
            decreases quad_rows - quad_row,
        )
    )]
    while quad_row < quad_rows {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = ht_metadata_row_view(&readers, &quads, &previous_patterns, significant_samples); }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_metadata_rows_step(start, width, height, maximum_u, quad_row as nat);
        }
        let result = decode_ht_metadata_row(
            &mut readers,
            &mut quads,
            &mut previous_patterns,
            &mut significant_samples,
            quads_per_row,
            quad_row,
            width,
            height,
            maximum_u,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(result!=Err(DecodeError::AllocationFailed) ==> crate::specs::ht_metadata_row(before, quad_row as nat, width, height, maximum_u)
                == (result, ht_metadata_row_view(&readers, &quads, &previous_patterns, significant_samples)));
        }
        match result {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_ht_metadata_row_error(input,width,height,maximum_u,work,initial_readers,quad_row as nat,before,
                        (result,ht_metadata_row_view(&readers,&quads,&previous_patterns,significant_samples)));
                    if error!=DecodeError::AllocationFailed{crate::proofs::production_impl::production_ht_metadata_rows_error(start, width, height, maximum_u,
                        (quad_row + 1) as nat, quad_rows as nat);}
                }
                return Err(error);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(result == Ok(()));
            assert(crate::specs::ht_metadata_rows(start, width, height, maximum_u, (quad_row + 1) as nat)
                == (Ok(()), ht_metadata_row_view(&readers, &quads, &previous_patterns, significant_samples)));
        }
        quad_row = quad_row.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    readers.finish()?;
    Ok(HtCleanupMetadata {
        width,
        height,
        quads,
        significant_samples,
        mel_bits: match u32::try_from(readers.mel.bits_read()) {
            Ok(value) => value,
            Err(_) => return Err(arithmetic_overflow()),
        },
        vlc_bits: match u32::try_from(readers.vlc.bits_read()) {
            Ok(value) => value,
            Err(_) => return Err(arithmetic_overflow()),
        },
        mel_events: readers.mel_events,
    })
}
