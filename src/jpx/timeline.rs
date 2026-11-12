//! Composition timeline construction and persistent frame selection.
use super::resources::{arithmetic_overflow, invalid_layer};
use super::{
    CompositionInstruction, DecodeError, JpxFrameInfo, JpxInstructionInfo, Resource, TimelineState,
    jp2,
};
#[cfg(verus_keep_ghost)]
use super::{
    frame_selection_result, frame_views, frame_views_push, instruction_view, instruction_views,
    instruction_views_push, timeline_frame_result, timeline_frames_result,
    timeline_instruction_view, timeline_instruction_views, timeline_set_views, timeline_state_view,
    timeline_step_result,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::part2_timeline_limit(layer_count, maximum_frames),
    )
)]
fn timeline_instruction_limit(
    layer_count: usize,
    maximum_frames: u32,
) -> Result<usize, DecodeError> {
    let frames = usize::try_from(maximum_frames).map_err(|_| arithmetic_overflow())?;
    let layers = if layer_count == 0 { 1 } else { layer_count };
    #[cfg(verus_keep_ghost)]
    proof! { vstd::arithmetic::mul::lemma_mul_is_commutative(frames as int, layers as int); }
    match frames.checked_mul(layers) {
        Some(limit) => Ok(limit),
        None => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures timeline_frames_result(result) == crate::specs::part2_build_timeline(
            timeline_set_views(composition), layer_count, maximum_frames),
    )
)]
pub(super) fn build_timeline(
    composition: &jp2::Composition,
    layer_count: usize,
    maximum_frames: u32,
) -> Result<Vec<JpxFrameInfo>, DecodeError> {
    let maximum_instructions = timeline_instruction_limit(layer_count, maximum_frames)?;
    let mut state = TimelineState {
        frames: Vec::new(),
        assignments: Vec::new(),
        next_layer: 0,
        instruction_index: 0,
        milliseconds: 0,
    };
    let mut set_index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost input = timeline_set_views(composition);
        let ghost initial = Ok::<(bool, crate::specs::Part2TimelineState), DecodeError>((true, timeline_state_view(&state)));
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(frame_views(state.frames@) =~= Seq::<crate::specs::Part2Frame>::empty());
        crate::proofs::production_impl::production_timeline_set_base(input, initial, layer_count, maximum_frames, maximum_instructions);
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant set_index <= composition.instruction_sets.len(),
                input == timeline_set_views(composition),
                initial == Ok((true, (Seq::empty(), Seq::empty(), 0, 0, 0))),
                crate::specs::part2_timeline_limit(layer_count, maximum_frames) == Ok(maximum_instructions),
                crate::proofs::internal_specs::part2_timeline_state_valid(timeline_state_view(&state), layer_count, maximum_frames, maximum_instructions),
                crate::specs::part2_timeline_sets(input, initial, set_index as nat, layer_count, maximum_frames, maximum_instructions)
                    == Ok((true, timeline_state_view(&state))),
            decreases composition.instruction_sets.len() - set_index,
        )
    )]
    while set_index < composition.instruction_sets.len() {
        let set = composition
            .instruction_sets
            .get(set_index)
            .ok_or_else(arithmetic_overflow)?;
        let repetitions = u32::from(set.repeat)
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        let mut repetition = 0_u32;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost set_initial = Ok::<(bool, crate::specs::Part2TimelineState), DecodeError>((true, timeline_state_view(&state)));
            let ghost program = timeline_instruction_views(set.instructions@);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_timeline_repetition_base(program, set_initial, layer_count, maximum_frames, maximum_instructions);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant repetition <= repetitions,
                    input == timeline_set_views(composition), set_index < input.len(),
                    initial == Ok((true, (Seq::empty(), Seq::empty(), 0, 0, 0))),
                    set == composition.instruction_sets@[set_index as int],
                    program == input[set_index as int].1,
                    repetitions as nat == input[set_index as int].0 as nat + 1,
                    crate::specs::part2_timeline_limit(layer_count, maximum_frames) == Ok(maximum_instructions),
                    crate::proofs::internal_specs::part2_timeline_state_valid(timeline_state_view(&state), layer_count, maximum_frames, maximum_instructions),
                    set_initial == crate::specs::part2_timeline_sets(input, initial, set_index as nat, layer_count, maximum_frames, maximum_instructions),
                    crate::specs::part2_timeline_repetitions(program, set_initial, repetition as nat, layer_count, maximum_frames, maximum_instructions)
                        == Ok((true, timeline_state_view(&state))),
                decreases repetitions - repetition,
            )
        )]
        while repetition < repetitions {
            let mut local_index = 0_usize;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost repeat_initial = Ok::<(bool, crate::specs::Part2TimelineState), DecodeError>((true, timeline_state_view(&state)));
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_timeline_instruction_base(program, repeat_initial, layer_count, maximum_frames, maximum_instructions);
            }
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant local_index <= set.instructions.len(),
                        input == timeline_set_views(composition), set_index < input.len(),
                        initial == Ok((true, (Seq::empty(), Seq::empty(), 0, 0, 0))),
                        set == composition.instruction_sets@[set_index as int],
                        program == input[set_index as int].1, program == timeline_instruction_views(set.instructions@),
                        repetitions as nat == input[set_index as int].0 as nat + 1,
                        repetition < repetitions,
                        crate::specs::part2_timeline_limit(layer_count, maximum_frames) == Ok(maximum_instructions),
                        crate::proofs::internal_specs::part2_timeline_state_valid(timeline_state_view(&state), layer_count, maximum_frames, maximum_instructions),
                        set_initial == crate::specs::part2_timeline_sets(input, initial, set_index as nat, layer_count, maximum_frames, maximum_instructions),
                        repeat_initial == crate::specs::part2_timeline_repetitions(program, set_initial, repetition as nat, layer_count, maximum_frames, maximum_instructions),
                        crate::specs::part2_timeline_instructions(program, repeat_initial, local_index as nat, layer_count, maximum_frames, maximum_instructions)
                            == Ok((true, timeline_state_view(&state))),
                    decreases set.instructions.len() - local_index,
                )
            )]
            while local_index < set.instructions.len() {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_timeline_instruction_step(program, repeat_initial, local_index as nat, layer_count, maximum_frames, maximum_instructions);
                }
                let outcome = apply_timeline_instruction(
                    &mut state,
                    set.instructions[local_index],
                    layer_count,
                    maximum_frames,
                    maximum_instructions,
                );
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(crate::specs::part2_timeline_instructions(program, repeat_initial, local_index as nat + 1, layer_count, maximum_frames, maximum_instructions)
                        == timeline_step_result(outcome, &state));
                    if crate::specs::part2_timeline_finished(timeline_step_result(outcome, &state)) {
                        crate::proofs::production_impl::production_timeline_instruction_halt(program, repeat_initial, local_index as nat + 1, program.len(), layer_count, maximum_frames, maximum_instructions);
                        crate::proofs::production_impl::production_timeline_repetition_step(program, set_initial, repetition as nat, layer_count, maximum_frames, maximum_instructions);
                        crate::proofs::production_impl::production_timeline_repetition_halt(program, set_initial, repetition as nat + 1, repetitions as nat, layer_count, maximum_frames, maximum_instructions);
                        crate::proofs::production_impl::production_timeline_set_step(input, initial, set_index as nat, layer_count, maximum_frames, maximum_instructions);
                        crate::proofs::production_impl::production_timeline_set_halt(input, initial, set_index as nat + 1, input.len(), layer_count, maximum_frames, maximum_instructions);
                    }
                }
                let active = outcome?;
                if !active {
                    return Ok(state.frames);
                }
                local_index = local_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_timeline_repetition_step(program, set_initial, repetition as nat, layer_count, maximum_frames, maximum_instructions);
            }
            repetition = repetition.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_timeline_set_step(input, initial, set_index as nat, layer_count, maximum_frames, maximum_instructions);
        }
        set_index = set_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(state.frames)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        requires crate::proofs::internal_specs::part2_timeline_state_valid(timeline_state_view(old(state)), layer_count, maximum_frames, maximum_instructions),
        ensures timeline_step_result(result, final(state)) == crate::specs::part2_timeline_step(
            timeline_state_view(old(state)), timeline_instruction_view(instruction), layer_count, maximum_frames, maximum_instructions),
            result.is_ok() ==> crate::proofs::internal_specs::part2_timeline_state_valid(timeline_state_view(final(state)), layer_count, maximum_frames, maximum_instructions),
    )
)]
pub(super) fn apply_timeline_instruction(
    state: &mut TimelineState,
    instruction: CompositionInstruction,
    layer_count: usize,
    maximum_frames: u32,
    maximum_instructions: usize,
) -> Result<bool, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = timeline_state_view(state); }
    if state.instruction_index >= maximum_instructions {
        let actual = (state.instruction_index as u64)
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: maximum_instructions as u64,
            actual,
        });
    }
    if state.instruction_index >= state.assignments.len() {
        state.assignments.push(None);
    }
    let assigned = match state.assignments.get(state.instruction_index) {
        Some(value) => *value,
        None => None,
    };
    let layer_index = match assigned {
        Some(index) => index,
        None => {
            if state.next_layer >= layer_count {
                return Ok(false);
            }
            let layer = state.next_layer;
            state.next_layer = state
                .next_layer
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
            layer
        }
    };
    append_timeline_frame(
        &mut state.frames,
        &mut state.milliseconds,
        instruction_info(layer_index, instruction),
        instruction.life,
        maximum_frames,
    )?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost assignments = state.assignments@; }
    if instruction.next_reuse != 0 {
        let reuse = usize::try_from(instruction.next_reuse).map_err(|_| arithmetic_overflow())?;
        let target = state
            .instruction_index
            .checked_add(reuse)
            .ok_or_else(arithmetic_overflow)?;
        if target >= maximum_instructions {
            let actual = (target as u64)
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: maximum_instructions as u64,
                actual,
            });
        }
        let mut assignment_count = state.assignments.len();
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant target < maximum_instructions,
                    assignment_count == state.assignments.len(),
                    state.instruction_index == before.3, state.next_layer <= layer_count,
                    before.3 < maximum_instructions,
                    assignments == if before.3 as nat >= before.1.len() { before.1.push(None) } else { before.1 },
                    (before.3 as nat) < assignments.len(),
                    assigned == assignments[before.3 as int],
                    assigned.is_some() ==> layer_index == assigned.unwrap() && state.next_layer == before.2,
                    assigned.is_none() ==> layer_index == before.2 && (state.next_layer as nat) == before.2 as nat + 1 && before.2 < layer_count,
                    crate::specs::part2_timeline_frame(before.0, before.4,
                        crate::specs::part2_timeline_assign(layer_index, timeline_instruction_view(instruction)), instruction.life, maximum_frames)
                        == Ok((frame_views(state.frames@), state.milliseconds)),
                    state.frames.len() <= maximum_frames,
                    assignments.len() <= state.assignments.len() <= maximum_instructions,
                    state.assignments.len() <= if assignments.len() > target as nat { assignments.len() } else { target as nat + 1 },
                    state.assignments@ == assignments + Seq::new((state.assignments.len() - assignments.len()) as nat, |i: int| None),
                decreases target + 1 - assignment_count,
            )
        )]
        while assignment_count <= target {
            state.assignments.push(None);
            assignment_count += 1;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(state.assignments@ =~= assignments + Seq::new((state.assignments.len() - assignments.len()) as nat, |i: int| None));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
                if (target as nat) < assignments.len() {
                    assert(state.assignments.len() == assignments.len());
                    assert(Seq::<Option<usize>>::new(0, |i: int| None) =~= Seq::empty());
                    assert(assignments + Seq::<Option<usize>>::empty() =~= assignments);
                } else {
                    assert(assignment_count > target);
                    assert(state.assignments.len() <= target as nat + 1);
                    assert(state.assignments.len() == target as nat + 1);
                }
                assert(state.assignments@ =~= if (target as nat) < assignments.len() { assignments } else {
                    assignments + Seq::new((target as nat + 1 - assignments.len()) as nat, |i: int| None)
                });
        }
        let slot = state
            .assignments
            .get_mut(target)
            .ok_or_else(arithmetic_overflow)?;
        let conflicting = match slot {
            Some(assigned) => *assigned != layer_index,
            None => false,
        };
        if conflicting {
            return Err(invalid_layer());
        }
        *slot = Some(layer_index);
    }
    state.instruction_index = state
        .instruction_index
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        let goal = crate::specs::part2_timeline_step(before, timeline_instruction_view(instruction), layer_count, maximum_frames, maximum_instructions);
        assert(goal.is_ok());
        assert(goal.ok().unwrap().1.0 == frame_views(state.frames@));
        assert(goal.ok().unwrap().1.1 == state.assignments@);
        assert(goal.ok().unwrap().1.2 == state.next_layer);
        assert(goal.ok().unwrap().1.3 == state.instruction_index);
        assert(goal.ok().unwrap().1.4 == state.milliseconds);
    }
    Ok(true)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        requires old(frames).len() <= maximum_frames,
        ensures timeline_frame_result(result, final(frames)@, *final(time))
            == crate::specs::part2_timeline_frame(frame_views(old(frames)@), *old(time), instruction_view(instruction), life, maximum_frames),
            result.is_ok() ==> final(frames).len() <= maximum_frames,
    )
)]
pub(super) fn append_timeline_frame(
    frames: &mut Vec<JpxFrameInfo>,
    time: &mut u64,
    instruction: JpxInstructionInfo,
    life: u32,
    maximum_frames: u32,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = frame_views(frames@);
        let ghost old_time = *time;
    }
    if life == 0 && !instruction.persistent {
        return Ok(());
    }
    let fresh = match frames.last() {
        Some(frame) => frame.duration_milliseconds != 0,
        None => true,
    };
    if fresh {
        if frames.len() as u64 >= u64::from(maximum_frames) {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::Frames,
                limit: u64::from(maximum_frames),
                actual: frames.len() as u64 + 1,
            });
        }
        let next = JpxFrameInfo {
            index: frames.len(),
            start_milliseconds: *time,
            duration_milliseconds: 0,
            persistent: true,
            instructions: Vec::new(),
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            frame_views_push(frames@, next);
            assert(instruction_views(next.instructions@) =~= Seq::<crate::specs::Part2Instruction>::empty());
        }
        frames.push(next);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(frame_views(frames@) =~= before.push((before.len() as usize, old_time, 0, true, Seq::empty())));
        }
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost prior = frame_views(frames@); }
    let frame = frames.last_mut().ok_or_else(arithmetic_overflow)?;
    frame.duration_milliseconds = life;
    frame.persistent = instruction.persistent;
    #[cfg(verus_keep_ghost)]
    proof! { instruction_views_push(frame.instructions@, instruction); }
    frame.instructions.push(instruction);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(frame_views(frames@) =~= prior.update(prior.len() as int - 1,
            (prior.last().0, prior.last().1, life, instruction.persistent, prior.last().4.push(instruction_view(instruction)))));
    }
    if life != 0 {
        *time = time
            .checked_add(u64::from(life))
            .ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if fresh {
            assert(frame_views(frames@) =~= before.push((before.len() as usize, old_time, life, instruction.persistent, seq![instruction_view(instruction)])));
        }
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures instruction_view(result) == crate::specs::part2_timeline_assign(layer_index, timeline_instruction_view(instruction)),
    )
)]
fn instruction_info(layer_index: usize, instruction: CompositionInstruction) -> JpxInstructionInfo {
    JpxInstructionInfo {
        layer_index,
        target_x: instruction.target_x,
        target_y: instruction.target_y,
        target_width: instruction.target_width,
        target_height: instruction.target_height,
        source_x: instruction.source_x,
        source_y: instruction.source_y,
        source_width: instruction.source_width,
        source_height: instruction.source_height,
        persistent: instruction.persistent,
        next_reuse: instruction.next_reuse,
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures frame_selection_result(result) == crate::specs::part2_select_frame(frame_views(frames@), requested_frame, loop_count),
    )
)]
pub(super) fn select_frame_instructions(
    frames: &[JpxFrameInfo],
    loop_count: u8,
    requested_frame: usize,
) -> Result<Vec<JpxInstructionInfo>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost input = frame_views(frames@); }
    if frames.is_empty() {
        return Err(DecodeError::FrameIndexOutOfRange {
            index: requested_frame,
            frames: 0,
        });
    }
    let frame_index = if loop_count == 0 {
        crate::refinement::loop_frame(requested_frame, frames.len())
    } else {
        let total = frames
            .len()
            .checked_mul(usize::from(loop_count))
            .ok_or_else(arithmetic_overflow)?;
        if requested_frame >= total {
            return Err(DecodeError::FrameIndexOutOfRange {
                index: requested_frame,
                frames: total,
            });
        }
        crate::refinement::loop_frame(requested_frame, frames.len())
    };
    let mut placements = Vec::new();
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_frame_index(requested_frame, input.len(), loop_count) == Ok(frame_index));
        crate::proofs::production_impl::production_frame_sequence_empty(input, frame_index as nat);
        assert(instruction_views(placements@) =~= Seq::<crate::specs::Part2Instruction>::empty());
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= frame_index + 1,
                frame_index < frames.len(),
                input == frame_views(frames@),
                crate::specs::part2_frame_index(requested_frame, input.len(), loop_count) == Ok(frame_index),
                instruction_views(placements@) == crate::specs::part2_frame_instruction_sequence(input, frame_index as nat, index as nat),
            decreases frame_index + 1 - index,
        )
    )]
    while index <= frame_index {
        let frame = frames.get(index).ok_or_else(arithmetic_overflow)?;
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_frame_sequence_step(input, frame_index as nat, index as nat); }
        if index == frame_index || frame.persistent {
            let mut instruction_index = 0_usize;
            let instruction_count = frame.instructions.len();
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost prior = instruction_views(placements@); }
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant instruction_index <= instruction_count,
                        index <= frame_index < frames.len(),
                        input == frame_views(frames@),
                        frame == frames@[index as int],
                        instruction_count == frame.instructions.len(),
                        index == frame_index || frame.persistent,
                        prior == crate::specs::part2_frame_instruction_sequence(input, frame_index as nat, index as nat),
                        instruction_views(placements@) == prior + instruction_views(frame.instructions@).take(instruction_index as int),
                    decreases instruction_count - instruction_index,
                )
            )]
            while instruction_index < instruction_count {
                let instruction = *frame
                    .instructions
                    .get(instruction_index)
                    .ok_or_else(arithmetic_overflow)?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    instruction_views_push(placements@, instruction);
                    assert(instruction_views(frame.instructions@).take(instruction_index as int + 1)
                        =~= instruction_views(frame.instructions@).take(instruction_index as int).push(instruction_view(instruction)));
                }
                placements.push(instruction);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(instruction_views(placements@) =~= prior + instruction_views(frame.instructions@).take(instruction_index as int + 1));
                }
                instruction_index = instruction_index
                    .checked_add(1)
                    .ok_or_else(arithmetic_overflow)?;
            }
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(placements)
}
