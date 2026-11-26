use crate::{DecodeError, MalformedKind, Resource, ResourceLimits};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

const CONTEXT_COUNT: usize = 19;

#[derive(Clone, Copy)]
struct ProbabilityState {
    q_e: u16,
    next_mps: u8,
    next_lps: u8,
    switch_mps: bool,
}

const STATES: [ProbabilityState; 47] = [
    ProbabilityState {
        q_e: 0x5601,
        next_mps: 1,
        next_lps: 1,
        switch_mps: true,
    },
    ProbabilityState {
        q_e: 0x3401,
        next_mps: 2,
        next_lps: 6,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x1801,
        next_mps: 3,
        next_lps: 9,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0ac1,
        next_mps: 4,
        next_lps: 12,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0521,
        next_mps: 5,
        next_lps: 29,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0221,
        next_mps: 38,
        next_lps: 33,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x5601,
        next_mps: 7,
        next_lps: 6,
        switch_mps: true,
    },
    ProbabilityState {
        q_e: 0x5401,
        next_mps: 8,
        next_lps: 14,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x4801,
        next_mps: 9,
        next_lps: 14,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x3801,
        next_mps: 10,
        next_lps: 14,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x3001,
        next_mps: 11,
        next_lps: 17,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x2401,
        next_mps: 12,
        next_lps: 18,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x1c01,
        next_mps: 13,
        next_lps: 20,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x1601,
        next_mps: 29,
        next_lps: 21,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x5601,
        next_mps: 15,
        next_lps: 14,
        switch_mps: true,
    },
    ProbabilityState {
        q_e: 0x5401,
        next_mps: 16,
        next_lps: 14,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x5101,
        next_mps: 17,
        next_lps: 15,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x4801,
        next_mps: 18,
        next_lps: 16,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x3801,
        next_mps: 19,
        next_lps: 17,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x3401,
        next_mps: 20,
        next_lps: 18,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x3001,
        next_mps: 21,
        next_lps: 19,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x2801,
        next_mps: 22,
        next_lps: 19,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x2401,
        next_mps: 23,
        next_lps: 20,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x2201,
        next_mps: 24,
        next_lps: 21,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x1c01,
        next_mps: 25,
        next_lps: 22,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x1801,
        next_mps: 26,
        next_lps: 23,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x1601,
        next_mps: 27,
        next_lps: 24,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x1401,
        next_mps: 28,
        next_lps: 25,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x1201,
        next_mps: 29,
        next_lps: 26,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x1101,
        next_mps: 30,
        next_lps: 27,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0ac1,
        next_mps: 31,
        next_lps: 28,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x09c1,
        next_mps: 32,
        next_lps: 29,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x08a1,
        next_mps: 33,
        next_lps: 30,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0521,
        next_mps: 34,
        next_lps: 31,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0441,
        next_mps: 35,
        next_lps: 32,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x02a1,
        next_mps: 36,
        next_lps: 33,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0221,
        next_mps: 37,
        next_lps: 34,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0141,
        next_mps: 38,
        next_lps: 35,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0111,
        next_mps: 39,
        next_lps: 36,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0085,
        next_mps: 40,
        next_lps: 37,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0049,
        next_mps: 41,
        next_lps: 38,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0025,
        next_mps: 42,
        next_lps: 39,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0015,
        next_mps: 43,
        next_lps: 40,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0009,
        next_mps: 44,
        next_lps: 41,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0005,
        next_mps: 45,
        next_lps: 42,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x0001,
        next_mps: 45,
        next_lps: 43,
        switch_mps: false,
    },
    ProbabilityState {
        q_e: 0x5601,
        next_mps: 46,
        next_lps: 46,
        switch_mps: false,
    },
];

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct MqContext {
    state: u8,
    mps: bool,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct MqContextState {
    contexts: [MqContext; CONTEXT_COUNT],
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct MqDecoder<'a> {
    input: &'a [u8],
    byte_index: usize,
    a: u32,
    c: u32,
    ct: u8,
    contexts: [MqContext; CONTEXT_COUNT],
    work_units: u64,
    maximum_work_units: u64,
    marker_padding_count: u64,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn mq_context_view(context: MqContext) -> crate::specs::Part1MqContext {
        (context.state, context.mps)
    }

    pub closed spec fn mq_context_state_view(state: MqContextState) -> Seq<crate::specs::Part1MqContext> {
        state.contexts@.map_values(|c: MqContext| mq_context_view(c))
    }

    pub closed spec fn mq_decoder_view(decoder: &MqDecoder<'_>) -> crate::specs::Part1MqState {
        crate::specs::Part1MqState {
            input: decoder.input@, byte_index: decoder.byte_index,
            a: decoder.a, c: decoder.c, ct: decoder.ct,
            contexts: decoder.contexts@.map_values(|c: MqContext| mq_context_view(c)),
            work_units: decoder.work_units, maximum_work_units: decoder.maximum_work_units,
            marker_padding_count: decoder.marker_padding_count,
        }
    }

    #[verifier::inline]
    pub open spec fn mq_decoder_outcome(result: Result<MqDecoder<'_>, DecodeError>)
        -> Result<crate::specs::Part1MqState, DecodeError>
    {
        match result {
            Ok(decoder) => Ok(mq_decoder_view(&decoder)),
            Err(error) => Err(error),
        }
    }

    #[verifier::inline]
    pub open spec fn mq_context_outcome(result: Result<MqContext, DecodeError>)
        -> Result<crate::specs::Part1MqContext, DecodeError>
    {
        match result {
            Ok(context) => Ok(mq_context_view(context)),
            Err(error) => Err(error),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_mq_error(offset, kind),
))]
fn mq_error(offset: usize, kind: MalformedKind) -> DecodeError {
    DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_mq_limit(resource, limit, actual),
))]
pub(crate) fn mq_limit(resource: Resource, limit: u64, actual: u64) -> DecodeError {
    DecodeError::LimitExceeded {
        resource,
        limit,
        actual,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires index < STATES.len(),
    ensures (result.q_e, result.next_mps, result.next_lps, result.switch_mps)
        == crate::specs::part1_mq_probabilities()[index as int],
))]
fn probability_state(index: usize) -> ProbabilityState {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(STATES.len() == 47);
        assert(STATES@.map_values(|p: ProbabilityState|
            (p.q_e, p.next_mps, p.next_lps, p.switch_mps))
            =~= crate::specs::part1_mq_probabilities());
    }
    STATES[index]
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures mq_decoder_outcome(result) == crate::specs::part1_mq_initial(
        input@, maximum_input_bytes, maximum_work_units),
))]
pub(crate) fn mq_from_input(
    input: &[u8],
    maximum_input_bytes: u64,
    maximum_work_units: u64,
) -> Result<MqDecoder<'_>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_mq_initial); }
    let input_length = input.len() as u64;
    if input_length > maximum_input_bytes {
        return Err(mq_limit(
            Resource::InputBytes,
            maximum_input_bytes,
            input_length,
        ));
    }
    let mut decoder = MqDecoder {
        input,
        byte_index: 0,
        a: 0x8000,
        c: if input.is_empty() {
            0x00ff_0000
        } else {
            u32::from(input[0]) << 16
        },
        ct: 0,
        contexts: [MqContext {
            state: 0,
            mps: false,
        }; CONTEXT_COUNT],
        work_units: 0,
        maximum_work_units,
        marker_padding_count: 0,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(mq_decoder_view(&decoder).contexts =~= Seq::new(19, |i: int| (0u8, false)));
    }
    decoder.byte_in()?;
    decoder.c = match decoder.c.checked_mul(128) {
        Some(code) => code,
        None => return Err(mq_error(0, MalformedKind::ArithmeticOverflow)),
    };
    decoder.ct = match decoder.ct.checked_sub(7) {
        Some(count) => count,
        None => return Err(mq_error(0, MalformedKind::InvalidMqState)),
    };
    Ok(decoder)
}

impl<'a> MqDecoder<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        mq_from_input(
            input,
            limits.maximum_input_bytes(),
            limits.maximum_work_units(),
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, mq_decoder_view(final(self))) == crate::specs::part1_mq_set_context(
            mq_decoder_view(old(self)), context, state, mps),
    ))]
    pub fn set_context(&mut self, context: usize, state: u8, mps: bool) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = mq_decoder_view(self); }
        if context >= self.contexts.len() || usize::from(state) >= STATES.len() {
            return Err(mq_error(self.byte_index, MalformedKind::InvalidMqState));
        }
        self.contexts[context] = MqContext { state, mps };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(mq_decoder_view(self).contexts =~= before.contexts.update(context as int, (state, mps)));
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures mq_decoder_view(final(self)) == (crate::specs::Part1MqState {
            contexts: Seq::new(19, |i: int| (0u8, false)), ..mq_decoder_view(old(self))
        }),
    ))]
    pub fn reset_contexts(&mut self) {
        self.contexts = [MqContext {
            state: 0,
            mps: false,
        }; CONTEXT_COUNT];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(mq_decoder_view(self).contexts =~= Seq::new(19, |i: int| (0u8, false)));
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures mq_context_state_view(result) == mq_decoder_view(self).contexts,
    ))]
    pub const fn context_state(&self) -> MqContextState {
        MqContextState {
            contexts: self.contexts,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures mq_decoder_view(final(self)) == (crate::specs::Part1MqState {
            contexts: mq_context_state_view(state), ..mq_decoder_view(old(self))
        }),
    ))]
    pub fn restore_context_state(&mut self, state: MqContextState) {
        self.contexts = state.contexts;
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures mq_context_outcome(result) == if context >= mq_decoder_view(self).contexts.len() {
            Err(crate::specs::part1_mq_error(mq_decoder_view(self).byte_index, MalformedKind::InvalidMqState))
        } else { Ok(mq_decoder_view(self).contexts[context as int]) },
    ))]
    pub fn context(&self, context: usize) -> Result<MqContext, DecodeError> {
        if context >= self.contexts.len() {
            return Err(mq_error(self.byte_index, MalformedKind::InvalidMqState));
        }
        Ok(self.contexts[context])
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_mq_bytes_consumed(mq_decoder_view(self)),
    ))]
    pub const fn bytes_consumed(&self) -> usize {
        if self.byte_index >= self.input.len() {
            self.input.len()
        } else {
            self.byte_index + 1
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == mq_decoder_view(self).marker_padding_count,
    ))]
    pub const fn marker_padding_count(&self) -> u64 {
        self.marker_padding_count
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_mq_termination(mq_decoder_view(self)),
    ))]
    pub fn validate_predictable_termination(&self) -> Result<(), DecodeError> {
        let remaining = self.input.len().saturating_sub(self.bytes_consumed());
        if remaining > 2 || self.marker_padding_count > 2 {
            return Err(mq_error(self.byte_index, MalformedKind::InvalidCodeBlock));
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, mq_decoder_view(final(self))) == crate::specs::part1_mq_decode(
            mq_decoder_view(old(self)), context_index),
    ))]
    #[inline]
    pub fn decode(&mut self, context_index: usize) -> Result<bool, DecodeError> {
        if context_index >= self.contexts.len() {
            return Err(mq_error(self.byte_index, MalformedKind::InvalidMqState));
        }
        self.charge_work()?;
        let context = self.contexts[context_index];
        let state_index = usize::from(context.state);
        if state_index >= STATES.len() {
            return Err(mq_error(self.byte_index, MalformedKind::InvalidMqState));
        }
        let probability = probability_state(state_index);
        if u32::from(probability.q_e) > self.a {
            return Err(mq_error(self.byte_index, MalformedKind::InvalidMqState));
        }
        self.a = crate::refinement::mq_interval_subtract(self.a, probability.q_e);

        let decision;
        if (self.c >> 16) < u32::from(probability.q_e) {
            if self.a < u32::from(probability.q_e) {
                self.a = u32::from(probability.q_e);
                decision = crate::refinement::mq_decision(context.mps, false);
                self.transition(context_index, probability.next_mps, false)?;
            } else {
                self.a = u32::from(probability.q_e);
                decision = crate::refinement::mq_decision(context.mps, true);
                self.transition(context_index, probability.next_lps, probability.switch_mps)?;
            }
            self.renormalize()?;
        } else {
            let qe_code = u64::from(probability.q_e) * 65_536;
            if qe_code > u64::from(self.c) {
                return Err(mq_error(self.byte_index, MalformedKind::InvalidMqState));
            }
            self.c = crate::refinement::mq_code_subtract(self.c, probability.q_e);
            if self.a & 0x8000 == 0 {
                if self.a < u32::from(probability.q_e) {
                    decision = crate::refinement::mq_decision(context.mps, true);
                    self.transition(context_index, probability.next_lps, probability.switch_mps)?;
                } else {
                    decision = crate::refinement::mq_decision(context.mps, false);
                    self.transition(context_index, probability.next_mps, false)?;
                }
                self.renormalize()?;
            } else {
                decision = crate::refinement::mq_decision(context.mps, false);
            }
        }
        Ok(decision)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, mq_decoder_view(final(self))) == crate::specs::part1_mq_renormalize(
            mq_decoder_view(old(self)), 16),
    ))]
    fn renormalize(&mut self) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = mq_decoder_view(self); }
        let mut remaining_shifts = 16_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant remaining_shifts <= 16,
                    initial == mq_decoder_view(old(self)),
                    crate::specs::part1_mq_renormalize(initial, 16)
                        == crate::specs::part1_mq_renormalize(mq_decoder_view(self), remaining_shifts as nat),
                decreases remaining_shifts,
            )
        )]
        while self.a < 0x8000 {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part1_mq_renormalize);
            }
            if remaining_shifts == 0 {
                return Err(mq_error(self.byte_index, MalformedKind::InvalidMqState));
            }
            remaining_shifts -= 1;
            if self.ct == 0 {
                self.byte_in()?;
            }
            if self.a > u32::MAX / 2 || self.c > u32::MAX / 2 || self.ct == 0 {
                return Err(mq_error(self.byte_index, MalformedKind::ArithmeticOverflow));
            }
            self.a = crate::refinement::mq_renorm_double(self.a);
            self.c = crate::refinement::mq_renorm_double(self.c);
            self.ct = crate::refinement::mq_renorm_ct(self.ct);
            self.charge_work()?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_mq_renormalize);
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, mq_decoder_view(final(self))) == crate::specs::part1_mq_byte_in(
            mq_decoder_view(old(self))),
    ))]
    fn byte_in(&mut self) -> Result<(), DecodeError> {
        let current = self.current_byte();
        let next = self.next_byte();
        let class = crate::refinement::mq_byte_class(current, next);
        if crate::refinement::mq_byte_advances(current, next) {
            self.advance_byte()?;
        }
        self.c = match self
            .c
            .checked_add(crate::refinement::mq_byte_addend(current, next))
        {
            Some(code) => code,
            None => return Err(mq_error(self.byte_index, MalformedKind::ArithmeticOverflow)),
        };
        self.ct = crate::refinement::mq_byte_ct(current, next);
        if class == 0 {
            self.marker_padding_count = match self.marker_padding_count.checked_add(1) {
                Some(count) => count,
                None => return Err(mq_error(self.byte_index, MalformedKind::ArithmeticOverflow)),
            };
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_mq_current(mq_decoder_view(self)),
    ))]
    fn current_byte(&self) -> u8 {
        if self.byte_index < self.input.len() {
            self.input[self.byte_index]
        } else {
            0xff
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_mq_next(mq_decoder_view(self)),
    ))]
    fn next_byte(&self) -> u8 {
        match self.byte_index.checked_add(1) {
            Some(next_index) if next_index < self.input.len() => self.input[next_index],
            _ => 0xff,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, mq_decoder_view(final(self))) == crate::specs::part1_mq_advance(
            mq_decoder_view(old(self))),
    ))]
    fn advance_byte(&mut self) -> Result<(), DecodeError> {
        if self.byte_index < self.input.len() {
            self.byte_index = match self.byte_index.checked_add(1) {
                Some(index) => index,
                None => return Err(mq_error(self.byte_index, MalformedKind::ArithmeticOverflow)),
            };
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, mq_decoder_view(final(self))) == crate::specs::part1_mq_transition(
            mq_decoder_view(old(self)), context_index, next_state, switch_mps),
    ))]
    fn transition(
        &mut self,
        context_index: usize,
        next_state: u8,
        switch_mps: bool,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = mq_decoder_view(self); }
        if context_index >= self.contexts.len() || usize::from(next_state) >= STATES.len() {
            return Err(mq_error(self.byte_index, MalformedKind::InvalidMqState));
        }
        let mut context = self.contexts[context_index];
        context.state = next_state;
        context.mps = crate::refinement::mq_next_mps(context.mps, switch_mps);
        self.contexts[context_index] = context;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(mq_decoder_view(self).contexts =~= before.contexts.update(
                context_index as int,
                (next_state, before.contexts[context_index as int].1 != switch_mps),
            ));
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, mq_decoder_view(final(self))) == crate::specs::part1_mq_charge(
            mq_decoder_view(old(self))),
    ))]
    #[inline]
    fn charge_work(&mut self) -> Result<(), DecodeError> {
        self.work_units = match self.work_units.checked_add(1) {
            Some(work) => work,
            None => return Err(mq_error(self.byte_index, MalformedKind::ArithmeticOverflow)),
        };
        if self.work_units > self.maximum_work_units {
            return Err(mq_limit(
                Resource::WorkUnits,
                self.maximum_work_units,
                self.work_units,
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Snapshot = (Vec<u8>, usize, u32, u32, u8, [MqContext; 19], u64, u64, u64);

    fn snapshot(decoder: &MqDecoder<'_>) -> Snapshot {
        (
            decoder.input.to_vec(),
            decoder.byte_index,
            decoder.a,
            decoder.c,
            decoder.ct,
            decoder.contexts,
            decoder.work_units,
            decoder.maximum_work_units,
            decoder.marker_padding_count,
        )
    }

    fn supplied_state(input: &[u8]) -> MqDecoder<'_> {
        MqDecoder {
            input,
            byte_index: 0,
            a: 0x8000,
            c: 0,
            ct: 8,
            contexts: [MqContext {
                state: 0,
                mps: false,
            }; 19],
            work_units: 0,
            maximum_work_units: u64::MAX,
            marker_padding_count: 0,
        }
    }

    #[test]
    fn initialization_all_two_byte_inputs_has_exact_registers_and_contexts() {
        for first in 0..=u8::MAX {
            for second in 0..=u8::MAX {
                let input = [first, second];
                let decoder = mq_from_input(&input, 2, 0).unwrap();
                let marker = first == 255 && second > 143;
                let stuffed = first == 255 && !marker;
                let increment = if marker {
                    65280
                } else {
                    u64::from(second) * if stuffed { 512 } else { 256 }
                };
                let expected = (
                    input.to_vec(),
                    usize::from(!marker),
                    32768,
                    ((u64::from(first) * 65536 + increment) * 128) as u32,
                    if stuffed { 0 } else { 1 },
                    [MqContext {
                        state: 0,
                        mps: false,
                    }; 19],
                    0,
                    0,
                    u64::from(marker),
                );
                assert_eq!(snapshot(&decoder), expected);
                assert_eq!(
                    mq_from_input(&input, 1, 0).unwrap_err(),
                    DecodeError::LimitExceeded {
                        resource: Resource::InputBytes,
                        limit: 1,
                        actual: 2
                    },
                );
            }
        }
        let empty = mq_from_input(&[], 0, 0).unwrap();
        assert_eq!(
            snapshot(&empty),
            (
                vec![],
                0,
                32768,
                0x7fff8000,
                1,
                [MqContext {
                    state: 0,
                    mps: false
                }; 19],
                0,
                0,
                1,
            )
        );
    }

    #[test]
    fn all_native_context_indices_states_and_mps_preserve_fast_path_whole_state() {
        for index in 0..19 {
            for state in 0..=u8::MAX {
                for mps in [false, true] {
                    let mut decoder = supplied_state(&[0x23, 0xff, 0x90]);
                    decoder.byte_index = usize::MAX;
                    decoder.ct = u8::MAX;
                    decoder.marker_padding_count = u64::MAX;
                    decoder.contexts[index] = MqContext { state, mps };
                    let mut expected = snapshot(&decoder);
                    expected.6 = 1;
                    if state < 47 {
                        let qe = u32::from(STATES[usize::from(state)].q_e);
                        decoder.a = 0x18000 + qe;
                        decoder.c = (qe << 16) + 123;
                        expected.2 = 0x18000;
                        expected.3 = 123;
                        assert_eq!(decoder.decode(index), Ok(mps));
                    } else {
                        assert_eq!(
                            decoder.decode(index),
                            Err(mq_error(usize::MAX, MalformedKind::InvalidMqState))
                        );
                    }
                    assert_eq!(
                        snapshot(&decoder),
                        expected,
                        "index={index}, state={state}, mps={mps}"
                    );
                }
            }
        }
    }

    #[test]
    fn arithmetic_exchanges_cover_both_intervals_decisions_and_context_transitions() {
        for (a, c, expected_a, expected_c, next_state, mps, decision, work, ct) in [
            (0x8000, 0, 0xac02, 0, 1, false, false, 2, 7),
            (0x10000, 0, 0xac02, 0, 1, true, true, 2, 7),
            (0x8000, 0x56010000, 0xa7fc, 0, 1, true, true, 3, 6),
            (0x10000, 0x56010000, 0xa9ff, 0, 0, false, false, 1, 8),
            (0xc000, 0x56010000, 0xd3fe, 0, 1, false, false, 2, 7),
        ] {
            let mut decoder = supplied_state(&[0x11, 0x22]);
            decoder.a = a;
            decoder.c = c;
            let mut expected = snapshot(&decoder);
            expected.2 = expected_a;
            expected.3 = expected_c;
            expected.4 = ct;
            expected.5[7] = MqContext {
                state: next_state,
                mps,
            };
            expected.6 = work;
            assert_eq!(decoder.decode(7), Ok(decision));
            assert_eq!(snapshot(&decoder), expected);
        }
    }

    #[test]
    fn first_errors_and_partial_mutations_are_not_transactional() {
        let mut decoder = supplied_state(&[]);
        decoder.work_units = u64::MAX;
        let before = snapshot(&decoder);
        assert_eq!(
            decoder.decode(19),
            Err(mq_error(0, MalformedKind::InvalidMqState))
        );
        assert_eq!(snapshot(&decoder), before);
        assert_eq!(
            decoder.decode(0),
            Err(mq_error(0, MalformedKind::ArithmeticOverflow))
        );
        assert_eq!(snapshot(&decoder), before);

        decoder.work_units = 0;
        decoder.maximum_work_units = 0;
        decoder.contexts[0].state = 255;
        let mut expected = snapshot(&decoder);
        expected.6 = 1;
        assert_eq!(decoder.decode(0), Err(mq_limit(Resource::WorkUnits, 0, 1)));
        assert_eq!(snapshot(&decoder), expected);

        let mut decoder = supplied_state(&[0xff, 0x90]);
        decoder.maximum_work_units = 1;
        let mut expected = snapshot(&decoder);
        expected.2 = 0xac02;
        expected.4 = 7;
        expected.5[0].state = 1;
        expected.6 = 2;
        assert_eq!(decoder.decode(0), Err(mq_limit(Resource::WorkUnits, 1, 2)));
        assert_eq!(snapshot(&decoder), expected);

        let mut decoder = supplied_state(&[0x01, 0x20]);
        decoder.c = u32::MAX;
        decoder.ct = 0;
        let mut expected = snapshot(&decoder);
        expected.1 = 1;
        assert_eq!(
            decoder.byte_in(),
            Err(mq_error(1, MalformedKind::ArithmeticOverflow))
        );
        assert_eq!(snapshot(&decoder), expected);

        let mut decoder = supplied_state(&[0xff, 0x90]);
        decoder.ct = 0;
        decoder.marker_padding_count = u64::MAX;
        let mut expected = snapshot(&decoder);
        expected.3 = 0xff00;
        expected.4 = 8;
        assert_eq!(
            decoder.byte_in(),
            Err(mq_error(0, MalformedKind::ArithmeticOverflow))
        );
        assert_eq!(snapshot(&decoder), expected);
    }

    #[test]
    fn supplied_zero_interval_renormalizes_only_sixteen_times_with_exact_error_state() {
        let mut decoder = supplied_state(&[0xff, 0x90]);
        decoder.a = 0;
        let mut expected = snapshot(&decoder);
        expected.3 = 0xff0000;
        expected.4 = 0;
        expected.6 = 16;
        expected.8 = 1;
        assert_eq!(
            decoder.renormalize(),
            Err(mq_error(0, MalformedKind::InvalidMqState))
        );
        assert_eq!(snapshot(&decoder), expected);
    }

    #[test]
    fn state_table_transitions_are_bounded() {
        for state in STATES {
            assert!(usize::from(state.next_mps) < STATES.len());
            assert!(usize::from(state.next_lps) < STATES.len());
            assert!(state.q_e > 0);
        }
    }

    #[test]
    fn decodes_deterministic_symbol_sequence() {
        let limits = ResourceLimits::default();
        let mut first = MqDecoder::new(&[0x00, 0x00, 0x00, 0x00], &limits).unwrap();
        let mut second = MqDecoder::new(&[0x00, 0x00, 0x00, 0x00], &limits).unwrap();
        let mut first_symbols = Vec::new();
        let mut second_symbols = Vec::new();
        for _ in 0..32 {
            first_symbols.push(first.decode(0).unwrap());
            second_symbols.push(second.decode(0).unwrap());
        }
        assert_eq!(first_symbols, second_symbols);
        assert_eq!(
            first_symbols,
            [
                false, true, true, false, true, false, true, false, true, false, true, false, true,
                false, true, false, true, false, true, false, true, false, true, false, true,
                false, true, false, true, false, true, true,
            ]
        );
        assert!(first.bytes_consumed() <= 4);
    }

    #[test]
    fn validates_context_state_and_work_limits() {
        let limits = ResourceLimits::default()
            .with_maximum_work_units(1)
            .unwrap();
        let mut decoder = MqDecoder::new(&[0], &limits).unwrap();
        assert!(decoder.set_context(0, 47, false).is_err());
        assert!(decoder.context(CONTEXT_COUNT).is_err());
        let _ = decoder.decode(0);
        assert!(matches!(
            decoder.decode(0),
            Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                ..
            })
        ));
    }

    #[test]
    fn preserves_probability_contexts_across_segments() {
        let limits = ResourceLimits::default();
        let mut first = MqDecoder::new(&[0, 0], &limits).unwrap();
        first.set_context(0, 4, false).unwrap();
        let _ = first.decode(0).unwrap();
        let state = first.context_state();

        let mut second = MqDecoder::new(&[0, 0], &limits).unwrap();
        second.restore_context_state(state);
        assert_eq!(second.context(0).unwrap(), first.context(0).unwrap());
    }

    #[test]
    fn handles_marker_padding_without_out_of_bounds_reads() {
        let mut decoder = MqDecoder::new(&[0xff, 0x90], &ResourceLimits::default()).unwrap();
        for _ in 0..16 {
            let _ = decoder.decode(0);
        }
        assert!(decoder.marker_padding_count() > 0);
        assert!(decoder.bytes_consumed() <= 2);
    }

    #[test]
    fn validates_predictable_termination_bounds() {
        let limits = ResourceLimits::default();
        let short = MqDecoder::new(&[0, 0], &limits).unwrap();
        short.validate_predictable_termination().unwrap();

        let long = MqDecoder::new(&[0; 8], &limits).unwrap();
        assert!(long.validate_predictable_termination().is_err());
    }
}
