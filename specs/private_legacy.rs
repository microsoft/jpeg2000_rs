//! Verified single-contribution collapse and logical-state equivalence for private legacy tiles.
use super::*;

verus! {

pub(crate) open spec fn private_legacy_style_ok(style: crate::tier1::Tier1CodingStyle) -> bool {
    matches!(style.block_coding, crate::tier1::Tier1BlockCoding::Legacy)
        && !style.force_high_throughput
        && !style.selective_arithmetic_coding_bypass
        && !style.reset_contexts
        && !style.terminate_all_passes
        && !style.segmentation_symbols
        && !style.predictable_termination
}

pub(crate) proof fn private_legacy_segment_passes_all(
    style: crate::tier1::Tier1CodingStyle,
    first: u32,
    count: u32,
)
    requires
        private_legacy_style_ok(style),
        count > 0,
        first as nat + count as nat <= u32::MAX,
    ensures
        part1_legacy_segment_passes(style, first, count) == count,
    decreases count,
{
    if count > 1 {
        assert(!part1_legacy_plan(style, first).terminates_segment);
        private_legacy_segment_passes_all(style, (first + 1) as u32, (count - 1) as u32);
    }
}

pub(crate) open spec fn private_legacy_with_work(s: Tier1DecoderState, work: u64) -> Tier1DecoderState {
    Tier1DecoderState { legacy_decode_work: work, ..s }
}

#[verifier::spinoff_prover]
proof fn private_legacy_ensure_bitplane_work_indep(
    s: Tier1DecoderState,
    work: u64,
)
    ensures
        ({
            let a = part1_legacy_ensure_bitplane(s);
            let b = part1_legacy_ensure_bitplane(private_legacy_with_work(s, work));
            a.0 == b.0 && b.1 == private_legacy_with_work(a.1, work)
        }),
{
    hide(part1_legacy_bitplane_initial);
}

#[verifier::spinoff_prover]
proof fn private_legacy_decode_pass_work_indep(
    s: Tier1DecoderState,
    work: u64,
    symbols: Part1LegacySymbols,
    kind: crate::tier1::Tier1PassKind,
)
    ensures
        ({
            let a = part1_legacy_decode_pass(s, symbols, kind);
            let b = part1_legacy_decode_pass(private_legacy_with_work(s, work), symbols, kind);
            a.0 == b.0 && b.1 == private_legacy_with_work(a.1, work) && a.2 == b.2
        }),
{
    hide(part1_legacy_cleanup_pass);
    hide(part1_legacy_pass);
    hide(part1_legacy_ensure_bitplane);
    reveal(part1_legacy_decode_pass);
    private_legacy_ensure_bitplane_work_indep(s, work);
    let r1 = part1_legacy_ensure_bitplane(s);
    let r2 = part1_legacy_ensure_bitplane(private_legacy_with_work(s, work));
    if r1.0.is_ok() {
        if let Some(st) = r1.1.bitplane_state {
            if !((symbols is Raw) && (kind is Cleanup)) {
                assert(r2.1.plane == r1.1.plane);
                assert(r2.1.bitplane_state == Some(st));
                assert(r2.1.orientation == r1.1.orientation);
                assert(r2.1.style == r1.1.style);
            }
        }
    }
}

#[verifier::spinoff_prover]
proof fn private_legacy_advance_work_indep(
    s: Tier1DecoderState,
    work: u64,
    kind: crate::tier1::Tier1PassKind,
)
    ensures
        ({
            let a = part1_legacy_advance(s, kind);
            let b = part1_legacy_advance(private_legacy_with_work(s, work), kind);
            a.0 == b.0 && b.1 == private_legacy_with_work(a.1, work)
        }),
{
}

#[verifier::spinoff_prover]
proof fn private_legacy_segment_step_work_indep(
    s: Part1LegacySegmentRun,
    work: u64,
)
    ensures
        ({
            let a = part1_legacy_segment_step(s);
            let s2 = Part1LegacySegmentRun {
                decoder: private_legacy_with_work(s.decoder, work),
                ..s
            };
            let b = part1_legacy_segment_step(s2);
            a.0 == b.0
                && b.1 == (Part1LegacySegmentRun {
                    decoder: private_legacy_with_work(a.1.decoder, work),
                    ..a.1
                })
        }),
{
    hide(part1_legacy_initialized);
    hide(tier1_statistics_merge);
    hide(part1_legacy_plan);
    hide(part1_legacy_advance);
    reveal(part1_legacy_segment_step);
    let plan = part1_legacy_plan(s.decoder.style, s.decoder.next_pass);
    private_legacy_decode_pass_work_indep(s.decoder, work, s.symbols, plan.kind);
    let dec1 = part1_legacy_decode_pass(s.decoder, s.symbols, plan.kind);
    if dec1.0.is_ok() {
        private_legacy_advance_work_indep(dec1.1, work, plan.kind);
    }
}

#[verifier::spinoff_prover]
proof fn private_legacy_segment_run_work_indep(
    s: Part1LegacySegmentRun,
    work: u64,
    remaining: nat,
)
    ensures
        ({
            let a = part1_legacy_segment_run(s, remaining);
            let s2 = Part1LegacySegmentRun {
                decoder: Tier1DecoderState { legacy_decode_work: work, ..s.decoder },
                ..s
            };
            let b = part1_legacy_segment_run(s2, remaining);
            a.0 == b.0
                && b.1 == (Part1LegacySegmentRun {
                    decoder: Tier1DecoderState { legacy_decode_work: work, ..a.1.decoder },
                    ..a.1
                })
        }),
    decreases remaining,
{
    if remaining > 0 {
        private_legacy_segment_step_work_indep(s, work);
        let step1 = part1_legacy_segment_step(s);
        if step1.0.is_ok() {
            private_legacy_segment_run_work_indep(step1.1, work, (remaining - 1) as nat);
        }
    }
}

#[verifier::spinoff_prover]
proof fn private_legacy_segment_account_work_indep(
    s: Tier1DecoderState,
    work: u64,
    bytes: nat,
    count: u32,
    statistics: crate::tier1::Tier1PassStatistics,
)
    ensures
        ({
            let s2 = Tier1DecoderState { legacy_decode_work: work, ..s };
            let a = part1_legacy_segment_account(s, bytes, count, statistics);
            let b = part1_legacy_segment_account(s2, bytes, count, statistics);
            a.0 == b.0 && b.1 == (Tier1DecoderState { legacy_decode_work: work, ..a.1 })
        }),
{
    reveal(part1_legacy_segment_account);
}

#[verifier::spinoff_prover]
proof fn private_legacy_segment_mq_finish_work_indep(
    run1: Part1LegacySegmentEffect,
    work: u64,
    bytes: nat,
    count: u32,
)
    ensures
        ({
            let run2 = (
                run1.0,
                Part1LegacySegmentRun {
                    decoder: Tier1DecoderState { legacy_decode_work: work, ..run1.1.decoder },
                    ..run1.1
                },
            );
            let a = part1_legacy_segment_mq_finish(part1_legacy_segment_finish(run1), bytes, count);
            let b = part1_legacy_segment_mq_finish(part1_legacy_segment_finish(run2), bytes, count);
            a.0 == b.0 && b.1 == (Tier1DecoderState { legacy_decode_work: work, ..a.1 })
        }),
{
    hide(part1_mq_termination);
    if run1.0.is_ok() {
        if let Part1LegacySymbols::Mq(mq) = run1.1.symbols {
            private_legacy_segment_account_work_indep(
                Tier1DecoderState { mq_context_state: Some(mq.contexts), ..run1.1.decoder },
                work,
                bytes,
                count,
                run1.1.statistics,
            );
        }
    }
}

#[verifier::spinoff_prover]
proof fn private_legacy_segment_raw_finish_work_indep(
    run1: Part1LegacySegmentEffect,
    work: u64,
    bytes: nat,
    count: u32,
)
    ensures
        ({
            let run2 = (
                run1.0,
                Part1LegacySegmentRun {
                    decoder: Tier1DecoderState { legacy_decode_work: work, ..run1.1.decoder },
                    ..run1.1
                },
            );
            let a = part1_legacy_segment_raw_finish(part1_legacy_segment_finish(run1), bytes, count);
            let b = part1_legacy_segment_raw_finish(part1_legacy_segment_finish(run2), bytes, count);
            a.0 == b.0 && b.1 == (Tier1DecoderState { legacy_decode_work: work, ..a.1 })
        }),
{
    hide(part1_raw_reader_termination);
    if run1.0.is_ok() {
        if let Part1LegacySymbols::Raw(_) = run1.1.symbols {
            private_legacy_segment_account_work_indep(
                run1.1.decoder,
                work,
                bytes,
                count,
                run1.1.statistics,
            );
        }
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn private_legacy_segment_work_indep(
    s: Tier1DecoderState,
    work: u64,
    input: Seq<u8>,
    count: u32,
    pass_limit: u32,
    byte_limit: u64,
    input_limit: u64,
    work_limit: u64,
)
    ensures
        ({
            let a = part1_legacy_segment(s, input, count, pass_limit, byte_limit, input_limit, work_limit);
            let s2 = Tier1DecoderState { legacy_decode_work: work, ..s };
            let b = part1_legacy_segment(s2, input, count, pass_limit, byte_limit, input_limit, work_limit);
            a.0 == b.0 && b.1 == (Tier1DecoderState { legacy_decode_work: work, ..a.1 })
        }),
{
    reveal(part1_legacy_segment);
    reveal(part1_legacy_segment_admission);
    let s2 = Tier1DecoderState { legacy_decode_work: work, ..s };
    if part1_legacy_segment_admission(s, input, count, pass_limit, byte_limit).is_ok() {
        if part1_legacy_plan(s.style, s.next_pass).coding_mode is Mq {
            if let Ok(mq) = part1_mq_initial(input, input_limit, work_limit) {
                let r1 = part1_legacy_segment_setup(s, mq);
                let r2 = part1_legacy_segment_setup(s2, mq);
                assert(r2.0 == (Tier1DecoderState { legacy_decode_work: work, ..r1.0 }) && r2.1 == r1.1);
                let init_run = Part1LegacySegmentRun {
                    decoder: r1.0,
                    symbols: Part1LegacySymbols::Mq(r1.1),
                    statistics: tier1_statistics_zero(),
                };
                private_legacy_segment_run_work_indep(init_run, work, count as nat);
                let run1 = part1_legacy_segment_run(init_run, count as nat);
                private_legacy_segment_mq_finish_work_indep(run1, work, input.len(), count);
            }
        } else if let Ok(raw) = part1_raw_reader_initial(input, input_limit, work_limit) {
            let init_run = Part1LegacySegmentRun {
                decoder: s,
                symbols: Part1LegacySymbols::Raw(raw),
                statistics: tier1_statistics_zero(),
            };
            private_legacy_segment_run_work_indep(init_run, work, count as nat);
            let run1 = part1_legacy_segment_run(init_run, count as nat);
            private_legacy_segment_raw_finish_work_indep(run1, work, input.len(), count);
        }
    }
}

pub struct PrivateLegacyBlockSpec {
    pub width: u16,
    pub height: u16,
    pub significant_bitplanes: u16,
    pub orientation: crate::tier1::SubbandOrientation,
    pub style: crate::tier1::Tier1CodingStyle,
    pub allow_multiple_ht_sets: bool,
    pub ht_magnitude_bound: u8,
    pub contribution: Option<(Part1CodeBlockContribution, Seq<u8>)>,
}

pub(crate) open spec fn private_legacy_empty_plane(width: u16, height: u16) -> Tier1RawPlane {
    Tier1RawPlane {
        width,
        height,
        coefficients: Seq::new((width as nat) * (height as nat), |_: int| tier1_empty_coefficient()),
    }
}

pub(crate) open spec fn private_legacy_compact_plane(
    width: u16,
    height: u16,
    words: Seq<u64>,
) -> Tier1RawPlane {
    Tier1RawPlane {
        width,
        height,
        coefficients: words.map_values(|word: u64| compact_coefficient(word)),
    }
}

pub(crate) open spec fn private_legacy_block_initial(b: PrivateLegacyBlockSpec) -> Tier1DecoderState {
    Tier1DecoderState {
        plane: private_legacy_empty_plane(b.width, b.height),
        private_plan: false,
        orientation: b.orientation,
        style: b.style,
        maximum_passes: (b.significant_bitplanes as int * 3 - 2) as u32,
        next_pass: 0,
        bitplane: (b.significant_bitplanes - 1) as u16,
        zero_bitplanes: None,
        bitplane_state: None,
        mq_context_state: None,
        reset_contexts_before_mq: false,
        decoded_segments: 0,
        decoded_bytes: 0,
        legacy_segment: None,
        legacy_decode_work: 0,
        ht_cleanup_plane: None,
        ht_refinement_data: Seq::empty(),
        ht_refinement_passes: 0,
        ht_decoded_bitplanes: 0,
        ht_current_set_has_cleanup: false,
        ht_sets_seen: 0,
        allow_multiple_ht_sets: b.allow_multiple_ht_sets,
        ht_magnitude_bound: b.ht_magnitude_bound,
    }
}

pub(crate) open spec fn private_legacy_block_zero_state(
    b: PrivateLegacyBlockSpec,
    zero_bitplanes: u16,
) -> Tier1DecoderState {
    let eff = (b.significant_bitplanes - zero_bitplanes) as u16;
    Tier1DecoderState {
        bitplane: (eff - 1) as u16,
        maximum_passes: (3 * (eff as nat) - 2) as u32,
        zero_bitplanes: Some(zero_bitplanes),
        ..private_legacy_block_initial(b)
    }
}

pub(crate) open spec fn private_legacy_block_valid(
    b: PrivateLegacyBlockSpec,
    pass_limit: u32,
    byte_limit: u64,
    input_limit: u64,
    work_limit: u64,
) -> bool {
    b.width > 0
        && b.height > 0
        && (b.width as nat) * (b.height as nat) <= 4096
        && b.significant_bitplanes > 0
        && b.significant_bitplanes <= 31
        && b.significant_bitplanes <= crate::tier1::MAX_TIER1_BITPLANES
        && b.ht_magnitude_bound > 0
        && b.ht_magnitude_bound <= crate::tier1::tier1_max_ht_magnitude_bits()
        && private_legacy_style_ok(b.style)
        && match b.contribution {
            None => true,
            Some((c, body)) => {
                !c.high_throughput
                    && c.first_inclusion
                    && c.new_passes > 0
                    && c.segment_count == 1
                    && c.segment_passes.len() >= 1
                    && c.segment_lengths.len() >= 1
                    && c.segment_passes[0] == c.new_passes
                    && c.segment_lengths[0] == c.data_length
                    && body.len() == c.data_length as nat
                    && body.len() > 0
                    && body.len() <= u32::MAX
                    && c.zero_bitplanes < b.significant_bitplanes
                    && (c.new_passes as nat) <= 3 * ((b.significant_bitplanes - c.zero_bitplanes) as nat) - 2
                    && (c.new_passes as u32) <= pass_limit
                    && (body.len() as u64) <= byte_limit
                    && (body.len() as u64) <= input_limit
                    && ((b.width as nat) * (b.height as nat)) * (c.new_passes as nat) + body.len() <= work_limit as nat
            }
        }
}

pub(crate) open spec fn private_legacy_block_segment_ok(
    b: PrivateLegacyBlockSpec,
    pass_limit: u32,
    byte_limit: u64,
    input_limit: u64,
    work_limit: u64,
) -> bool {
    match b.contribution {
        None => true,
        Some((c, body)) => part1_legacy_segment(
            private_legacy_block_zero_state(b, c.zero_bitplanes),
            body,
            c.new_passes as u32,
            pass_limit,
            byte_limit,
            input_limit,
            work_limit,
        ).0.is_ok(),
    }
}

pub(crate) open spec fn private_legacy_block_logical(
    b: PrivateLegacyBlockSpec,
    pass_limit: u32,
    byte_limit: u64,
    input_limit: u64,
    work_limit: u64,
) -> Tier1DecoderState {
    match b.contribution {
        None => private_legacy_block_initial(b),
        Some((c, body)) => part1_legacy_code_block_transaction(
            private_legacy_block_initial(b),
            c,
            body,
            pass_limit,
            byte_limit,
            input_limit,
            work_limit,
        ).1,
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn private_legacy_block_initial_matches_configured(b: PrivateLegacyBlockSpec)
    requires
        b.width > 0 && b.height > 0 && (b.width as nat) * (b.height as nat) <= 4096,
        b.significant_bitplanes > 0
            && b.significant_bitplanes <= 31
            && b.significant_bitplanes <= crate::tier1::MAX_TIER1_BITPLANES,
        b.ht_magnitude_bound > 0 && b.ht_magnitude_bound <= crate::tier1::tier1_max_ht_magnitude_bits(),
        private_legacy_style_ok(b.style),
    ensures
        part2_configured_checkpoint(
            b.width,
            b.height,
            b.significant_bitplanes,
            b.orientation,
            b.style,
            b.allow_multiple_ht_sets,
            b.ht_magnitude_bound,
            true,
        ) == Ok::<Tier1DecoderState, crate::DecodeError>(private_legacy_block_initial(b)),
{
    assert(!ht_block_coding_enabled(b.style.block_coding));
    assert(tier1_empty_plane(b.width, b.height) == Ok::<Tier1RawPlane, crate::DecodeError>(private_legacy_empty_plane(b.width, b.height))) by {
        assert(tier1_empty_plane(b.width, b.height).get_Ok_0().coefficients
            =~= private_legacy_empty_plane(b.width, b.height).coefficients);
    };
    let init = part2_tier1_initial_decoder(b.width, b.height, b.significant_bitplanes, b.orientation, b.style);
    assert(init.is_ok());
    let cfg = part2_tier1_configured_decoder(
        b.width, b.height, b.significant_bitplanes, b.orientation, b.style,
        b.allow_multiple_ht_sets, b.ht_magnitude_bound,
    );
    assert(cfg.is_ok());
    assert(part2_with_ht_checkpoint(cfg, true).get_Ok_0() == private_legacy_block_initial(b));
}

#[verifier::spinoff_prover]
pub(crate) proof fn private_legacy_block_single_contribution(
    b: PrivateLegacyBlockSpec,
    pass_limit: u32,
    byte_limit: u64,
    input_limit: u64,
    work_limit: u64,
)
    requires
        b.contribution.is_some(),
        private_legacy_block_valid(b, pass_limit, byte_limit, input_limit, work_limit),
        private_legacy_block_segment_ok(b, pass_limit, byte_limit, input_limit, work_limit),
    ensures
        ({
            let (c, body) = b.contribution.unwrap();
            let init = private_legacy_block_initial(b);
            let tx = part1_legacy_code_block_transaction(
                init, c, body, pass_limit, byte_limit, input_limit, work_limit,
            );
            let seg = part1_legacy_segment(
                private_legacy_block_zero_state(b, c.zero_bitplanes),
                body,
                c.new_passes as u32,
                pass_limit,
                byte_limit,
                input_limit,
                work_limit,
            );
            tx.0 == Ok::<crate::packet::CodeBlockBodyDecode, crate::DecodeError>(
                crate::packet::CodeBlockBodyDecode {
                    segments: 1,
                    passes: c.new_passes as u32,
                    bytes: c.data_length,
                },
            ) && tx.1.plane == seg.1.plane
        }),
{
    let (c, body) = b.contribution.unwrap();
    let init = private_legacy_block_initial(b);
    let init_z = private_legacy_block_zero_state(b, c.zero_bitplanes);
    let p = c.new_passes as u32;
    let count = (b.width as nat) * (b.height as nat);
    let work = (count * (p as nat) + body.len()) as u64;

    reveal(part1_legacy_code_block_staged);
    reveal(part1_legacy_code_block_body);
    reveal(part1_legacy_contribution);
    reveal(part1_legacy_contribution_admission);
    reveal(part1_legacy_contribution_work);
    reveal(part1_legacy_replay);
    reveal(part1_legacy_replay_commit);

    assert(part1_code_block_body_prepare(init, c, body) == (Ok::<(), crate::DecodeError>(()), init_z)) by {
        assert((((b.significant_bitplanes - 1) - c.zero_bitplanes) as nat) * 3 + 1
            == 3 * ((b.significant_bitplanes - c.zero_bitplanes) as nat) - 2);
    }
    assert(body.subrange(0, body.len() as int) =~= body);
    assert(part1_legacy_contribution_work(count, p, body.len() as u64, 0, work_limit) == Ok::<u64, crate::DecodeError>(work));
    let s1 = Tier1DecoderState { legacy_decode_work: work, ..init_z };
    private_legacy_segment_work_indep(init_z, work, body, p, pass_limit, byte_limit, input_limit, work_limit);
    let seg0 = part1_legacy_segment(init_z, body, p, pass_limit, byte_limit, input_limit, work_limit);
    let seg1 = part1_legacy_segment(s1, body, p, pass_limit, byte_limit, input_limit, work_limit);
    assert(seg1.0 == seg0.0 && seg1.1.plane == seg0.1.plane);
    assert(seg1.0.is_ok());

    if p == init_z.maximum_passes || part1_legacy_plan(init_z.style, (p - 1) as u32).terminates_segment {
        assert(part1_legacy_contribution(init_z, body, c.new_passes, pass_limit, byte_limit, input_limit, work_limit)
            == (Ok::<(), crate::DecodeError>(()), seg1.1));
    } else {
        let snap = part1_legacy_snapshot(s1);
        let seg_frame = part1_legacy_append(snap, body, p);
        assert(seg_frame.input =~= body);
        assert(part1_legacy_restore(s1, seg_frame) == s1);
        // Prove seg1.1.next_pass == p > 0 so part1_legacy_replay_commit returns Ok!
        assert(seg1.1.next_pass > 0) by {
            reveal(part1_legacy_segment);
            reveal(part1_legacy_segment_admission);
            reveal(part1_legacy_segment_account);
            private_legacy_segment_next_pass(s1, body, p, pass_limit, byte_limit, input_limit, work_limit);
        }
        assert(part1_legacy_replay(s1, body, p, pass_limit, byte_limit, input_limit, work_limit).0 == Ok::<(), crate::DecodeError>(()));
        assert(part1_legacy_replay(s1, body, p, pass_limit, byte_limit, input_limit, work_limit).1.plane == seg1.1.plane);
    }
    let run0 = Part1LegacyPacketProgress { decoder: init_z, segment_index: 0, offset: 0, decoded_passes: 0 };
    reveal(part1_legacy_code_block_segment);
    reveal_with_fuel(part1_legacy_code_block_run, 2);
    let step = part1_legacy_code_block_segment(run0, c, body, pass_limit, byte_limit, input_limit, work_limit);
    assert(step.0 == Ok::<(), crate::DecodeError>(()));
    assert(step.1.offset == body.len() && step.1.decoded_passes == p);
}

#[verifier::spinoff_prover]
proof fn private_legacy_decode_pass_preserves_next_pass(
    s: Tier1DecoderState,
    symbols: Part1LegacySymbols,
    kind: crate::tier1::Tier1PassKind,
)
    ensures
        part1_legacy_decode_pass(s, symbols, kind).1.next_pass == s.next_pass,
{
    reveal(part1_legacy_decode_pass);
}

#[verifier::spinoff_prover]
proof fn private_legacy_segment_run_next_pass(
    s: Part1LegacySegmentRun,
    remaining: nat,
)
    requires
        part1_legacy_segment_run(s, remaining).0.is_ok(),
        s.decoder.next_pass as nat + remaining <= u32::MAX,
    ensures
        part1_legacy_segment_run(s, remaining).1.decoder.next_pass as nat == s.decoder.next_pass as nat + remaining,
    decreases remaining,
{
    if remaining > 0 {
        reveal(part1_legacy_segment_step);
        let plan = part1_legacy_plan(s.decoder.style, s.decoder.next_pass);
        private_legacy_decode_pass_preserves_next_pass(s.decoder, s.symbols, plan.kind);
        let step = part1_legacy_segment_step(s);
        assert(step.0.is_ok());
        assert(step.1.decoder.next_pass as nat == s.decoder.next_pass as nat + 1);
        private_legacy_segment_run_next_pass(step.1, (remaining - 1) as nat);
    }
}

#[verifier::spinoff_prover]
proof fn private_legacy_segment_next_pass(
    s: Tier1DecoderState,
    input: Seq<u8>,
    count: u32,
    pass_limit: u32,
    byte_limit: u64,
    input_limit: u64,
    work_limit: u64,
)
    requires
        count > 0,
        s.next_pass == 0,
        part1_legacy_segment(s, input, count, pass_limit, byte_limit, input_limit, work_limit).0.is_ok(),
    ensures
        part1_legacy_segment(s, input, count, pass_limit, byte_limit, input_limit, work_limit).1.next_pass == count,
{
    reveal(part1_legacy_segment);
    reveal(part1_legacy_segment_admission);
    reveal(part1_legacy_segment_account);
    if part1_legacy_plan(s.style, s.next_pass).coding_mode is Mq {
        let mq = part1_mq_initial(input, input_limit, work_limit).get_Ok_0();
        let ready = part1_legacy_segment_setup(s, mq);
        private_legacy_segment_run_next_pass(
            Part1LegacySegmentRun {
                decoder: ready.0,
                symbols: Part1LegacySymbols::Mq(ready.1),
                statistics: tier1_statistics_zero(),
            },
            count as nat,
        );
    } else {
        let raw = part1_raw_reader_initial(input, input_limit, work_limit).get_Ok_0();
        private_legacy_segment_run_next_pass(
            Part1LegacySegmentRun {
                decoder: s,
                symbols: Part1LegacySymbols::Raw(raw),
                statistics: tier1_statistics_zero(),
            },
            count as nat,
        );
    }
}

}
