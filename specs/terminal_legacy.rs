//! Final-image legacy execution and the private packet retirement boundary.
use super::*;
verus! {
// Unlike the private no-copy predecessor, a failed staging operation
// here continues to have an exact frame. The private owner is dropped
// only at tile finalization, not while supplying child tape witnesses.
pub(crate) open spec fn terminal_exact_matches<T, S>(actual:(Result<T,crate::DecodeError>,S), model:(Result<T,crate::DecodeError>,S))->bool {
    actual==model
}
pub(crate) open spec fn terminal_exact_observed<T>(actual:T, model:spec_fn(T)->bool)->bool {
    model(actual)
}
pub(crate) proof fn terminal_exact_witness<T>(actual:T, model:spec_fn(T)->bool)->(effect:T)
    requires terminal_exact_observed(actual,model),
    ensures effect==actual, model(effect),
{actual}
pub(crate) proof fn terminal_exact_publish<T>(actual:T, effect:T, model:spec_fn(T)->bool)
    requires actual==effect, model(effect),
    ensures terminal_exact_observed(actual,model),
{}


/// Rows permanently closed to calls to the precinct decoder. Omitted
/// coordinates and duplicates do not execute a precinct decoder.
pub(crate) open spec fn terminal_precinct_row(seen: Seq<bool>, layers: nat, index: nat) -> bool {
    let start = index * layers;
    0 < layers && start + layers <= seen.len()
        && forall|slot: int| start <= slot < start + layers ==> #[trigger] seen[slot]
}

pub(crate) open spec fn terminal_precinct_last_slot(
    seen: Seq<bool>, layers: nat, index: nat, slot: usize, layer: nat,
) -> bool {
    let start = index * layers;
    0 < layers && layer + 1 == layers && slot as nat == start + layer
        && start + layers <= seen.len() <= usize::MAX && !seen[slot as int]
        && forall|other: int| start <= other < start + layers && other != slot
            ==> #[trigger] seen[other]
}

pub(crate) open spec fn terminal_seen_extends(before: Seq<bool>, after: Seq<bool>) -> bool {
    before.len() == after.len()
        && forall|i: int| 0 <= i < before.len() && #[trigger] before[i] ==> #[trigger] after[i]
}

pub(crate) proof fn terminal_precinct_missing(
    seen: Seq<bool>, layers: nat, index: nat, slot: usize, layer: nat, missing: int,
)
    requires index * layers <= missing < index * layers + layers,
        missing != slot, 0 <= missing < seen.len(), !seen[missing],
    ensures !terminal_precinct_last_slot(seen,layers,index,slot,layer),
{
    if terminal_precinct_last_slot(seen,layers,index,slot,layer) {
        assert(seen[missing]);
    }
}

pub(crate) proof fn terminal_seen_mark(before: Seq<bool>, slot: usize)
    requires slot < before.len(),
    ensures terminal_seen_extends(before, before.update(slot as int, true)),
{
    assert forall|i: int| 0 <= i < before.len() && #[trigger] before[i]
        implies #[trigger] before.update(slot as int, true)[i] by {
        if i != slot { assert(before.update(slot as int, true)[i] == before[i]); }
    };
}

pub(crate) proof fn terminal_seen_close(
    before: Seq<bool>, layers: nat, index: nat, slot: usize, layer: nat,
)
    requires terminal_precinct_last_slot(before, layers, index, slot, layer),
    ensures terminal_precinct_row(before.update(slot as int, true), layers, index),
{
    let start = index * layers;
    assert forall|i: int| start <= i < start + layers
        implies #[trigger] before.update(slot as int, true)[i] by {
        if i != slot { assert(before[i]); }
    };
}

pub(crate) proof fn terminal_seen_row_monotone(before: Seq<bool>, after: Seq<bool>, layers: nat, index: nat)
    requires terminal_seen_extends(before, after), terminal_precinct_row(before, layers, index),
    ensures terminal_precinct_row(after, layers, index),
{
    let start = index * layers;
    assert forall|i: int| start <= i < start + layers implies #[trigger] after[i] by {
        assert(before[i]);
    };
}

pub(crate) proof fn terminal_seen_row_no_revisit(
    seen: Seq<bool>, layers: nat, index: nat, slot: nat, layer: nat,
)
    requires terminal_precinct_row(seen, layers, index),
        layer < layers,
        slot == index * layers + layer,
    ensures slot < seen.len() && seen[slot as int],
{
    assert(index * layers <= slot < index * layers + layers);
}

pub(crate) open spec fn terminal_decoder_live(state: Tier1DecoderState) -> Tier1DecoderState {
    Tier1DecoderState { legacy_segment: None, ..state }
}

pub(crate) open spec fn terminal_decoder_related(actual: Tier1DecoderState, baseline: Tier1DecoderState) -> bool {
    actual == baseline || actual == terminal_decoder_live(baseline)
}

pub(crate) open spec fn terminal_precinct_live(state: Part1PacketPrecinctState) -> Part1PacketPrecinctState {
    Part1PacketPrecinctState { decoders: state.decoders.map_values(|decoder: Tier1DecoderState| terminal_decoder_live(decoder)), ..state }
}

pub(crate) open spec fn terminal_precinct_related(
    actual: Part1PacketPrecinctState, baseline: Part1PacketPrecinctState,
) -> bool {
    actual.decoders.len() == baseline.decoders.len()
        && terminal_precinct_live(actual) == terminal_precinct_live(baseline)
        && forall|i: int| 0 <= i < actual.decoders.len()
            ==> terminal_decoder_related(#[trigger] actual.decoders[i], #[trigger] baseline.decoders[i])
}

pub(crate) open spec fn terminal_tile_related(
    layers: nat, actual: Part1TilePacketExecution, baseline: Part1TilePacketExecution,
) -> bool {
    actual.progress == baseline.progress && actual.precincts.len() == baseline.precincts.len()
        && forall|i: int| 0 <= i < actual.precincts.len() ==> {
            let a = #[trigger] actual.precincts[i];
            let b = #[trigger] baseline.precincts[i];
            if terminal_precinct_row(actual.progress.seen, layers, i as nat) {
                terminal_precinct_related(a, b)
            } else { a == b }
        }
}

pub(crate) proof fn terminal_tile_active_equal(
    layers: nat, actual: Part1TilePacketExecution, baseline: Part1TilePacketExecution,
    index: usize, slot: usize, layer: nat,
)
    requires terminal_tile_related(layers, actual, baseline),
        index < actual.precincts.len(), slot < actual.progress.seen.len(), !actual.progress.seen[slot as int],
        layer < layers, slot as nat == index as nat * layers + layer,
    ensures actual.precincts[index as int] == baseline.precincts[index as int],
{
    if terminal_precinct_row(actual.progress.seen, layers, index as nat) {
        terminal_seen_row_no_revisit(actual.progress.seen, layers, index as nat, slot as nat, layer);
    }
}

pub(crate) open spec fn terminal_legacy_selected(
    admitted: (Result<(u32, u32, u32), crate::DecodeError>, Tier1DecoderState),
) -> bool {
    match admitted.0 {
        Err(_) => false,
        Ok((_, next, last)) => admitted.1.legacy_segment.is_none()
            && next != admitted.1.maximum_passes
            && !part1_legacy_plan(admitted.1.style, last).terminates_segment,
    }
}

pub(crate) open spec fn terminal_legacy_finish(decoded: HtDecoderResult) -> Part2LegacyResult {
    match decoded.0 {
        Err(error) => (Err(error), decoded.1),
        Ok(_) if decoded.1.next_pass == 0 => (
            Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), decoded.1,
        ),
        Ok(_) => (Ok(()), terminal_decoder_live(decoded.1)),
    }
}

pub(crate) open spec fn terminal_legacy_segment_run(
    before: Tier1DecoderState, input: Seq<u8>, count: u32, caps: Part2LegacyCaps,
    calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part2LegacyResult> {
    part2_tier1_storage_bind(part2_legacy_segment_run(before, input, count, caps, calls),
        |decoded: HtDecoderResult, rest| Some((Ok(terminal_legacy_finish(decoded)), rest)))
}

pub(crate) open spec fn terminal_legacy_contribution_run(
    before: Tier1DecoderState, input: Seq<u8>, passes: u8, caps: Part2LegacyCaps,
    terminal: bool, calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part2LegacyResult> {
    let admitted = part1_legacy_contribution_admission(before, input, passes, caps.bytes, caps.work);
    if terminal && terminal_legacy_selected(admitted) {
        terminal_legacy_segment_run(admitted.1, input, (admitted.0->Ok_0).0, caps, calls)
    } else { part2_legacy_contribution_run(before, input, passes, caps, calls) }
}

pub(crate) open spec fn terminal_legacy_contribution_result(
    before: Tier1DecoderState, input: Seq<u8>, passes: u8, caps: Part2LegacyCaps,
    terminal: bool, result: Part2LegacyResult,
) -> bool {
    part2_tier1_storage_framed(
        |calls| terminal_legacy_contribution_run(before, input, passes, caps, terminal, calls),
        Ok(result),
    )
}

pub(crate) open spec fn terminal_legacy_normal(
    before: Tier1DecoderState, input: Seq<u8>, passes: u8, caps: Part2LegacyCaps, terminal: bool,
) -> Part2LegacyResult {
    let ordinary = part1_legacy_contribution(before, input, passes, caps.passes, caps.bytes, caps.input, caps.work);
    let admitted = part1_legacy_contribution_admission(before, input, passes, caps.bytes, caps.work);
    if terminal && terminal_legacy_selected(admitted) && ordinary.0.is_ok() {
        (ordinary.0, terminal_decoder_live(ordinary.1))
    } else { ordinary }
}

pub(crate) proof fn terminal_legacy_segment_observed(
    before: Tier1DecoderState, input: Seq<u8>, count: u32, caps: Part2LegacyCaps,
    decoded: HtDecoderResult,
)
    requires before.legacy_segment.is_none(),
        part2_legacy_segment_result(before, input, count, caps, decoded),
        decoded.0 != Err(crate::DecodeError::AllocationFailed) ==>
            decoded == part1_legacy_segment(before, input, count, caps.passes, caps.bytes, caps.input, caps.work),
    ensures part2_tier1_storage_framed(
        |calls| terminal_legacy_segment_run(before, input, count, caps, calls), Ok(terminal_legacy_finish(decoded))),
        decoded.0 != Err(crate::DecodeError::AllocationFailed) ==> {
            let ordinary = part1_legacy_replay(before, input, count, caps.passes, caps.bytes, caps.input, caps.work);
            terminal_legacy_finish(decoded) == if ordinary.0.is_ok() {
                (ordinary.0, terminal_decoder_live(ordinary.1))
            } else { ordinary }
        },
{
    part2_legacy_segment_frames(before, input, count, caps, decoded);
    part2_tier1_storage_pure(Ok(terminal_legacy_finish(decoded)));
    part2_tier1_storage_bind_frame(
        |calls| part2_legacy_segment_run(before, input, count, caps, calls),
        |value: HtDecoderResult, rest| Some((Ok(terminal_legacy_finish(value)), rest)),
        Ok(decoded), Ok(terminal_legacy_finish(decoded)),
    );
    reveal(part1_legacy_replay);
    reveal(part1_legacy_replay_commit);
    let source = part1_legacy_append(part1_legacy_snapshot(before), input, count);
    assert(source.input =~= input);
    assert(part1_legacy_restore(before, source) == before);
}

pub(crate) proof fn terminal_legacy_selected_observed(
    before: Tier1DecoderState, input: Seq<u8>, passes: u8, caps: Part2LegacyCaps, decoded: HtDecoderResult,
)
    requires
        terminal_legacy_selected(part1_legacy_contribution_admission(before, input, passes, caps.bytes, caps.work)),
        {
            let a = part1_legacy_contribution_admission(before, input, passes, caps.bytes, caps.work);
            part2_legacy_segment_result(a.1, input, (a.0->Ok_0).0, caps, decoded)
                && (decoded.0 != Err(crate::DecodeError::AllocationFailed) ==>
                    decoded == part1_legacy_segment(a.1, input, (a.0->Ok_0).0, caps.passes, caps.bytes, caps.input, caps.work))
        },
    ensures
        terminal_legacy_contribution_result(before, input, passes, caps, true, terminal_legacy_finish(decoded)),
        decoded.0 != Err(crate::DecodeError::AllocationFailed) ==>
            terminal_legacy_finish(decoded) == terminal_legacy_normal(before, input, passes, caps, true),
{
    reveal(part1_legacy_contribution);
    let admitted = part1_legacy_contribution_admission(before, input, passes, caps.bytes, caps.work);
    let count = (admitted.0->Ok_0).0;
    terminal_legacy_segment_observed(admitted.1, input, count, caps, decoded);
    part2_tier1_storage_eta(
        |calls| terminal_legacy_segment_run(admitted.1, input, count, caps, calls),
        Ok(terminal_legacy_finish(decoded)),
    );
}

pub(crate) proof fn terminal_legacy_ordinary_observed(
    before: Tier1DecoderState, input: Seq<u8>, passes: u8, caps: Part2LegacyCaps,
    terminal: bool, result: Part2LegacyResult,
)
    requires !terminal || !terminal_legacy_selected(part1_legacy_contribution_admission(before, input, passes, caps.bytes, caps.work)),
        part2_legacy_contribution_result(before, input, passes, caps, result),
    ensures terminal_legacy_contribution_result(before, input, passes, caps, terminal, result),
{
    part2_legacy_contribution_frames(before, input, passes, caps, result);
}

pub(crate) proof fn terminal_legacy_normal_observed(
    before: Tier1DecoderState, input: Seq<u8>, passes: u8, caps: Part2LegacyCaps,
)
    ensures terminal_legacy_contribution_result(before, input, passes, caps, true,
        terminal_legacy_normal(before, input, passes, caps, true)),
{
    let a = part1_legacy_contribution_admission(before, input, passes, caps.bytes, caps.work);
    if terminal_legacy_selected(a) {
        let v = part1_legacy_segment(a.1, input, (a.0->Ok_0).0, caps.passes, caps.bytes, caps.input, caps.work);
        part2_legacy_segment_normal(a.1, input, (a.0->Ok_0).0, caps);
        terminal_legacy_selected_observed(before, input, passes, caps, v);
        if v.0 == Err(crate::DecodeError::AllocationFailed) {
            reveal(part1_legacy_contribution);
            reveal(part1_legacy_replay);
            let source = part1_legacy_append(part1_legacy_snapshot(a.1), input, (a.0->Ok_0).0);
            assert(source.input =~= input);
            assert(part1_legacy_restore(a.1, source) == a.1);
        }
    } else {
        part2_legacy_contribution_normal(before, input, passes, caps);
        terminal_legacy_ordinary_observed(before, input, passes, caps, true,
            part1_legacy_contribution(before, input, passes, caps.passes, caps.bytes, caps.input, caps.work));
    }
}

pub(crate) open spec fn terminal_packet_segment_run(
    before: Part1LegacyPacketProgress, header: Part1CodeBlockContribution, body: Seq<u8>,
    caps: Part2LegacyCaps, calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part1LegacyPacketEffect> {
    match part2_legacy_packet_admit(before, header, body) {
        Err(error) => Some((Ok((Err(error), before)), calls)),
        Ok((segment, end)) =>
            part2_tier1_storage_bind(
                terminal_legacy_contribution_run(
                    before.decoder, body.subrange(before.offset as int, end as int), segment.passes, caps, true, calls,
                ),
                |decoded: Part2LegacyResult, rest|
                    Some((Ok(part2_legacy_packet_after_decode(before, segment, end, decoded)), rest)),
            ),
    }
}

pub(crate) open spec fn terminal_packet_segment_normal(
    before: Part1LegacyPacketProgress, header: Part1CodeBlockContribution, body: Seq<u8>,
    caps: Part2LegacyCaps,
) -> Part1LegacyPacketEffect {
    match part2_legacy_packet_admit(before, header, body) {
        Err(error) => (Err(error), before),
        Ok((segment, end)) =>
            part2_legacy_packet_after_decode(
                before, segment, end,
                terminal_legacy_normal(before.decoder, body.subrange(before.offset as int, end as int), segment.passes, caps, true),
            ),
    }
}

pub(crate) proof fn terminal_packet_segment_observed(
    before: Part1LegacyPacketProgress, header: Part1CodeBlockContribution, body: Seq<u8>,
    caps: Part2LegacyCaps, segment: crate::packet::CodeBlockSegmentContribution, end: usize, decoded: Part2LegacyResult,
)
    requires part2_legacy_packet_admit(before, header, body) == Ok((segment, end)),
        terminal_legacy_contribution_result(
            before.decoder, body.subrange(before.offset as int, end as int), segment.passes, caps, true, decoded),
    ensures part2_tier1_storage_framed(
        |calls| terminal_packet_segment_run(before, header, body, caps, calls),
        Ok(part2_legacy_packet_after_decode(before, segment, end, decoded)),
    ),
{
    let input = body.subrange(before.offset as int, end as int);
    let result = part2_legacy_packet_after_decode(before, segment, end, decoded);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(
        |calls| terminal_legacy_contribution_run(before.decoder, input, segment.passes, caps, true, calls),
        |value: Part2LegacyResult, rest|
            Some((Ok(part2_legacy_packet_after_decode(before, segment, end, value)), rest)),
        Ok(decoded), Ok(result),
    );
}

pub(crate) proof fn terminal_packet_segment_equivalence(
    before: Part1LegacyPacketProgress, header: Part1CodeBlockContribution, body: Seq<u8>,
    caps: Part2LegacyCaps,
)
    ensures {
        let a = terminal_packet_segment_normal(before, header, body, caps);
        let b = part1_legacy_code_block_segment(before, header, body, caps.passes, caps.bytes, caps.input, caps.work);
        a.0 == b.0 && a.1 == (Part1LegacyPacketProgress { decoder: a.1.decoder, ..b.1 })
            && terminal_decoder_related(a.1.decoder, b.1.decoder)
    },
{
    terminal_packet_segment_ordinary(before, header, body, caps);
    if let Ok((segment, end)) = part2_legacy_packet_admit(before, header, body) {
        let input = body.subrange(before.offset as int, end as int);
        let original = part1_legacy_contribution(before.decoder,input,segment.passes,caps.passes,caps.bytes,caps.input,caps.work);
        let retired = terminal_legacy_normal(before.decoder,input,segment.passes,caps,true);
        assert(original.0 == retired.0 && terminal_decoder_related(retired.1, original.1));
    }
}

pub(crate) proof fn terminal_packet_segment_ordinary(
    before: Part1LegacyPacketProgress, header: Part1CodeBlockContribution, body: Seq<u8>, caps: Part2LegacyCaps,
)
    ensures part1_legacy_code_block_segment(before,header,body,caps.passes,caps.bytes,caps.input,caps.work)
        == match part2_legacy_packet_admit(before,header,body) {
            Err(error) => (Err(error),before),
            Ok((segment,end)) => part2_legacy_packet_after_decode(before,segment,end,
                part1_legacy_contribution(before.decoder,body.subrange(before.offset as int,end as int),segment.passes,
                    caps.passes,caps.bytes,caps.input,caps.work)),
        },
{
    reveal(part1_legacy_code_block_segment);
}

pub(crate) open spec fn terminal_packet_single_progress(before: Tier1DecoderState) -> Part1LegacyPacketProgress {
    Part1LegacyPacketProgress { decoder: before, segment_index: 0, offset: 0, decoded_passes: 0 }
}

pub(crate) open spec fn terminal_packet_single_body_selected(
    header: Part1CodeBlockContribution, terminal: bool,
) -> bool {
    terminal && !header.high_throughput && header.segment_count == 1
}

pub(crate) open spec fn terminal_packet_single_body_run(
    before: Tier1DecoderState, header: Part1CodeBlockContribution, body: Seq<u8>, caps: Part2LegacyCaps,
    calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<HtCodeBlockBodyResult> {
    let prepared = part1_code_block_body_prepare(before, header, body);
    match prepared.0 {
        Err(error) => Some((Ok((Err(error), prepared.1)), calls)),
        Ok(()) => part2_tier1_storage_bind(
            terminal_packet_segment_run(terminal_packet_single_progress(prepared.1), header, body, caps, calls),
            |effect: Part1LegacyPacketEffect, rest| Some((Ok(part1_legacy_code_block_finish(effect, header, body)), rest)),
        ),
    }
}

pub(crate) open spec fn terminal_packet_single_body_normal(
    before: Tier1DecoderState, header: Part1CodeBlockContribution, body: Seq<u8>, caps: Part2LegacyCaps,
) -> HtCodeBlockBodyResult {
    let prepared = part1_code_block_body_prepare(before, header, body);
    match prepared.0 {
        Err(error) => (Err(error), prepared.1),
        Ok(()) => part1_legacy_code_block_finish(
            terminal_packet_segment_normal(terminal_packet_single_progress(prepared.1), header, body, caps), header, body,
        ),
    }
}

pub(crate) proof fn terminal_packet_single_body_equivalence(
    before: Tier1DecoderState, header: Part1CodeBlockContribution, body: Seq<u8>, caps: Part2LegacyCaps,
)
    requires !header.high_throughput, header.segment_count == 1,
    ensures {
        let a = terminal_packet_single_body_normal(before, header, body, caps);
        let b = part1_code_block_body_staged(before, header, body, caps.passes, caps.bytes, caps.input, caps.work);
        a.0 == b.0 && terminal_decoder_related(a.1, b.1)
    },
{
    reveal(part1_legacy_code_block_body);
    reveal_with_fuel(part1_legacy_code_block_run, 2);
    let prepared = part1_code_block_body_prepare(before, header, body);
    if prepared.0.is_ok() {
        let start = terminal_packet_single_progress(prepared.1);
        terminal_packet_segment_equivalence(start, header, body, caps);
        let a = terminal_packet_segment_normal(start, header, body, caps);
        let b = part1_legacy_code_block_segment(start,header,body,caps.passes,caps.bytes,caps.input,caps.work);
        assert(part1_legacy_code_block_run(start,header,body,1,caps.passes,caps.bytes,caps.input,caps.work) == b);
        let final_a = part1_legacy_code_block_finish(a,header,body);
        let final_b = part1_legacy_code_block_finish(b,header,body);
        assert(final_a.0 == final_b.0);
    }
}

pub(crate) proof fn terminal_packet_single_body_observed(
    before: Tier1DecoderState, header: Part1CodeBlockContribution, body: Seq<u8>, caps: Part2LegacyCaps,
    effect: Part1LegacyPacketEffect,
)
    requires part1_code_block_body_prepare(before, header, body).0.is_ok(),
        part2_tier1_storage_framed(
            |calls| terminal_packet_segment_run(terminal_packet_single_progress(
                part1_code_block_body_prepare(before, header, body).1), header, body, caps, calls), Ok(effect)),
    ensures part2_tier1_storage_framed(
        |calls| terminal_packet_single_body_run(before, header, body, caps, calls),
        Ok(part1_legacy_code_block_finish(effect, header, body)),
    ),
{
    let ready = terminal_packet_single_progress(part1_code_block_body_prepare(before, header, body).1);
    let result = part1_legacy_code_block_finish(effect, header, body);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(
        |calls| terminal_packet_segment_run(ready, header, body, caps, calls),
        |value: Part1LegacyPacketEffect, rest| Some((Ok(part1_legacy_code_block_finish(value, header, body)), rest)),
        Ok(effect), Ok(result),
    );
}

pub(crate) proof fn terminal_packet_single_body_normal_observed(
    before: Tier1DecoderState, header: Part1CodeBlockContribution, body: Seq<u8>, caps: Part2LegacyCaps,
)
    ensures part2_tier1_storage_framed(
        |calls| terminal_packet_single_body_run(before, header, body, caps, calls),
        Ok(terminal_packet_single_body_normal(before, header, body, caps)),
    ),
{
    let prepared = part1_code_block_body_prepare(before, header, body);
    let result = terminal_packet_single_body_normal(before, header, body, caps);
    if prepared.0.is_ok() {
        let init = terminal_packet_single_progress(prepared.1);
        let step = terminal_packet_segment_normal(init, header, body, caps);
        match part2_legacy_packet_admit(init, header, body) {
            Err(_) => { part2_tier1_storage_pure(Ok(step)); }
            Ok((segment, end)) => {
                let input = body.subrange(init.offset as int, end as int);
                terminal_legacy_normal_observed(init.decoder, input, segment.passes, caps);
                terminal_packet_segment_observed(init, header, body, caps, segment, end,
                    terminal_legacy_normal(init.decoder, input, segment.passes, caps, true));
            }
        }
        terminal_packet_single_body_observed(before, header, body, caps, step);
    } else { part2_tier1_storage_pure(Ok(result)); }
}

pub(crate) open spec fn terminal_stage_publish(before: Tier1DecoderState, decoded: HtCodeBlockBodyResult) -> HtCodeBlockBodyResult {
    if decoded.0.is_err() { (decoded.0,before) } else { decoded }
}

pub(crate) open spec fn terminal_body_after_copy(
    before: Tier1DecoderState, header: Part1CodeBlockContribution, body:Seq<u8>, caps:Part2LegacyCaps,
    copy:Result<Tier1DecoderState,crate::DecodeError>, calls:Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<HtCodeBlockBodyResult> {
    match copy {
        Err(error) => Some((Ok((Err(error),before)),calls)),
        Ok(source) => part2_tier1_storage_bind(terminal_packet_single_body_run(source,header,body,caps,calls),
            |decoded:HtCodeBlockBodyResult,rest|Some((Ok(terminal_stage_publish(before,decoded)),rest))),
    }
}

pub(crate) open spec fn terminal_body_mode_run(
    terminal:bool,before:Tier1DecoderState, header:Part1CodeBlockContribution, body:Seq<u8>,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<HtCodeBlockBodyResult> {
    if terminal_packet_single_body_selected(header,terminal) {
        part2_tier1_storage_resume(part2_ht_duplicate_run(before,crate::tier1::HtRefinementCopyRole::PacketStaging,calls),
            |copy:Result<Tier1DecoderState,crate::DecodeError>,rest|
                terminal_body_after_copy(before,header,body,part2_legacy_caps(pass_limit,byte_limit,input_limit,work),copy,rest))
    } else { part2_plane_body_transaction_run(before,header,body,pass_limit,byte_limit,input_limit,work,calls) }
}

pub(crate) proof fn terminal_body_duplicate_observed(
    before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,
    copy:Result<Tier1DecoderState,crate::DecodeError>,staged:HtCodeBlockBodyResult,
)
    requires terminal_packet_single_body_selected(header,true),
        part2_ht_duplicate_result(before,crate::tier1::HtRefinementCopyRole::PacketStaging,copy),
        match copy { Err(error)=>staged==(Err(error),before), Ok(source)=>part2_tier1_storage_framed(
            |calls|terminal_packet_single_body_run(source,header,body,caps,calls),Ok(staged)) },
    ensures part2_tier1_storage_framed(
        |calls|terminal_body_mode_run(true,before,header,body,caps.passes,caps.bytes,caps.input,caps.work,calls),
        Ok(terminal_stage_publish(before,staged))),
{
    let role=crate::tier1::HtRefinementCopyRole::PacketStaging;
    let result=terminal_stage_publish(before,staged);
    let next=|copy:Result<Tier1DecoderState,crate::DecodeError>,rest|terminal_body_after_copy(before,header,body,caps,copy,rest);
    part2_tier1_storage_pure(Ok(result));
    if let Ok(source)=copy {
        part2_tier1_storage_bind_frame(|calls|terminal_packet_single_body_run(source,header,body,caps,calls),
            |decoded:HtCodeBlockBodyResult,rest|Some((Ok(terminal_stage_publish(before,decoded)),rest)),Ok(staged),Ok(result));
    }
    part2_ht_duplicate_frames(before,role,copy);
    part2_tier1_resume_frame(|calls|part2_ht_duplicate_run(before,role,calls),next,copy,Ok(result));
}

pub(crate) open spec fn terminal_body_mode_value(
    terminal:bool,before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,
) -> HtCodeBlockBodyResult {
    if terminal_packet_single_body_selected(header,terminal) {
        terminal_stage_publish(before,terminal_packet_single_body_normal(before,header,body,caps))
    } else { part1_code_block_body_transaction(before,header,body,caps.passes,caps.bytes,caps.input,caps.work) }
}

pub(crate) proof fn terminal_body_mode_value_related(
    terminal:bool,before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,
)
    ensures {
        let a=terminal_body_mode_value(terminal,before,header,body,caps);
        let b=part1_code_block_body_transaction(before,header,body,caps.passes,caps.bytes,caps.input,caps.work);
        a.0==b.0 && terminal_decoder_related(a.1,b.1)
    },
{
    if terminal_packet_single_body_selected(header,terminal) {
        terminal_packet_single_body_equivalence(before,header,body,caps);
    }
}

pub(crate) proof fn terminal_body_mode_normal_observed(
    terminal:bool,before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,
)
    ensures part2_tier1_storage_framed(
        |calls|terminal_body_mode_run(terminal,before,header,body,caps.passes,caps.bytes,caps.input,caps.work,calls),
        Ok(terminal_body_mode_value(terminal,before,header,body,caps))),
{
    if terminal_packet_single_body_selected(header,terminal) {
        terminal_packet_single_body_normal_observed(before,header,body,caps);
        part2_ht_duplicate_normal(before,crate::tier1::HtRefinementCopyRole::PacketStaging);
        terminal_body_duplicate_observed(before,header,body,caps,Ok(before),terminal_packet_single_body_normal(before,header,body,caps));
    } else {
        let result=part1_code_block_body_transaction(before,header,body,caps.passes,caps.bytes,caps.input,caps.work);
        part2_plane_body_transaction_normal(before,header,body,caps.passes,caps.bytes,caps.input,caps.work);
        part2_plane_body_transaction_frames(before,header,body,caps.passes,caps.bytes,caps.input,caps.work,result);
    }
}

pub(crate) open spec fn terminal_body_slot_value(
    terminal: bool, before: Part1PacketBodyExecution, contribution: Part1CodeBlockContribution,
    data: Seq<u8>, error: usize, local: usize, decode: bool, caps: Part2LegacyCaps,
) -> Part1PacketBodyExecutionResult {
    if part2_plane_execute_admit(before, contribution, data, decode) {
        let body = data.subrange(before.offset as int, before.offset as int + contribution.data_length as int);
        part2_plane_execute_finish(before, contribution, local,
            terminal_body_mode_value(terminal, before.decoders[before.index as int], contribution, body, caps))
    } else {
        part1_packet_body_execute_slot_at(before, contribution, data, error, local, decode,
            caps.passes, caps.bytes, caps.input, caps.work)
    }
}

#[verifier::opaque]
pub(crate) open spec fn terminal_body_value(
    terminal: bool, before: Part1PacketBodyExecution,
    contributions: Seq<Option<Part1CodeBlockContribution>>, data: Seq<u8>,
    error: usize, local: usize, decode: bool, caps: Part2LegacyCaps,
) -> Part1PacketBodyExecutionResult
    decreases contributions.len() - before.index as nat,
{
    if !terminal {
        part1_packet_body_execute_at(before, contributions, data, error, local, decode,
            caps.passes, caps.bytes, caps.input, caps.work)
    } else if before.index >= contributions.len() {
        (Ok(()), before)
    } else {
        let step = match contributions[before.index as int] {
            None => (Ok(()), before),
            Some(c) => terminal_body_slot_value(terminal, before, c, data, error, local, decode, caps),
        };
        if step.0.is_err() { step }
        else if before.index == usize::MAX {
            (Err(part1_packet_reader_error(local, crate::MalformedKind::ArithmeticOverflow)), step.1)
        } else {
            terminal_body_value(terminal, Part1PacketBodyExecution { index: (before.index + 1) as usize, ..step.1 },
                contributions, data, error, local, decode, caps)
        }
    }
}

pub(crate) open spec fn terminal_body_slot_run(
    terminal: bool, before: Part1PacketBodyExecution, contribution: Part1CodeBlockContribution,
    data: Seq<u8>, error: usize, local: usize, decode: bool, caps: Part2LegacyCaps,
    calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part1PacketBodyExecutionResult> {
    if part2_plane_execute_admit(before, contribution, data, decode) {
        let body = data.subrange(before.offset as int, before.offset as int + contribution.data_length as int);
        part2_tier1_storage_bind(
            terminal_body_mode_run(terminal, before.decoders[before.index as int], contribution, body,
                caps.passes, caps.bytes, caps.input, caps.work, calls),
            |decoded: HtCodeBlockBodyResult, rest|
                Some((Ok(part2_plane_execute_finish(before, contribution, local, decoded)), rest)),
        )
    } else {
        Some((Ok(part1_packet_body_execute_slot_at(before, contribution, data, error, local, decode,
            caps.passes, caps.bytes, caps.input, caps.work)), calls))
    }
}

#[verifier::opaque]
pub(crate) open spec fn terminal_body_run(
    terminal: bool, before: Part1PacketBodyExecution,
    contributions: Seq<Option<Part1CodeBlockContribution>>, data: Seq<u8>,
    error: usize, local: usize, decode: bool, caps: Part2LegacyCaps, calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part1PacketBodyExecutionResult>
    decreases if before.index < contributions.len() { ((contributions.len() - before.index as nat) * 2 + 1) as nat } else { 0nat },
{
    if !terminal {
        part2_plane_execute_run(before, contributions, data, error, local, decode,
            caps.passes, caps.bytes, caps.input, caps.work, calls)
    } else if before.index >= contributions.len() {
        Some((Ok((Ok(()), before)), calls))
    } else {
        let step = match contributions[before.index as int] {
            None => Some((Ok((Ok(()), before)), calls)),
            Some(c) => terminal_body_slot_run(terminal, before, c, data, error, local, decode, caps, calls),
        };
        part2_tier1_storage_bind(step, |value: Part1PacketBodyExecutionResult, rest|
            terminal_body_next(terminal, value, before.index, contributions, data, error, local, decode, caps, rest))
    }
}

pub(crate) open spec fn terminal_body_next(
    terminal: bool, step: Part1PacketBodyExecutionResult, index: usize,
    contributions: Seq<Option<Part1CodeBlockContribution>>, data: Seq<u8>,
    error: usize, local: usize, decode: bool, caps: Part2LegacyCaps, calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part1PacketBodyExecutionResult>
    decreases if index < contributions.len() { ((contributions.len() - index as nat) * 2) as nat } else { 0nat },
{
    if !terminal {
        part2_plane_execute_next(step, index, contributions, data, error, local, decode,
            caps.passes, caps.bytes, caps.input, caps.work, calls)
    } else if step.1.index != index { None }
    else if step.0.is_err() { Some((Ok(step), calls)) }
    else if index == usize::MAX {
        Some((Ok((Err(part1_packet_reader_error(local, crate::MalformedKind::ArithmeticOverflow)), step.1)), calls))
    } else if index >= contributions.len() { Some((Ok(step), calls)) }
    else {
        terminal_body_run(terminal, Part1PacketBodyExecution { index: (index + 1) as usize, ..step.1 },
            contributions, data, error, local, decode, caps, calls)
    }
}

pub(crate) open spec fn terminal_body_suffix_related(
    actual: Part1PacketBodyExecution, baseline: Part1PacketBodyExecution,
) -> bool {
    actual == (Part1PacketBodyExecution { decoders: actual.decoders, ..baseline })
        && actual.decoders.len() == baseline.decoders.len()
        && forall|i: int| 0 <= i < actual.decoders.len() ==> {
            let a = #[trigger] actual.decoders[i];
            let b = #[trigger] baseline.decoders[i];
            if i < actual.index { terminal_decoder_related(a, b) } else { a == b }
        }
}

pub(crate) open spec fn terminal_body_complete_related(
    actual: Part1PacketBodyExecution, baseline: Part1PacketBodyExecution,
) -> bool {
    actual == (Part1PacketBodyExecution { decoders: actual.decoders, ..baseline })
        && actual.decoders.len() == baseline.decoders.len()
        && forall|i: int| 0 <= i < actual.decoders.len() ==>
            terminal_decoder_related(#[trigger] actual.decoders[i], #[trigger] baseline.decoders[i])
}

pub(crate) proof fn terminal_body_related(
    actual: Part1PacketBodyExecution, baseline: Part1PacketBodyExecution,
    contributions: Seq<Option<Part1CodeBlockContribution>>, data: Seq<u8>, error: usize, local: usize,
    decode: bool, caps: Part2LegacyCaps,
)
    requires terminal_body_suffix_related(actual, baseline),
    ensures {
        let a = terminal_body_value(true,actual, contributions, data, error, local, decode, caps);
        let b = part1_packet_body_execute_at(baseline, contributions, data, error, local, decode,
            caps.passes, caps.bytes, caps.input, caps.work);
        a.0 == b.0 && terminal_body_complete_related(a.1, b.1)
    },
    decreases contributions.len() - actual.index as nat,
{
    reveal(terminal_body_value);
    reveal(part1_packet_body_execute_at);
    reveal(part1_packet_body_execute_slot_at);
    let i = actual.index;
    if i < contributions.len() {
        let (a, b) = match contributions[i as int] {
            None => ((Ok(()), actual), (Ok(()), baseline)),
            Some(c) => {
                if part2_plane_execute_admit(actual, c, data, decode) {
                    let body = data.subrange(actual.offset as int, actual.offset as int + c.data_length as int);
                    terminal_body_mode_value_related(true, actual.decoders[i as int], c, body, caps);
                }
                (
                    terminal_body_slot_value(true,actual, c, data, error, local, decode, caps),
                    part1_packet_body_execute_slot_at(baseline, c, data, error, local, decode,
                        caps.passes, caps.bytes, caps.input, caps.work),
                )
            },
        };
        assert(a.0 == b.0);
        assert(terminal_body_complete_related(a.1, b.1));
        if a.0.is_ok() && i < usize::MAX {
            let a = Part1PacketBodyExecution { index: (i + 1) as usize, ..a.1 };
            let b = Part1PacketBodyExecution { index: (i + 1) as usize, ..b.1 };
            assert(terminal_body_suffix_related(a, b));
            terminal_body_related(a, b, contributions, data, error, local, decode, caps);
        }
    }
}

pub(crate) open spec fn terminal_body_frame(
    before: Part1PacketBodyExecution, contributions: Seq<Option<Part1CodeBlockContribution>>,
    data: Seq<u8>, offsets: (usize, usize), decode: bool, caps: Part2LegacyCaps,
    output: Part1PacketBodyExecutionResult,
) -> bool {
    part2_tier1_storage_framed(
        |calls| terminal_body_run(true,before, contributions, data, offsets.0, offsets.1, decode, caps, calls),
        Ok(output),
    )
}

pub(crate) proof fn terminal_body_slot_pure(
    before: Part1PacketBodyExecution, contribution: Option<Part1CodeBlockContribution>,
    data: Seq<u8>, offsets: (usize, usize), decode: bool, caps: Part2LegacyCaps,
)
    requires contribution.is_none() || !part2_plane_execute_admit(before, contribution.unwrap(), data, decode),
    ensures forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger]
        terminal_body_optional_slot_run(before, contribution, data, offsets, decode, caps, calls)
        == Some((Ok(terminal_body_optional_slot_value(before, contribution, data, offsets, decode, caps)), calls)),
{}

pub(crate) proof fn terminal_body_slot_keeps_index(
    before: Part1PacketBodyExecution, contribution: Option<Part1CodeBlockContribution>,
    data: Seq<u8>, offsets: (usize, usize), caps: Part2LegacyCaps,
    result: Part1PacketBodyExecutionResult,
)
    requires part2_tier1_storage_framed(
        |calls| terminal_body_optional_slot_run(before, contribution, data, offsets, true, caps, calls),
        Ok(result)),
    ensures result.1.index == before.index,
{
    reveal(part1_packet_body_execute_slot_at);
    let child = |calls| terminal_body_optional_slot_run(before, contribution, data, offsets, true, caps, calls);
    let tape = choose|calls| #[trigger] part2_tier1_storage_prefix(child, calls, Ok(result));
    part2_tier1_storage_at(child, tape, Ok(result), Seq::empty());
    assert(tape + Seq::empty() =~= tape);
    if let Some(header) = contribution {
        if part2_plane_execute_admit(before, header, data, true) {
            let body = data.subrange(before.offset as int, before.offset as int + header.data_length as int);
            match terminal_body_mode_run(true, before.decoders[before.index as int], header, body,
                caps.passes, caps.bytes, caps.input, caps.work, tape) {
                Some((Ok(effect), _)) => {
                    assert(result == part2_plane_execute_finish(before, header, offsets.1, effect));
                }
                _ => { assert(false); }
            }
        }
    }
}

pub(crate) open spec fn terminal_body_optional_slot_run(
    before: Part1PacketBodyExecution, contribution: Option<Part1CodeBlockContribution>,
    data: Seq<u8>, offsets: (usize, usize), decode: bool, caps: Part2LegacyCaps,
    calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part1PacketBodyExecutionResult> {
    match contribution {
        None => Some((Ok((Ok(()), before)), calls)),
        Some(c) => terminal_body_slot_run(true,before, c, data, offsets.0, offsets.1, decode, caps, calls),
    }
}

pub(crate) open spec fn terminal_body_optional_slot_value(
    before: Part1PacketBodyExecution, contribution: Option<Part1CodeBlockContribution>,
    data: Seq<u8>, offsets: (usize, usize), decode: bool, caps: Part2LegacyCaps,
) -> Part1PacketBodyExecutionResult {
    match contribution {
        None => (Ok(()), before),
        Some(c) => terminal_body_slot_value(true,before, c, data, offsets.0, offsets.1, decode, caps),
    }
}

pub(crate) proof fn terminal_body_slot_observed(
    before: Part1PacketBodyExecution, contribution: Part1CodeBlockContribution,
    data: Seq<u8>, offsets: (usize, usize), caps: Part2LegacyCaps, decoded: HtCodeBlockBodyResult,
)
    requires part2_plane_execute_admit(before, contribution, data, true),
        part2_tier1_storage_framed(
            |calls| terminal_body_mode_run(true, before.decoders[before.index as int], contribution,
                data.subrange(before.offset as int, before.offset as int + contribution.data_length as int),
                caps.passes, caps.bytes, caps.input, caps.work, calls), Ok(decoded)),
    ensures part2_tier1_storage_framed(
        |calls| terminal_body_optional_slot_run(before, Some(contribution), data, offsets, true, caps, calls),
        Ok(part2_plane_execute_finish(before, contribution, offsets.1, decoded)),
    ),
{
    let body = data.subrange(before.offset as int, before.offset as int + contribution.data_length as int);
    let output = part2_plane_execute_finish(before, contribution, offsets.1, decoded);
    part2_tier1_storage_pure(Ok(output));
    part2_tier1_storage_bind_frame(
        |calls| terminal_body_mode_run(true, before.decoders[before.index as int], contribution,
            body, caps.passes, caps.bytes, caps.input, caps.work, calls),
        |value: HtCodeBlockBodyResult, rest|
            Some((Ok(part2_plane_execute_finish(before, contribution, offsets.1, value)), rest)),
        Ok(decoded), Ok(output),
    );
}

pub(crate) proof fn terminal_body_unfold(
    before: Part1PacketBodyExecution, contributions: Seq<Option<Part1CodeBlockContribution>>,
    data: Seq<u8>, offsets: (usize, usize), decode: bool, caps: Part2LegacyCaps,
)
    ensures forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger]
        terminal_body_run(true,before, contributions, data, offsets.0, offsets.1, decode, caps, calls)
        == if before.index >= contributions.len() { Some((Ok((Ok(()), before)), calls)) }
        else {
            part2_tier1_storage_bind(
                terminal_body_optional_slot_run(before, contributions[before.index as int], data, offsets, decode, caps, calls),
                |effect: Part1PacketBodyExecutionResult, rest|
                    terminal_body_next(true,effect, before.index, contributions, data,
                        offsets.0, offsets.1, decode, caps, rest),
            )
        },
{
    reveal(terminal_body_run);
}

pub(crate) proof fn terminal_body_normal_observed(
    before: Part1PacketBodyExecution, contributions: Seq<Option<Part1CodeBlockContribution>>,
    data: Seq<u8>, offsets: (usize, usize), decode: bool, caps: Part2LegacyCaps,
)
    ensures terminal_body_frame(before, contributions, data, offsets, decode, caps,
        terminal_body_value(true,before, contributions, data, offsets.0, offsets.1, decode, caps)),
    decreases contributions.len() - before.index as nat,
{
    reveal(terminal_body_value);
    let result = terminal_body_value(true,before, contributions, data, offsets.0, offsets.1, decode, caps);
    terminal_body_unfold(before, contributions, data, offsets, decode, caps);
    if before.index >= contributions.len() {
        part2_tier1_storage_pure(Ok(result));
    } else {
        let contribution = contributions[before.index as int];
        let value = terminal_body_optional_slot_value(before, contribution, data, offsets, decode, caps);
        let child = |calls| terminal_body_optional_slot_run(before, contribution, data, offsets, decode, caps, calls);
        let next = |effect: Part1PacketBodyExecutionResult, rest| terminal_body_next(true,effect, before.index,
            contributions, data, offsets.0, offsets.1, decode, caps, rest);
        if contribution.is_none() || !part2_plane_execute_admit(before, contribution.unwrap(), data, decode) {
            terminal_body_slot_pure(before, contribution, data, offsets, decode, caps);
            part2_tier1_storage_pure(Ok(value));
        } else {
            let header = contribution.unwrap();
            let index = before.index as int;
            let body = data.subrange(before.offset as int, before.offset as int + header.data_length as int);
            terminal_body_mode_normal_observed(true, before.decoders[index], header, body, caps);
            terminal_body_slot_observed(before, header, data, offsets, caps,
                terminal_body_mode_value(true, before.decoders[index], header, body, caps));
        }
        terminal_body_slot_index(before, contribution, data, offsets, decode, caps);
        assert(value.1.index == before.index);
        if value.0.is_ok() && before.index < usize::MAX {
            let after = Part1PacketBodyExecution { index: (before.index + 1) as usize, ..value.1 };
            terminal_body_normal_observed(after, contributions, data, offsets, decode, caps);
            let tail = |calls| terminal_body_run(true,after,contributions,data,offsets.0,offsets.1,decode,caps,calls);
            part2_tier1_storage_eta(tail,Ok(result));
            terminal_body_next_success(value,before.index,contributions,data,offsets,decode,caps);
            assert forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger] next(value,calls)==tail(calls) by {
                assert(terminal_body_next(true,value,before.index,contributions,data,offsets.0,offsets.1,decode,caps,calls)
                    == tail(calls));
            };
            assert((|calls: Seq<Part2Tier1StorageEvent>| next(value,calls)) =~= tail);
        } else { part2_tier1_storage_pure(Ok(result)); }
        assert(part2_tier1_storage_framed(|calls| next(value,calls),Ok(result)));
        part2_tier1_storage_bind_frame(child, next, Ok(value), Ok(result));
    }
}

pub(crate) proof fn terminal_body_next_success(
    value: Part1PacketBodyExecutionResult, index: usize,
    contributions: Seq<Option<Part1CodeBlockContribution>>, data: Seq<u8>,
    offsets: (usize,usize), decode: bool, caps: Part2LegacyCaps,
)
    requires value.0.is_ok(), value.1.index == index, index < usize::MAX, index < contributions.len(),
    ensures forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger]
        terminal_body_next(true,value,index,contributions,data,offsets.0,offsets.1,decode,caps,calls)
        == terminal_body_run(true,Part1PacketBodyExecution {index:(index+1) as usize,..value.1},
            contributions,data,offsets.0,offsets.1,decode,caps,calls),
{
    reveal_with_fuel(terminal_body_next, 2);
    reveal_with_fuel(terminal_body_run, 1);
}

pub(crate) proof fn terminal_body_slot_index(
    before: Part1PacketBodyExecution, contribution: Option<Part1CodeBlockContribution>, data: Seq<u8>,
    offsets: (usize,usize), decode: bool, caps: Part2LegacyCaps,
)
    ensures terminal_body_optional_slot_value(before,contribution,data,offsets,decode,caps).1.index == before.index,
{
    reveal(part1_packet_body_execute_slot_at);
}

pub(crate) open spec fn terminal_payload_body_initial(state: Part1PacketPrecinctState, offset: usize) -> Part1PacketBodyExecution {
    Part1PacketBodyExecution { decoders: state.decoders, index: 0, offset, segments: 0, passes: 0 }
}

pub(crate) open spec fn terminal_payload_after_run(
    state: Part1PacketPrecinctState, parameters: Part1PrecinctPayloadParameters,
    data: Seq<u8>, header: Part2PlanePayloadHeader, caps: Part2LegacyCaps, calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part1PrecinctPayloadResult> {
    match part2_plane_payload_admit(parameters, data, header.packet, header.reader, header.contributions, header.sop) {
        Err(error) => Some((Ok((Err(error), state)), calls)),
        Ok(args) => part2_tier1_storage_bind(
            terminal_body_run(true,terminal_payload_body_initial(state, args.1), header.contributions, data,
                parameters.error_offset, 0, parameters.decode_tier1, caps, calls),
            |effect: Part1PacketBodyExecutionResult, rest|
                Some((Ok(part2_plane_payload_finish(state, parameters, header.present, header.count, args, effect)), rest)),
        ),
    }
}

pub(crate) open spec fn terminal_payload_after_value(
    state: Part1PacketPrecinctState, parameters: Part1PrecinctPayloadParameters,
    data: Seq<u8>, header: Part2PlanePayloadHeader, caps: Part2LegacyCaps,
) -> Part1PrecinctPayloadResult {
    match part2_plane_payload_admit(parameters, data, header.packet, header.reader, header.contributions, header.sop) {
        Err(error) => (Err(error), state),
        Ok(args) => part2_plane_payload_finish(state, parameters, header.present, header.count, args,
            terminal_body_value(true,terminal_payload_body_initial(state, args.1), header.contributions,
                data, parameters.error_offset, 0, parameters.decode_tier1, caps)),
    }
}

pub(crate) open spec fn terminal_payload_after_frame(
    state: Part1PacketPrecinctState, parameters: Part1PrecinctPayloadParameters,
    data: Seq<u8>, header: Part2PlanePayloadHeader, caps: Part2LegacyCaps, result: Part1PrecinctPayloadResult,
) -> bool {
    part2_tier1_storage_framed(|calls| terminal_payload_after_run(state, parameters, data, header, caps, calls), Ok(result))
}

pub(crate) open spec fn terminal_payload_mode_after_frame(
    terminal: bool, state: Part1PacketPrecinctState, parameters: Part1PrecinctPayloadParameters,
    data: Seq<u8>, header: Part2PlanePayloadHeader, caps: Part2LegacyCaps, result: Part1PrecinctPayloadResult,
) -> bool {
    if terminal && parameters.decode_tier1 {
        terminal_payload_after_frame(state, parameters, data, header, caps, result)
    } else {
        part2_plane_payload_after_result(state, parameters, data, header.packet, header.reader,
            header.contributions, header.count, header.present, header.sop, caps.passes, caps.bytes, caps.input, caps.work, result)
    }
}

pub(crate) open spec fn terminal_payload_mode_frame(
    terminal: bool, context: Part2PrecinctContributionsContext, caps: Part2LegacyCaps,
    result: Part1PrecinctPayloadResult,
) -> bool {
    if terminal && context.parameters.decode_tier1 {
        part2_tier1_storage_framed(|calls| terminal_payload_run(context, caps, calls), Ok(result))
    } else {
        part2_plane_payload_result(context.state, context.data, context.packed, context.parameters,
            context.header_limit, caps.passes, caps.bytes, caps.input, caps.work, result)
    }
}

pub(crate) proof fn terminal_payload_mode_publish(
    terminal: bool, context: Part2PrecinctContributionsContext, caps: Part2LegacyCaps,
    after: Part1PacketPrecinctState, header: Part2PlanePayloadHeader, actual: Part1PrecinctPayloadResult,
)
    requires caps.work == context.work,
        part2_plane_payload_headers(context.state,context.data,context.packed,context.parameters,
            context.header_limit,context.work)==(Ok(header),after),
        part1_precinct_payload_prefix(context.data,context.packed,context.parameters,
            context.header_limit,context.work).is_ok(),
        part2_precinct_contributions_result(context,Ok(())),
        terminal_exact_observed(actual,
            |effect|terminal_payload_mode_after_frame(terminal,after,context.parameters,context.data,header,caps,effect)),
    ensures terminal_exact_observed(actual,|effect|terminal_payload_mode_frame(terminal,context,caps,effect)),
        !terminal ==> terminal_exact_observed(actual,|effect|part2_plane_payload_result(context.state,context.data,
            context.packed,context.parameters,context.header_limit,caps.passes,caps.bytes,caps.input,caps.work,effect)),
{
    let found = terminal_exact_witness(actual,
        |effect|terminal_payload_mode_after_frame(terminal,after,context.parameters,context.data,header,caps,effect));
    if terminal && context.parameters.decode_tier1 {
        terminal_payload_observed(context,caps,after,header,found);
    } else {
        part2_plane_payload_observed(context.state,context.data,context.packed,context.parameters,context.header_limit,
            caps.passes,caps.bytes,caps.input,caps.work,after,header,found);
        if !terminal {
            terminal_exact_publish(actual,found,|effect|part2_plane_payload_result(context.state,
                context.data,context.packed,context.parameters,context.header_limit,caps.passes,caps.bytes,caps.input,caps.work,effect));
        }
    }
    terminal_exact_publish(actual,found,|effect|terminal_payload_mode_frame(terminal,context,caps,effect));
}

pub(crate) open spec fn terminal_precinct_mode_frame(
    terminal: bool, state: Part1PacketPrecinctState, part: Part2OwnedTilePart, offset: usize,
    packed: Seq<u8>, packed_offset: usize, expected: Option<u32>, sequence: u16, decode: bool,
    blocks: u64, header_limit: u64, caps: Part2LegacyCaps, result: Part1PrecinctPayloadResult,
) -> bool {
    if terminal && decode {
        part2_tier1_storage_framed(|calls| terminal_precinct_run(state, part, offset, packed, packed_offset, expected,
            sequence, decode, blocks, header_limit, caps, calls), Ok(result))
    } else {
        part2_plane_precinct_result(state, part, offset, packed, packed_offset, expected, sequence, decode,
            blocks, header_limit, caps.passes, caps.bytes, caps.input, caps.work, result)
    }
}

pub(crate) proof fn terminal_precinct_ordinary_bridge(
    state: Part1PacketPrecinctState, part: Part2OwnedTilePart, offset: usize,
    packed: Seq<u8>, packed_offset: usize, expected: Option<u32>, sequence: u16, decode: bool,
    blocks: u64, header_limit: u64, caps: Part2LegacyCaps, actual: Part1PrecinctPayloadResult,
)
    requires terminal_exact_observed(actual,|effect:Part1PrecinctPayloadResult|
        part2_plane_precinct_result(state,part,offset,packed,packed_offset,expected,sequence,decode,
            blocks,header_limit,caps.passes,caps.bytes,caps.input,caps.work,effect)),
    ensures terminal_exact_observed(actual,|effect:Part1PrecinctPayloadResult|
        terminal_precinct_mode_frame(false,state,part,offset,packed,packed_offset,expected,sequence,decode,
            blocks,header_limit,caps,effect)),
{
    let ordinary=|effect:Part1PrecinctPayloadResult|
        part2_plane_precinct_result(state,part,offset,packed,packed_offset,expected,sequence,decode,
            blocks,header_limit,caps.passes,caps.bytes,caps.input,caps.work,effect);
    let indexed=|effect:Part1PrecinctPayloadResult|
        terminal_precinct_mode_frame(false,state,part,offset,packed,packed_offset,expected,sequence,decode,
            blocks,header_limit,caps,effect);
    assert(indexed =~= ordinary);
}

pub(crate) proof fn terminal_precinct_mode_publish(
    terminal: bool, state: Part1PacketPrecinctState, part: Part2OwnedTilePart,
    offset: usize, packed: Seq<u8>, packed_offset: usize, expected: Option<u32>, sequence: u16, decode: bool,
    blocks: u64, header_limit: u64, caps: Part2LegacyCaps, parameters: Part1PrecinctPayloadParameters,
    actual: Part1PrecinctPayloadResult,
)
    requires part2_plane_precinct_admit(state,part,offset,packed_offset,expected,sequence,decode,blocks,caps.work)==Ok(parameters),
        parameters.decode_tier1 == decode,
        terminal_exact_observed(actual,|effect|terminal_payload_mode_frame(terminal,terminal_precinct_context(state,part,offset,packed,parameters,header_limit,caps.work),caps,effect)),
    ensures terminal_exact_observed(actual,|effect|terminal_precinct_mode_frame(terminal,state,part,offset,
        packed,packed_offset,expected,sequence,decode,blocks,header_limit,caps,effect)),
        !terminal ==> terminal_exact_observed(actual,|effect|part2_plane_precinct_result(state,part,offset,packed,
            packed_offset,expected,sequence,decode,blocks,header_limit,caps.passes,caps.bytes,caps.input,caps.work,effect)),
{
    let context = terminal_precinct_context(state,part,offset,packed,parameters,header_limit,caps.work);
    let found = terminal_exact_witness(actual,|effect|terminal_payload_mode_frame(terminal,context,caps,effect));
    if terminal && decode {
        part2_tier1_storage_eta(|calls|terminal_payload_run(context,caps,calls),Ok(found));
    } else {
        part2_plane_precinct_observed(state,part,offset,packed,packed_offset,expected,sequence,decode,blocks,header_limit,
            caps.passes,caps.bytes,caps.input,caps.work,parameters,found);
        if !terminal {
            terminal_exact_publish(actual,found,|effect|part2_plane_precinct_result(state,part,offset,packed,
                packed_offset,expected,sequence,decode,blocks,header_limit,caps.passes,caps.bytes,caps.input,caps.work,effect));
        }
    }
    terminal_exact_publish(actual,found,|effect|terminal_precinct_mode_frame(terminal,state,part,offset,
        packed,packed_offset,expected,sequence,decode,blocks,header_limit,caps,effect));
}

pub(crate) open spec fn terminal_precinct_mode_matches(
    terminal: bool, actual: Part1PrecinctPayloadResult,
    state: Part1PacketPrecinctState, part: Part2OwnedTilePart, offset: usize,
    packed: Seq<u8>, packed_offset: usize, expected: Option<u32>, sequence: u16, decode: bool,
    blocks: u64, header_limit: u64, caps: Part2LegacyCaps,
) -> bool {
    if terminal && decode {
        terminal_exact_matches(actual,
            terminal_precinct_value(state, part, offset, packed, packed_offset, expected, sequence, decode,
                blocks, header_limit, caps))
    } else {
        terminal_exact_matches(actual, part1_precinct_packet_owned(state, part, offset, packed,
            packed_offset, expected, sequence, decode, blocks, header_limit, caps.passes, caps.bytes, caps.input, caps.work))
    }
}

pub(crate) open spec fn terminal_payload_mode_value(
    terminal: bool, context: Part2PrecinctContributionsContext, caps: Part2LegacyCaps,
) -> Part1PrecinctPayloadResult {
    if terminal && context.parameters.decode_tier1 {
        terminal_payload_value(context, caps)
    } else {
        part1_precinct_payload(context.state, context.data, context.packed, context.parameters, context.header_limit,
            caps.passes, caps.bytes, caps.input, caps.work)
    }
}

pub(crate) open spec fn terminal_payload_after_mode_value(
    terminal: bool, state: Part1PacketPrecinctState, parameters: Part1PrecinctPayloadParameters,
    data: Seq<u8>, header: Part2PlanePayloadHeader, caps: Part2LegacyCaps,
) -> Part1PrecinctPayloadResult {
    if terminal && parameters.decode_tier1 {
        terminal_payload_after_value(state, parameters, data, header, caps)
    } else {
        part1_precinct_payload_after_headers(state, parameters, data, header.packet, header.reader,
            header.contributions, header.count, header.present, header.sop, caps.passes, caps.bytes, caps.input, caps.work)
    }
}

pub(crate) proof fn terminal_payload_after_publish(
    terminal: bool, state: Part1PacketPrecinctState, parameters: Part1PrecinctPayloadParameters, data: Seq<u8>,
    header: Part2PlanePayloadHeader, caps: Part2LegacyCaps, args: (usize,usize,usize,usize),
    executed: Part1PacketBodyExecutionResult, actual: Part1PacketPrecinctState,
)
    requires part2_plane_payload_admit(parameters,data,header.packet,header.reader,header.contributions,header.sop)==Ok(args),
        terminal_exact_observed(executed,|effect|terminal_payload_execution_frame(
            terminal,state,parameters,data,header,caps,args.1,effect)),
        executed.0.is_err() ==> actual == (Part1PacketPrecinctState {decoders: executed.1.decoders,..state}),
    ensures
        match executed.0 {
            Err(error) => terminal_exact_observed((Err(error),actual),
                |effect|terminal_payload_mode_after_frame(terminal,state,parameters,data,header,caps,effect))
                && (!terminal ==> terminal_exact_observed((Err(error),actual),
                    |effect|part2_plane_payload_after_result(state,parameters,data,header.packet,header.reader,
                        header.contributions,header.count,header.present,header.sop,caps.passes,caps.bytes,caps.input,caps.work,effect))),
            Ok(()) => true,
        },
        executed.0.is_ok() ==> terminal_payload_mode_after_frame(terminal,state,parameters,data,header,caps,
            part2_plane_payload_finish(state,parameters,header.present,header.count,args,executed)),
        !terminal && executed.0.is_ok() ==> part2_plane_payload_after_result(state,parameters,data,header.packet,header.reader,
            header.contributions,header.count,header.present,header.sop,caps.passes,caps.bytes,caps.input,caps.work,
            part2_plane_payload_finish(state,parameters,header.present,header.count,args,executed)),
{
    let effect=terminal_exact_witness(executed,|effect|terminal_payload_execution_frame(
        terminal,state,parameters,data,header,caps,args.1,effect));
    if terminal && parameters.decode_tier1 {
        terminal_payload_after_observed(state,parameters,data,header,caps,args,effect);
    } else {
        part2_plane_payload_after_observed(state,parameters,data,header.packet,header.reader,
            header.contributions,header.count,header.present,header.sop,caps.passes,caps.bytes,caps.input,caps.work,args,effect);
    }
    if let Err(error) = executed.0 {
        let failed = (Err(error),actual);
        let output=part2_plane_payload_finish(state,parameters,header.present,header.count,args,effect);
        terminal_exact_publish(failed,output,
            |effect|terminal_payload_mode_after_frame(terminal,state,parameters,data,header,caps,effect));
        if !terminal {
            terminal_exact_publish(failed,output,|effect|part2_plane_payload_after_result(state,parameters,data,
                header.packet,header.reader,header.contributions,header.count,header.present,header.sop,
                caps.passes,caps.bytes,caps.input,caps.work,effect));
        }
    }
}

pub(crate) proof fn terminal_payload_execution_observed(
    terminal: bool, state: Part1PacketPrecinctState, p: Part1PrecinctPayloadParameters,
    data: Seq<u8>, header: Part2PlanePayloadHeader, caps: Part2LegacyCaps, start: usize,
    actual: Part1PacketBodyExecutionResult,
)
    requires if terminal && p.decode_tier1 {
            terminal_exact_observed(actual, |effect:Part1PacketBodyExecutionResult|
                terminal_body_frame(terminal_payload_body_initial(state,start),header.contributions,data,
                    (p.error_offset,0),true,caps,effect))
        } else {
            terminal_exact_observed(actual, |effect:Part1PacketBodyExecutionResult|
                part2_plane_execute_result(terminal_payload_body_initial(state,start),header.contributions,data,
                    p.error_offset,0,p.decode_tier1,caps.passes,caps.bytes,caps.input,caps.work,effect))
        },
    ensures terminal_exact_observed(actual,|effect:Part1PacketBodyExecutionResult|
        terminal_payload_execution_frame(terminal,state,p,data,header,caps,start,effect)),
{
    let before=terminal_payload_body_initial(state,start);
    let frame=|effect:Part1PacketBodyExecutionResult|terminal_payload_execution_frame(terminal,state,p,data,header,caps,start,effect);
    if terminal && p.decode_tier1 {
        let child=|effect:Part1PacketBodyExecutionResult|terminal_body_frame(before,header.contributions,data,(p.error_offset,0),true,caps,effect);
        assert(frame =~= child);
    } else {
        let child=|effect:Part1PacketBodyExecutionResult|part2_plane_execute_result(before,header.contributions,data,
            p.error_offset,0,p.decode_tier1,caps.passes,caps.bytes,caps.input,caps.work,effect);
        assert(frame =~= child);
    }
}

pub(crate) open spec fn terminal_payload_execution_frame(
    terminal: bool, state: Part1PacketPrecinctState, p: Part1PrecinctPayloadParameters,
    data: Seq<u8>, header: Part2PlanePayloadHeader, caps: Part2LegacyCaps, start: usize,
    effect: Part1PacketBodyExecutionResult,
) -> bool {
    let before=terminal_payload_body_initial(state,start);
    if terminal && p.decode_tier1 {
        terminal_body_frame(before,header.contributions,data,(p.error_offset,0),true,caps,effect)
    } else {
        part2_plane_execute_result(before,header.contributions,data,p.error_offset,0,p.decode_tier1,
            caps.passes,caps.bytes,caps.input,caps.work,effect)
    }
}

pub(crate) proof fn terminal_payload_after_observed(
    state: Part1PacketPrecinctState, parameters: Part1PrecinctPayloadParameters,
    data: Seq<u8>, header: Part2PlanePayloadHeader, caps: Part2LegacyCaps,
    args: (usize, usize, usize, usize), effect: Part1PacketBodyExecutionResult,
)
    requires part2_plane_payload_admit(parameters, data, header.packet, header.reader, header.contributions, header.sop) == Ok(args),
        terminal_body_frame(terminal_payload_body_initial(state, args.1), header.contributions, data,
            (parameters.error_offset, 0), parameters.decode_tier1, caps, effect),
    ensures terminal_payload_after_frame(state, parameters, data, header, caps,
        part2_plane_payload_finish(state, parameters, header.present, header.count, args, effect)),
{
    let after = part2_plane_payload_finish(state, parameters, header.present, header.count, args, effect);
    part2_tier1_storage_pure(Ok(after));
    part2_tier1_storage_bind_frame(
        |calls| terminal_body_run(true,terminal_payload_body_initial(state, args.1), header.contributions, data,
            parameters.error_offset, 0, parameters.decode_tier1, caps, calls),
        |value: Part1PacketBodyExecutionResult, rest|
            Some((Ok(part2_plane_payload_finish(state, parameters, header.present, header.count, args, value)), rest)),
        Ok(effect), Ok(after),
    );
}

pub(crate) open spec fn terminal_payload_prepared_run(
    context: Part2PrecinctContributionsContext, caps: Part2LegacyCaps, calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part1PrecinctPayloadResult> {
    let prepared = part2_plane_payload_headers(context.state, context.data, context.packed, context.parameters,
        context.header_limit, context.work);
    match prepared.0 {
        Err(error) => Some((Ok((Err(error), prepared.1)), calls)),
        Ok(header) => terminal_payload_after_run(prepared.1, context.parameters, context.data, header, caps, calls),
    }
}

pub(crate) open spec fn terminal_payload_run(
    context: Part2PrecinctContributionsContext, caps: Part2LegacyCaps, calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part1PrecinctPayloadResult> {
    match part1_precinct_payload_prefix(context.data, context.packed, context.parameters, context.header_limit, context.work) {
        Err(error) => Some((Ok((Err(error), context.state)), calls)),
        Ok(_) => part2_tier1_storage_resume(part2_precinct_contributions_run(context, calls),
            |response: Result<(), crate::DecodeError>, rest| match response {
                Err(error) => Some((Ok((Err(error), context.state)), rest)),
                Ok(()) => terminal_payload_prepared_run(context, caps, rest),
            }),
    }
}

pub(crate) open spec fn terminal_payload_value(
    context: Part2PrecinctContributionsContext, caps: Part2LegacyCaps,
) -> Part1PrecinctPayloadResult {
    let prepared = part2_plane_payload_headers(context.state, context.data, context.packed, context.parameters,
        context.header_limit, context.work);
    match prepared.0 {
        Err(error) => (Err(error), prepared.1),
        Ok(header) => terminal_payload_after_value(prepared.1, context.parameters, context.data, header, caps),
    }
}

pub(crate) proof fn terminal_payload_capacity(
    context: Part2PrecinctContributionsContext, caps: Part2LegacyCaps,
    response: Result<(), crate::DecodeError>, result: Part1PrecinctPayloadResult,
)
    requires part1_precinct_payload_prefix(context.data, context.packed, context.parameters, context.header_limit, context.work).is_ok(),
        part2_precinct_contributions_result(context, response),
        match response {
            Err(error) => result == (Err(error), context.state),
            Ok(()) => part2_tier1_storage_framed(|calls| terminal_payload_prepared_run(context, caps, calls), Ok(result)),
        },
    ensures part2_tier1_storage_framed(|calls| terminal_payload_run(context, caps, calls), Ok(result)),
{
    if response.is_err() { part2_tier1_storage_pure(Ok(result)); }
    else { part2_tier1_storage_eta(|calls| terminal_payload_prepared_run(context, caps, calls), Ok(result)); }
    part2_tier1_resume_frame(
        |calls| part2_precinct_contributions_run(context, calls),
        |reply: Result<(), crate::DecodeError>, rest| match reply {
            Err(error) => Some((Ok((Err(error), context.state)), rest)),
            Ok(()) => terminal_payload_prepared_run(context, caps, rest),
        }, response, Ok(result),
    );
}

pub(crate) proof fn terminal_payload_observed(
    context: Part2PrecinctContributionsContext, caps: Part2LegacyCaps,
    after: Part1PacketPrecinctState, header: Part2PlanePayloadHeader, result: Part1PrecinctPayloadResult,
)
    requires part2_plane_payload_headers(context.state, context.data, context.packed, context.parameters,
            context.header_limit, context.work) == (Ok(header), after),
        part1_precinct_payload_prefix(context.data, context.packed, context.parameters, context.header_limit, context.work).is_ok(),
        part2_precinct_contributions_result(context, Ok(())),
        terminal_payload_after_frame(after, context.parameters, context.data, header, caps, result),
    ensures part2_tier1_storage_framed(|calls| terminal_payload_run(context, caps, calls), Ok(result)),
{
    part2_tier1_storage_eta(
        |calls| terminal_payload_after_run(after, context.parameters, context.data, header, caps, calls), Ok(result));
    terminal_payload_capacity(context, caps, Ok(()), result);
}

pub(crate) proof fn terminal_payload_after_normal_observed(
    state: Part1PacketPrecinctState, parameters: Part1PrecinctPayloadParameters,
    data: Seq<u8>, header: Part2PlanePayloadHeader, caps: Part2LegacyCaps,
)
    ensures terminal_payload_after_frame(state, parameters, data, header, caps,
        terminal_payload_after_value(state, parameters, data, header, caps)),
{
    match part2_plane_payload_admit(parameters, data, header.packet, header.reader, header.contributions, header.sop) {
        Err(error) => { part2_tier1_storage_pure(Ok::<Part1PrecinctPayloadResult, crate::DecodeError>((Err(error), state))); }
        Ok(args) => {
            let start = terminal_payload_body_initial(state, args.1);
            terminal_body_normal_observed(start, header.contributions, data, (parameters.error_offset, 0), parameters.decode_tier1, caps);
            terminal_payload_after_observed(state, parameters, data, header, caps, args,
                terminal_body_value(true,start,header.contributions,data,parameters.error_offset,0,parameters.decode_tier1,caps));
        }
    }
}

pub(crate) proof fn terminal_payload_normal_observed(
    context: Part2PrecinctContributionsContext, caps: Part2LegacyCaps,
)
    ensures part2_tier1_storage_framed(|calls| terminal_payload_run(context, caps, calls),
        Ok(terminal_payload_value(context, caps))),
{
    let result = terminal_payload_value(context, caps);
    match part1_precinct_payload_prefix(context.data,context.packed,context.parameters,context.header_limit,context.work) {
        Err(_) => { part2_tier1_storage_pure(Ok(result)); }
        Ok(_) => {
            part2_precinct_contributions_observed(context, Ok(()));
            match part2_plane_payload_headers(context.state,context.data,context.packed,context.parameters,context.header_limit,context.work) {
                (Err(_), _) => {part2_tier1_storage_pure(Ok(result));}
                (Ok(h), state) => {
                    terminal_payload_after_normal_observed(state, context.parameters, context.data, h, caps);
                    part2_tier1_storage_eta(|calls|terminal_payload_after_run(state,context.parameters,context.data,h,caps,calls),Ok(result));
                }
            }
            terminal_payload_capacity(context, caps, Ok(()), result);
        }
    }
}

pub(crate) proof fn terminal_payload_related(
    context: Part2PrecinctContributionsContext, caps: Part2LegacyCaps,
)
    requires caps.work == context.work,
    ensures {
        let actual = terminal_payload_value(context, caps);
        let baseline = part1_precinct_payload(context.state, context.data, context.packed,
            context.parameters, context.header_limit, caps.passes, caps.bytes, caps.input, context.work);
        actual.0 == baseline.0 && terminal_precinct_related(actual.1, baseline.1)
    },
{
    reveal(part1_precinct_payload_headers);
    reveal(part1_precinct_payload_after_headers);
    reveal(part1_precinct_payload_body);
    reveal(part1_packet_body_execute);
    let (prepared, state) = part2_plane_payload_headers(context.state, context.data, context.packed,
        context.parameters, context.header_limit, context.work);
    if let Ok(header) = prepared {
        if let Ok(args) = part2_plane_payload_admit(context.parameters, context.data, header.packet,
            header.reader, header.contributions, header.sop) {
            let initial = terminal_payload_body_initial(state, args.1);
            terminal_body_related(initial, initial, header.contributions, context.data, context.parameters.error_offset,
                0, context.parameters.decode_tier1, caps);
            let a = terminal_body_value(true,initial,header.contributions,context.data,context.parameters.error_offset,0,
                context.parameters.decode_tier1,caps);
            let b = part1_packet_body_execute_at(initial,header.contributions,context.data,context.parameters.error_offset,0,
                context.parameters.decode_tier1,caps.passes,caps.bytes,caps.input,caps.work);
            let left = part2_plane_payload_finish(state,context.parameters,header.present,header.count,args,a);
            let right = part2_plane_payload_finish(state,context.parameters,header.present,header.count,args,b);
            terminal_precinct_updates_related(left.1,right.1);
            assert(left.0 == right.0);
        }
    }
}

pub(crate) proof fn terminal_precinct_updates_related(actual: Part1PacketPrecinctState, baseline: Part1PacketPrecinctState)
    requires actual == (Part1PacketPrecinctState {decoders: actual.decoders,..baseline}),
        actual.decoders.len() == baseline.decoders.len(),
        forall|i:int| 0<=i<actual.decoders.len() ==>
            terminal_decoder_related(#[trigger] actual.decoders[i],#[trigger] baseline.decoders[i]),
    ensures terminal_precinct_related(actual,baseline),
{
    let project = |d:Tier1DecoderState| terminal_decoder_live(d);
    assert(actual.decoders.map_values(project) =~= baseline.decoders.map_values(project));
}

pub(crate) open spec fn terminal_precinct_context(
    state: Part1PacketPrecinctState, part: Part2OwnedTilePart, offset: usize, packed: Seq<u8>,
    parameters: Part1PrecinctPayloadParameters, header_limit: u64, work: u64,
) -> Part2PrecinctContributionsContext {
    Part2PrecinctContributionsContext {state, data: part.data.subrange(offset as int, part.data.len() as int),
        packed, parameters, header_limit, work}
}

pub(crate) open spec fn terminal_precinct_run(
    state: Part1PacketPrecinctState, part: Part2OwnedTilePart, offset: usize, packed: Seq<u8>,
    packed_offset: usize, expected: Option<u32>, sequence: u16, decode: bool,
    blocks: u64, header_limit: u64, caps: Part2LegacyCaps, calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part1PrecinctPayloadResult> {
    match part2_plane_precinct_admit(state, part, offset, packed_offset, expected, sequence, decode, blocks, caps.work) {
        Err(error) => Some((Ok((Err(error), state)), calls)),
        Ok(parameters) => terminal_payload_run(
            terminal_precinct_context(state, part, offset, packed, parameters, header_limit, caps.work), caps, calls),
    }
}

pub(crate) open spec fn terminal_precinct_value(
    state: Part1PacketPrecinctState, part: Part2OwnedTilePart, offset: usize, packed: Seq<u8>,
    packed_offset: usize, expected: Option<u32>, sequence: u16, decode: bool,
    blocks: u64, header_limit: u64, caps: Part2LegacyCaps,
) -> Part1PrecinctPayloadResult {
    match part2_plane_precinct_admit(state, part, offset, packed_offset, expected, sequence, decode, blocks, caps.work) {
        Err(error) => (Err(error), state),
        Ok(parameters) => terminal_payload_value(
            terminal_precinct_context(state, part, offset, packed, parameters, header_limit, caps.work), caps),
    }
}

pub(crate) proof fn terminal_precinct_value_related(
    state: Part1PacketPrecinctState, part: Part2OwnedTilePart, offset: usize, packed: Seq<u8>,
    packed_offset: usize, expected: Option<u32>, sequence: u16, decode: bool,
    blocks: u64, header_limit: u64, caps: Part2LegacyCaps,
)
    ensures {
        let actual = terminal_precinct_value(state, part, offset, packed, packed_offset, expected, sequence, decode,
            blocks, header_limit, caps);
        let baseline = part1_precinct_packet_owned(state, part, offset, packed, packed_offset, expected, sequence, decode,
            blocks, header_limit, caps.passes, caps.bytes, caps.input, caps.work);
        actual.0 == baseline.0 && terminal_precinct_related(actual.1, baseline.1)
    },
{
    if let Ok(parameters) = part2_plane_precinct_admit(state, part, offset, packed_offset, expected, sequence, decode, blocks, caps.work) {
        terminal_payload_related(terminal_precinct_context(state, part, offset, packed, parameters, header_limit, caps.work), caps);
    }
}

pub(crate) proof fn terminal_precinct_normal_observed(
    state: Part1PacketPrecinctState, part: Part2OwnedTilePart, offset: usize, packed: Seq<u8>,
    packed_offset: usize, expected: Option<u32>, sequence: u16, decode: bool,
    blocks: u64, header_limit: u64, caps: Part2LegacyCaps,
)
    ensures part2_tier1_storage_framed(
        |calls| terminal_precinct_run(state, part, offset, packed, packed_offset, expected, sequence,
            decode, blocks, header_limit, caps, calls),
        Ok(terminal_precinct_value(state, part, offset, packed, packed_offset, expected, sequence, decode, blocks, header_limit, caps))),
{
    match part2_plane_precinct_admit(state, part, offset, packed_offset, expected, sequence, decode, blocks, caps.work) {
        Err(error) => {part2_tier1_storage_pure(Ok::<Part1PrecinctPayloadResult, crate::DecodeError>((Err(error), state)));}
        Ok(parameters) => {
            let context = terminal_precinct_context(state, part, offset, packed, parameters, header_limit, caps.work);
            terminal_payload_normal_observed(context, caps);
            part2_tier1_storage_eta(|calls| terminal_payload_run(context, caps, calls),Ok(terminal_payload_value(context,caps)));
        },
    }
}

pub(crate) open spec fn terminal_tile_precinct_run(
    terminal: bool, params: Part1TilePacketParameters, part: Part2OwnedTilePart,
    p: Part1TilePacketProgress, coordinate: crate::packet::PacketCoordinate, expected: Option<u32>,
    precinct: Part1PacketPrecinctState, calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<Part1PrecinctPayloadResult> {
    if !terminal {
        part2_plane_tile_precinct_run(params, part, p, coordinate, expected, precinct, calls)
    } else {
        let layered = part1_precinct_context_layer(precinct, coordinate.layer);
        if p.current_tile_part >= params.input.packed.len() {
            Some((Ok((Err(ht_reader_error(crate::MalformedKind::InvalidTilePart)), layered)), calls))
        } else if params.selection.is_some() && coordinate.component as nat >= params.selection.unwrap().len() {
            Some((Ok((Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle)), layered)), calls))
        } else {
            let decode = match params.selection { None => true, Some(counts) => coordinate.resolution < counts[coordinate.component as int] };
            if decode {
                terminal_precinct_run(layered, part, p.offset, params.input.packed[p.current_tile_part as int],
                    p.packed_offset, expected, (p.packets & 65535u64) as u16, decode, params.caps.blocks, params.caps.header,
                    part2_legacy_caps(params.caps.passes, params.caps.bytes, params.caps.input, params.caps.work), calls)
            } else { part2_plane_tile_precinct_run(params, part, p, coordinate, expected, precinct, calls) }
        }
    }
}

pub(crate) open spec fn terminal_tile_packet_run(
    params: Part1TilePacketParameters, state: Part1TilePacketExecution, coordinate: crate::packet::PacketCoordinate,
    calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<(Result<(),crate::DecodeError>, Part1TilePacketExecution)> {
    match part2_plane_tile_packet_admit(params, state, coordinate) {
        Part2PlaneTileAdmission::Return(value) => Some((Ok(value), calls)),
        Part2PlaneTileAdmission::Packet { state: after, part, index, seen, expected } => {
            let terminal = terminal_precinct_last_slot(after.progress.seen, params.grid.layers as nat,
                index as nat, seen, coordinate.layer as nat);
            part2_tier1_storage_bind(
                terminal_tile_precinct_run(terminal, params, part, after.progress, coordinate, expected, after.precincts[index as int], calls),
                |packet: Part1PrecinctPayloadResult, rest|
                    Some((Ok(part2_plane_tile_packet_finish(after, index, seen, expected, packet)), rest)),
            )
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn terminal_tile_run(
    params: Part1TilePacketParameters, state: Part1TilePacketExecution, calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<(Result<(),crate::DecodeError>, Part1TilePacketExecution)>
    decreases state.progress.remaining_packets * 2 + 1,
{
    match part2_plane_tile_run_admit(params, state) {
        Part2PlaneTileStep::Return(value) => Some((Ok(value), calls)),
        Part2PlaneTileStep::Continue(after) =>
            if after.progress.remaining_packets < state.progress.remaining_packets { terminal_tile_run(params, after, calls) } else { None },
        Part2PlaneTileStep::Packet(coordinate, after) => part2_tier1_storage_bind(
            terminal_tile_packet_run(params, after, coordinate, calls),
            |packet: (Result<(),crate::DecodeError>, Part1TilePacketExecution), rest|
                terminal_tile_after_packet(params, state.progress.remaining_packets, packet, rest),
        ),
    }
}

pub(crate) open spec fn terminal_tile_after_packet(
    params: Part1TilePacketParameters, budget: u64,
    packet: (Result<(),crate::DecodeError>, Part1TilePacketExecution), calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<(Result<(),crate::DecodeError>, Part1TilePacketExecution)>
    decreases budget * 2,
{
    if packet.0.is_err() { Some((Ok(packet), calls)) }
    else if packet.1.progress.remaining_packets < budget { terminal_tile_run(params, packet.1, calls) } else { None }
}

pub(crate) open spec fn terminal_tile_precinct_value(
    terminal: bool, params: Part1TilePacketParameters, part: Part2OwnedTilePart, p: Part1TilePacketProgress,
    coordinate: crate::packet::PacketCoordinate, expected: Option<u32>, precinct: Part1PacketPrecinctState,
) -> Part1PrecinctPayloadResult {
    if !terminal || p.current_tile_part >= params.input.packed.len()
        || (params.selection.is_some() && coordinate.component as nat >= params.selection.unwrap().len()) {
        part1_tile_precinct_packet_owned(params, part, p, coordinate, expected, precinct)
    } else {
        let layered = part1_precinct_context_layer(precinct, coordinate.layer);
        let decode = match params.selection { None => true, Some(counts) => coordinate.resolution < counts[coordinate.component as int] };
        if decode {
            terminal_precinct_value(layered, part, p.offset, params.input.packed[p.current_tile_part as int],
                p.packed_offset, expected, (p.packets & 65535u64) as u16, decode, params.caps.blocks, params.caps.header,
                part2_legacy_caps(params.caps.passes, params.caps.bytes, params.caps.input, params.caps.work))
        } else {
            part1_tile_precinct_packet_owned(params, part, p, coordinate, expected, precinct)
        }
    }
}

pub(crate) open spec fn terminal_tile_packet_value(
    params: Part1TilePacketParameters, state: Part1TilePacketExecution, coordinate: crate::packet::PacketCoordinate,
) -> (Result<(), crate::DecodeError>, Part1TilePacketExecution) {
    match part2_plane_tile_packet_admit(params, state, coordinate) {
        Part2PlaneTileAdmission::Return(value) => value,
        Part2PlaneTileAdmission::Packet { state: after, part, index, seen, expected } => {
            let terminal = terminal_precinct_last_slot(after.progress.seen, params.grid.layers as nat,
                index as nat, seen, coordinate.layer as nat);
            let packet = terminal_tile_precinct_value(terminal, params, part, after.progress, coordinate,
                expected, after.precincts[index as int]);
            part2_plane_tile_packet_finish(after, index, seen, expected, packet)
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn terminal_tile_value(
    params: Part1TilePacketParameters, state: Part1TilePacketExecution,
) -> (Result<(), crate::DecodeError>, Part1TilePacketExecution)
    decreases state.progress.remaining_packets,
{
    match part2_plane_tile_run_admit(params, state) {
        Part2PlaneTileStep::Return(value) => value,
        Part2PlaneTileStep::Continue(after) =>
            if after.progress.remaining_packets < state.progress.remaining_packets { terminal_tile_value(params, after) }
            else { (Err(ht_reader_error(crate::MalformedKind::InvalidProgressionOrderChange)), after) },
        Part2PlaneTileStep::Packet(coordinate, after) => {
            let result = terminal_tile_packet_value(params, after, coordinate);
            if result.0.is_ok() && result.1.progress.remaining_packets < state.progress.remaining_packets {
                terminal_tile_value(params, result.1)
            } else { result }
        },
    }
}

pub(crate) open spec fn terminal_tile_precinct_frame(
    terminal: bool, params: Part1TilePacketParameters, part: Part2OwnedTilePart,
    p: Part1TilePacketProgress, coordinate: crate::packet::PacketCoordinate, expected: Option<u32>,
    precinct: Part1PacketPrecinctState, effect: Part1PrecinctPayloadResult,
) -> bool {
    if terminal { part2_tier1_storage_framed(
        |calls| terminal_tile_precinct_run(true, params, part, p, coordinate, expected, precinct, calls), Ok(effect))
    } else { part2_plane_tile_precinct_result(params, part, p, coordinate, expected, precinct, effect) }
}

pub(crate) open spec fn terminal_tile_packet_frame(
    final_image: bool, params: Part1TilePacketParameters, state: Part1TilePacketExecution,
    coordinate: crate::packet::PacketCoordinate, output: (Result<(), crate::DecodeError>, Part1TilePacketExecution),
) -> bool {
    if final_image { part2_tier1_storage_framed(
        |calls| terminal_tile_packet_run(params, state, coordinate, calls), Ok(output))
    } else { part2_plane_tile_packet_result(params, state, coordinate, output) }
}

pub(crate) open spec fn terminal_tile_mode_run(
    final_image: bool, params: Part1TilePacketParameters, state: Part1TilePacketExecution,
    calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<(Result<(), crate::DecodeError>, Part1TilePacketExecution)> {
    if final_image { terminal_tile_run(params, state, calls) }
    else { part2_plane_tile_run(params, state, calls) }
}

pub(crate) open spec fn terminal_tile_mode_frame(
    final_image: bool, params: Part1TilePacketParameters, state: Part1TilePacketExecution,
    output: (Result<(), crate::DecodeError>, Part1TilePacketExecution),
) -> bool {
    if final_image { part2_tier1_storage_framed(|calls| terminal_tile_run(params, state, calls), Ok(output)) }
    else { part2_plane_tile_run_result(params, state, output) }
}

pub(crate) open spec fn terminal_tile_mode_value(
    final_image: bool, params: Part1TilePacketParameters, state: Part1TilePacketExecution,
) -> (Result<(), crate::DecodeError>, Part1TilePacketExecution) {
    if final_image { terminal_tile_value(params, state) }
    else { part1_tile_run(params, state) }
}

pub(crate) proof fn terminal_unravel_bounds(index: u64, dimensions: Seq<u64>, values: Seq<u64>)
    requires part1_packet_unravel(index, dimensions) == Ok(values),
    ensures values.len() == 4, dimensions.len() == 4,
        0 < dimensions[1], 0 < dimensions[2], 0 < dimensions[3],
        values[0] < dimensions[0], values[1] < dimensions[1], values[2] < dimensions[2], values[3] < dimensions[3],
{
    let v = index / dimensions[3];
    let w = v / dimensions[2];
    vstd::arithmetic::div_mod::lemma_mod_bound(index as int, dimensions[3] as int);
    vstd::arithmetic::div_mod::lemma_mod_bound(v as int, dimensions[2] as int);
    vstd::arithmetic::div_mod::lemma_mod_bound(w as int, dimensions[1] as int);
}

pub(crate) proof fn terminal_regular_candidate_bound(
    grid: Part1PacketGrid, order: crate::codestream::ProgressionOrder, candidate: u64,
    coordinate: crate::packet::PacketCoordinate,
)
    requires part1_packet_candidate(grid, order, candidate) == Ok(coordinate),
    ensures coordinate.layer < grid.layers,
{
    let dims = part1_packet_candidate_dimensions(grid, order);
    if let Ok(values) = part1_packet_unravel(candidate, dims) {
        terminal_unravel_bounds(candidate, dims, values);
        match order {
            crate::codestream::ProgressionOrder::Lrcp => {},
            crate::codestream::ProgressionOrder::Rlcp => {},
            _ => {},
        }
    }
}

pub(crate) proof fn terminal_window_candidate_bound(
    grid: Part1PacketGrid, record: crate::codestream::ProgressionChange, candidate: u64,
    coordinate: crate::packet::PacketCoordinate,
)
    requires part1_packet_window_candidate(grid, record, candidate) == Ok(coordinate),
    ensures coordinate.layer < grid.layers,
{
    let window = part1_packet_window_bounds(grid, record);
    let local = Part1PacketGrid { layers: window.layer_end,
        resolutions: (window.resolution_end - window.resolution_start) as u8,
        components: (window.component_end - window.component_start) as u16, ..grid };
    let order = window.progression_order;
    let dims = part1_packet_candidate_dimensions(local, order);
    if let Ok(values) = part1_packet_unravel(candidate, dims) {
        terminal_unravel_bounds(candidate, dims, values);
        match order {
            crate::codestream::ProgressionOrder::Lrcp => {},
            crate::codestream::ProgressionOrder::Rlcp => {},
            _ => {},
        }
    }
}

pub(crate) proof fn terminal_regular_next_bound(state: Part1PacketIterator)
    ensures part1_packet_iterator_next(state).1.grid == state.grid,
        match part1_packet_iterator_next(state).0 { Ok(Some(c)) => c.layer < state.grid.layers, _ => true },
    decreases match part1_packet_candidate_count(state.grid, state.order) {
        Err(_) => 0nat,
        Ok(count) => if state.candidate_index >= count { 0nat } else { (count - state.candidate_index) as nat },
    },
{
    reveal(part1_packet_iterator_next);
    if let Ok(count) = part1_packet_candidate_count(state.grid, state.order) {
        if state.candidate_index < count {
            if let Ok(c) = part1_packet_candidate(state.grid, state.order, state.candidate_index) {
                terminal_regular_candidate_bound(state.grid, state.order, state.candidate_index, c);
                if let Ok(precincts) = part1_packet_grid_precinct_count(state.grid, c.component, c.resolution) {
                    if c.precinct >= precincts {
                        terminal_regular_next_bound(Part1PacketIterator { candidate_index: (state.candidate_index + 1) as u64, ..state });
                    }
                }
            }
        }
    }
}

pub(crate) proof fn terminal_windows_next_bound(state: Part1ProgressionPacketIterator)
    ensures part1_progression_windows_next(state).1.grid == state.grid,
        part1_progression_windows_next(state).1.default == state.default,
        match part1_progression_windows_next(state).0 { Ok(Some(c)) => c.layer < state.grid.layers, _ => true },
    decreases state.changes.len() - state.window_index as nat,
        if state.window_candidate >= state.window_candidates { 0nat }
        else { (state.window_candidates-state.window_candidate) as nat },
{
    reveal(part1_progression_windows_next);
    if state.window_index < state.changes.len() {
        if state.window_candidate < state.window_candidates {
            let record = state.changes[state.window_index as int];
            let step = part1_progression_candidate_step(state, record);
            match step.0 {
                Ok(None) => terminal_windows_next_bound(step.1),
                Ok(Some(c)) => terminal_window_candidate_bound(state.grid, record, state.window_candidate, c),
                Err(_) => {},
            }
        } else {
            let step = part1_progression_next_window(state);
            if step.0.is_ok() { terminal_windows_next_bound(step.1); }
        }
    }
}

pub(crate) open spec fn terminal_iterator_grid(state: Part1ProgressionPacketIterator, grid: Part1PacketGrid) -> bool {
    state.grid == grid && (state.default.is_some() ==> state.default.unwrap().grid == grid)
}

pub(crate) proof fn terminal_iterator_bound(state: Part1ProgressionPacketIterator, grid: Part1PacketGrid)
    requires terminal_iterator_grid(state, grid),
    ensures terminal_iterator_grid(part1_progression_iterator_next(state).1, grid),
        match part1_progression_iterator_next(state).0 { Ok(Some(c)) => c.layer < grid.layers, _ => true },
{
    match state.default {
        Some(default) => terminal_regular_next_bound(default),
        None => terminal_windows_next_bound(state),
    }
}

pub(crate) proof fn terminal_boundary_frame(params: Part1TilePacketParameters, before: Part1TilePacketProgress)
    requires terminal_iterator_grid(before.iterator, params.grid),
    ensures terminal_iterator_grid(part1_tile_boundary(params,before).1.iterator, params.grid),
        part1_tile_boundary(params,before).1.seen == before.seen,
        part1_tile_boundary(params,before).1.remaining_packets == before.remaining_packets,
{}

pub(crate) proof fn terminal_progress_initial_grid(params: Part1TilePacketParameters, progress: Part1TilePacketProgress)
    requires part1_tile_progress_initial(params) == Ok(progress),
    ensures terminal_iterator_grid(progress.iterator, params.grid),
{}

pub(crate) proof fn terminal_project_planes(actual: Seq<Part1PacketPrecinctState>, baseline: Seq<Part1PacketPrecinctState>)
    requires actual.len() == baseline.len(),
        forall|i: int| 0 <= i < actual.len() ==>
            terminal_precinct_related(#[trigger] actual[i], #[trigger] baseline[i]),
    ensures part2_precinct_decoder_planes(actual) == part2_precinct_decoder_planes(baseline),
{
    assert(part2_precinct_decoder_planes(actual) =~= part2_precinct_decoder_planes(baseline)) by {
        assert forall|i: int| 0 <= i < actual.len() implies
            #[trigger] part2_precinct_decoder_planes(actual)[i] == #[trigger] part2_precinct_decoder_planes(baseline)[i] by {
            let a = actual[i].decoders;
            let b = baseline[i].decoders;
            let project = |d: Tier1DecoderState| d.plane;
            let x = terminal_precinct_live(actual[i]).decoders;
            let y = terminal_precinct_live(baseline[i]).decoders;
            assert(x == y);
            assert(x.len() == a.len());
            assert(y.len() == b.len());
            assert forall|j:int| 0 <= j < a.len() implies
                (#[trigger] a[j]).plane == (#[trigger] b[j]).plane by {};
            assert(a.map_values(project) =~= b.map_values(project));
        };
    };
}

pub(crate) proof fn terminal_tile_keep_rows(
    layers: nat, actual: Part1TilePacketExecution, baseline: Part1TilePacketExecution,
    after: Part1TilePacketProgress,
)
    requires terminal_tile_related(layers, actual, baseline),
        terminal_seen_extends(actual.progress.seen, after.seen),
    ensures terminal_tile_related(layers, Part1TilePacketExecution { progress: after, ..actual },
        Part1TilePacketExecution { progress: after, ..baseline }),
{
    assert forall|i: int| 0 <= i < actual.precincts.len() implies {
        let a = #[trigger] actual.precincts[i];
        let b = #[trigger] baseline.precincts[i];
        if terminal_precinct_row(after.seen, layers, i as nat) { terminal_precinct_related(a, b) }
        else { a == b }
    } by {
        if terminal_precinct_row(actual.progress.seen, layers, i as nat) {
            terminal_seen_row_monotone(actual.progress.seen, after.seen, layers, i as nat);
        }
    };
}

pub(crate) proof fn terminal_precinct_value_tile_related(
    terminal: bool, params: Part1TilePacketParameters, part: Part2OwnedTilePart, p: Part1TilePacketProgress,
    coordinate: crate::packet::PacketCoordinate, expected: Option<u32>, precinct: Part1PacketPrecinctState,
)
    ensures {
        let a = terminal_tile_precinct_value(terminal, params, part, p, coordinate, expected, precinct);
        let b = part1_tile_precinct_packet_owned(params, part, p, coordinate, expected, precinct);
        a.0 == b.0 && (if terminal { terminal_precinct_related(a.1, b.1) } else { a.1 == b.1 })
    },
{
    if terminal && p.current_tile_part < params.input.packed.len()
        && (params.selection.is_none() || (coordinate.component as nat) < params.selection.unwrap().len()) {
        let layered = part1_precinct_context_layer(precinct, coordinate.layer);
        let decode = match params.selection { None => true, Some(counts) => coordinate.resolution < counts[coordinate.component as int] };
        if decode {
            terminal_precinct_value_related(layered, part, p.offset, params.input.packed[p.current_tile_part as int],
                p.packed_offset, expected, (p.packets & 65535u64) as u16, decode, params.caps.blocks, params.caps.header,
                part2_legacy_caps(params.caps.passes, params.caps.bytes, params.caps.input, params.caps.work));
        }
    }
}

pub(crate) proof fn terminal_tile_packet_related(
    params: Part1TilePacketParameters, actual: Part1TilePacketExecution, baseline: Part1TilePacketExecution,
    coordinate: crate::packet::PacketCoordinate,
)
    requires terminal_tile_related(params.grid.layers as nat, actual, baseline), coordinate.layer < params.grid.layers,
    ensures {
        let a = terminal_tile_packet_value(params, actual, coordinate);
        let b = part1_tile_packet(params, baseline, coordinate);
        a.0 == b.0 && (a.0.is_ok() ==> terminal_tile_related(params.grid.layers as nat, a.1, b.1))
            && a.1.progress.remaining_packets == actual.progress.remaining_packets
            && a.1.progress.iterator == actual.progress.iterator
    },
{
    let layers = params.grid.layers as nat;
    match part2_plane_tile_packet_admit(params, actual, coordinate) {
        Part2PlaneTileAdmission::Return(value) => {
            terminal_tile_keep_rows(layers, actual, baseline, value.1.progress);
        }
        Part2PlaneTileAdmission::Packet { state: after, part, index, seen, expected } => {
            terminal_tile_active_equal(layers, actual, baseline, index, seen, coordinate.layer as nat);
            let terminal = terminal_precinct_last_slot(after.progress.seen, layers, index as nat, seen, coordinate.layer as nat);
            let input = after.precincts[index as int];
            terminal_precinct_value_tile_related(terminal, params, part, after.progress, coordinate, expected, input);
            let a = terminal_tile_packet_value(params, actual, coordinate);
            let b = part1_tile_packet(params, baseline, coordinate);
            if a.0.is_ok() {
                terminal_seen_mark(actual.progress.seen, seen);
                if terminal {
                    terminal_seen_close(actual.progress.seen, layers, index as nat, seen, coordinate.layer as nat);
                }
                terminal_tile_keep_rows(layers, actual, baseline, a.1.progress);
                assert forall|i: int| 0 <= i < a.1.precincts.len() implies {
                    let row_a = #[trigger] a.1.precincts[i];
                    let row_b = #[trigger] b.1.precincts[i];
                    if terminal_precinct_row(a.1.progress.seen, layers, i as nat) { terminal_precinct_related(row_a, row_b) }
                    else { row_a == row_b }
                } by {
                    if i != index {
                        assert(a.1.precincts[i] == actual.precincts[i]);
                        assert(b.1.precincts[i] == baseline.precincts[i]);
                    }
                };
            }
        }
    }
}

pub(crate) proof fn terminal_tile_value_related(
    params: Part1TilePacketParameters, actual: Part1TilePacketExecution, baseline: Part1TilePacketExecution,
)
    requires terminal_tile_related(params.grid.layers as nat, actual, baseline),
        terminal_iterator_grid(actual.progress.iterator, params.grid),
    ensures {
        let a = terminal_tile_value(params, actual);
        let b = part1_tile_run(params, baseline);
        a.0 == b.0 && (a.0.is_ok() ==> terminal_tile_related(params.grid.layers as nat, a.1, b.1))
    },
    decreases actual.progress.remaining_packets,
{
    reveal(part1_tile_run);
    reveal(terminal_tile_value);
    let layers = params.grid.layers as nat;
    terminal_boundary_frame(params, actual.progress);
    let boundary = part1_tile_boundary(params, actual.progress);
    terminal_iterator_bound(boundary.1.iterator, params.grid);
    match part2_plane_tile_run_admit(params, actual) {
        Part2PlaneTileStep::Return(value) => {
            if value.0.is_ok() { terminal_tile_keep_rows(layers, actual, baseline, value.1.progress); }
        }
        Part2PlaneTileStep::Continue(after) => {
            if after.progress.seen != actual.progress.seen {
                let step = part1_progression_iterator_next(boundary.1.iterator);
                let slot = (part1_tile_packet_slot(params.grid, (step.0->Ok_0).unwrap())->Ok_0).1;
                terminal_seen_mark(actual.progress.seen, slot);
            }
            terminal_tile_keep_rows(layers, actual, baseline, after.progress);
            terminal_tile_value_related(params, after, Part1TilePacketExecution { progress: after.progress, ..baseline });
        }
        Part2PlaneTileStep::Packet(coordinate, after) => {
            let other = Part1TilePacketExecution { progress: after.progress, ..baseline };
            terminal_tile_keep_rows(layers, actual, baseline, after.progress);
            terminal_tile_packet_related(params, after, other, coordinate);
            let a = terminal_tile_packet_value(params, after, coordinate);
            let b = part1_tile_packet(params, other, coordinate);
            if a.0.is_ok() { terminal_tile_value_related(params, a.1, b.1); }
        }
    }
}

pub(crate) proof fn terminal_tile_precinct_observed(
    terminal: bool, params: Part1TilePacketParameters, part: Part2OwnedTilePart,
    progress: Part1TilePacketProgress, coordinate: crate::packet::PacketCoordinate, expected: Option<u32>,
    precinct: Part1PacketPrecinctState, decode: bool, result: Part1PrecinctPayloadResult,
)
    requires progress.current_tile_part < params.input.packed.len(),
        params.selection.is_none() || (coordinate.component as nat) < params.selection.unwrap().len(),
        decode == match params.selection { None => true, Some(c) => coordinate.resolution < c[coordinate.component as int] },
        terminal_precinct_mode_frame(terminal,part1_precinct_context_layer(precinct, coordinate.layer),
            part, progress.offset, params.input.packed[progress.current_tile_part as int], progress.packed_offset, expected,
            (progress.packets & 65535u64) as u16, decode, params.caps.blocks, params.caps.header,
            part2_legacy_caps(params.caps.passes, params.caps.bytes, params.caps.input, params.caps.work), result),
    ensures terminal_tile_precinct_frame(terminal,params, part, progress, coordinate, expected, precinct, result),
{
    let state = part1_precinct_context_layer(precinct, coordinate.layer);
    let packed = params.input.packed[progress.current_tile_part as int];
    let sequence = (progress.packets & 65535u64) as u16;
    let c = params.caps;
    if terminal && decode {
        part2_tier1_storage_eta(|calls| terminal_precinct_run(state, part, progress.offset, packed,
            progress.packed_offset, expected, sequence, decode, c.blocks, c.header,
            part2_legacy_caps(c.passes, c.bytes, c.input, c.work), calls), Ok(result));
    } else {
        part2_plane_tile_precinct_observed(params, part, progress, coordinate, expected, precinct, decode, result);
        if terminal {
            part2_tier1_storage_eta(|calls| part2_plane_precinct_run(state, part, progress.offset, packed,
                progress.packed_offset, expected, sequence, decode, c.blocks, c.header, c.passes, c.bytes, c.input, c.work, calls), Ok(result));
        }
    }
}

pub(crate) proof fn terminal_tile_packet_observed(
    params: Part1TilePacketParameters, initial: Part1TilePacketExecution, coordinate: crate::packet::PacketCoordinate,
    before: Part1TilePacketExecution, part: Part2OwnedTilePart, index: usize, slot: usize, expected: Option<u32>,
    packet: Part1PrecinctPayloadResult,
)
    requires part2_plane_tile_packet_admit(params, initial, coordinate) ==
            (Part2PlaneTileAdmission::Packet { state: before, part, index, seen: slot, expected }),
        terminal_tile_precinct_frame(terminal_precinct_last_slot(before.progress.seen, params.grid.layers as nat,
            index as nat, slot, coordinate.layer as nat),
            params, part, before.progress, coordinate, expected, before.precincts[index as int], packet),
    ensures terminal_tile_packet_frame(true,params, initial, coordinate,
        part2_plane_tile_packet_finish(before, index, slot, expected, packet)),
{
    let terminal = terminal_precinct_last_slot(before.progress.seen, params.grid.layers as nat, index as nat, slot, coordinate.layer as nat);
    let precinct = before.precincts[index as int];
    if !terminal {
        reveal(part2_plane_tile_precinct_result);
        part2_tier1_storage_eta(|calls| part2_plane_tile_precinct_run(params,part,before.progress,coordinate,expected,precinct,calls),Ok(packet));
    }
    let result = part2_plane_tile_packet_finish(before, index, slot, expected, packet);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(
        |calls| terminal_tile_precinct_run(terminal, params, part, before.progress, coordinate, expected, precinct, calls),
        |value: Part1PrecinctPayloadResult, rest| Some((Ok(part2_plane_tile_packet_finish(before, index, slot, expected, value)), rest)),
        Ok(packet), Ok(result),
    );
}

pub(crate) proof fn terminal_tile_packet_pure(
    params: Part1TilePacketParameters, state: Part1TilePacketExecution, coordinate: crate::packet::PacketCoordinate,
)
    ensures match part2_plane_tile_packet_admit(params, state, coordinate) {
        Part2PlaneTileAdmission::Return(output) => terminal_tile_packet_frame(true,params, state, coordinate, output),
        _ => true,
    },
{
    if let Part2PlaneTileAdmission::Return(output) = part2_plane_tile_packet_admit(params, state, coordinate) {
        part2_tier1_storage_pure(Ok(output));
    }
}

pub(crate) open spec fn terminal_tile_finish_projection(
    params: Part1TilePacketParameters, effect: (Result<(), crate::DecodeError>, Part1TilePacketExecution),
) -> Result<(crate::packet::TilePacketDecode, Seq<Seq<Tier1RawPlane>>), crate::DecodeError> {
    match effect.0 {
        Err(error) => Err(error),
        Ok(()) => match part1_tile_finish(params, effect.1.progress).0 {
            Err(error) => Err(error),
            Ok(packet) => Ok((packet, part2_precinct_decoder_planes(effect.1.precincts))),
        },
    }
}

pub(crate) open spec fn terminal_tile_projected_value(
    effect: (Result<crate::packet::TilePacketDecode, crate::DecodeError>, Seq<Part1PacketPrecinctState>),
) -> Result<(crate::packet::TilePacketDecode, Seq<Seq<Tier1RawPlane>>), crate::DecodeError> {
    match effect.0 {
        Err(error) => Err(error),
        Ok(packet) => Ok((packet, part2_precinct_decoder_planes(effect.1))),
    }
}

pub(crate) open spec fn terminal_tile_call_run(
    params: Part1TilePacketParameters, initial: Part1TilePacketExecution,
    calls: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(crate::packet::TilePacketDecode, Seq<Seq<Tier1RawPlane>>)> {
    if calls.len() > 0 && calls[0] is FinalTilePlaneCalls {
        match calls[0] {
            Part2JpipSnapshotEvent::FinalTilePlaneCalls {params: observed, initial: before, calls: tape} => {
                if observed != params || before != initial { None }
                else {
                    match terminal_tile_run(params, initial, tape) {
                        Some((Ok(effect), remaining)) if remaining.len() == 0 =>
                            Some((terminal_tile_finish_projection(params, effect), calls.drop_first())),
                        _ => None,
                    }
                }
            },
            _ => None,
        }
    } else {
        match part2_tile_plane_calls_run(params, initial, calls) {
            None => None,
            Some((Err(error), rest)) => Some((Err(error), rest)),
            Some((Ok(effect), rest)) => Some((terminal_tile_finish_projection(params, effect), rest)),
        }
    }
}

pub(crate) open spec fn terminal_packet_value_run(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, calls: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(crate::packet::TilePacketDecode, Seq<Seq<Tier1RawPlane>>)> {
    part2_jpip_snapshot_bind(part2_packet_input_run(parts, grid, precincts, selection, limits, calls),
        |input: Part1TilePacketPreparation, rest| {
            let params = part2_packet_parameters(parts, grid, input, selection, limits);
            part2_jpip_snapshot_bind(part2_progress_initial_run(params, rest), |progress: Part1TilePacketProgress, tail|
                terminal_tile_call_run(params, Part1TilePacketExecution { progress, precincts }, tail))
        })
}

pub(crate) open spec fn terminal_packet_value_frame(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
    output: Result<(crate::packet::TilePacketDecode, Seq<Seq<Tier1RawPlane>>), crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| terminal_packet_value_run(parts, grid, precincts, selection, limits, events), output)
}

pub(crate) proof fn terminal_tile_call_observed(
    params: Part1TilePacketParameters, initial: Part1TilePacketExecution,
    effect: (Result<(), crate::DecodeError>, Part1TilePacketExecution),
)
    requires terminal_tile_mode_frame(true,params, initial, effect),
    ensures part2_cold_framed(|calls| terminal_tile_call_run(params, initial, calls), terminal_tile_finish_projection(params, effect)),
{
    let child = |calls| terminal_tile_run(params, initial, calls);
    let tape = choose|calls| #[trigger] part2_tier1_storage_prefix(child, calls, Ok(effect));
    let event = seq![Part2JpipSnapshotEvent::FinalTilePlaneCalls { params, initial, calls: tape }];
    part2_tier1_storage_at(child, tape, Ok(effect), Seq::empty());
    assert(tape + Seq::empty() =~= tape);
    assert forall|tail: Seq<Part2JpipSnapshotEvent>| terminal_tile_call_run(params, initial, event + tail)
        == Some((terminal_tile_finish_projection(params, effect), tail)) by {
        assert((event + tail).drop_first() =~= tail);
    };
    assert(part2_cold_prefix(|calls| terminal_tile_call_run(params, initial, calls), event, terminal_tile_finish_projection(params, effect)));
}

pub(crate) proof fn terminal_packet_ordinary_projection(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
    output: Result<(crate::packet::TilePacketDecode, Seq<Part1PacketPrecinctState>), crate::DecodeError>,
)
    requires part2_cold_framed(|calls| part2_packet_value_run(parts,grid,precincts,selection,limits,calls),output),
    ensures terminal_packet_value_frame(parts, grid, precincts, selection, limits,
        match output {
            Err(error) => Err(error),
            Ok((packet, precincts)) => Ok((packet, part2_precinct_decoder_planes(precincts))),
        }),
{
    let old = |calls| part2_packet_value_run(parts, grid, precincts, selection, limits, calls);
    let new = |calls| terminal_packet_value_run(parts, grid, precincts, selection, limits, calls);
    let prefix = part2_cold_witness(old, output);
    let value = match output {
        Err(error) => Err(error),
        Ok((packet, precincts)) => Ok((packet, part2_precinct_decoder_planes(precincts))),
    };
    assert forall|tail| new(prefix + tail) == Some((value, tail)) by {
        let calls = prefix + tail;
        part2_cold_prefix_at(old, prefix, output, tail);
        match part2_packet_input_run(parts, grid, precincts, selection, limits, calls) {
            Some((Ok(input), rest)) => {
                let params = part2_packet_parameters(parts, grid, input, selection, limits);
                if let Some((Ok(progress), events)) = part2_progress_initial_run(params, rest) {
                    assert(events.len() > 0 && events[0] is TilePlaneCalls);
                    let init = Part1TilePacketExecution {progress, precincts};
                    let executed = part2_tile_plane_calls_run(params, init, events);
                    assert(executed.is_some());
                }
            },
            _ => {},
        }
    };
    assert(part2_cold_prefix(new, prefix, value));
}

pub(crate) proof fn terminal_packet_projection_from_stages(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
    input: Result<Part1TilePacketPreparation, crate::DecodeError>,
    progress: Result<Part1TilePacketProgress, crate::DecodeError>,
    run: Option<(Result<(), crate::DecodeError>, Part1TilePacketExecution)>,
)
    requires part2_packet_input_result(parts, grid, precincts, selection, limits, input),
        input.is_ok() ==> part2_progress_initial_result(part2_packet_parameters(parts, grid, input->Ok_0, selection, limits), progress),
        input.is_ok() && progress.is_ok() ==> run.is_some() && terminal_tile_mode_frame(true,part2_packet_parameters(parts, grid, input->Ok_0, selection, limits),
            Part1TilePacketExecution { progress: progress->Ok_0, precincts }, run.unwrap()),
    ensures terminal_packet_value_frame(parts, grid, precincts, selection, limits,
        match input {
            Err(error) => Err(error),
            Ok(input) => match progress {
                Err(error) => Err(error),
                Ok(_) => terminal_tile_finish_projection(part2_packet_parameters(parts, grid, input, selection, limits), run.unwrap()),
            },
        }),
{
    reveal(part2_packet_input_result);
    reveal(part2_progress_initial_result);
    let before = |calls| part2_packet_input_run(parts, grid, precincts, selection, limits, calls);
    let root = |calls| terminal_packet_value_run(parts, grid, precincts, selection, limits, calls);
    if let Ok(input) = input {
        let params = part2_packet_parameters(parts, grid, input, selection, limits);
        let child = |calls| part2_progress_initial_run(params, calls);
        let next = |p: Part1TilePacketProgress, calls| terminal_tile_call_run(params, Part1TilePacketExecution {progress:p, precincts}, calls);
        let after = |input: Part1TilePacketPreparation, calls| {
            let params = part2_packet_parameters(parts, grid, input, selection, limits);
            part2_jpip_snapshot_bind(part2_progress_initial_run(params, calls), |p: Part1TilePacketProgress, rest|
                terminal_tile_call_run(params, Part1TilePacketExecution {progress:p, precincts}, rest))
        };
        let result = match progress { Err(error) => Err(error), Ok(_) => terminal_tile_finish_projection(params, run.unwrap()) };
        if let Ok(p) = progress {
            terminal_tile_call_observed(params, Part1TilePacketExecution {progress:p, precincts}, run.unwrap());
            part2_decode_eta(|calls| terminal_tile_call_run(params,Part1TilePacketExecution {progress:p,precincts},calls),result);
            assert(part2_cold_framed(|calls| next(p,calls),result));
        }
        part2_cold_bind(child, next, progress, result);
        part2_decode_eta(|calls| part2_jpip_snapshot_bind(child(calls), next), result);
        part2_cold_bind(before, after, Ok(input), result);
    } else {
        part2_cold_bind(before, |input: Part1TilePacketPreparation, calls| {
            let params = part2_packet_parameters(parts, grid, input, selection, limits);
            part2_jpip_snapshot_bind(part2_progress_initial_run(params, calls), |p: Part1TilePacketProgress, rest|
                terminal_tile_call_run(params, Part1TilePacketExecution {progress:p, precincts}, rest))
        }, input, Err(input->Err_0));
    }
}

pub(crate) proof fn terminal_finish_equivalence(
    params: Part1TilePacketParameters, initial: Part1TilePacketExecution,
    observed: (Result<(), crate::DecodeError>, Part1TilePacketExecution),
)
    requires observed == terminal_tile_value(params, initial),
        terminal_iterator_grid(initial.progress.iterator, params.grid),
    ensures terminal_tile_finish_projection(params, observed) ==
        terminal_tile_projected_value(part2_packet_plane_finish(params, part1_tile_run(params, initial))),
{
    let baseline = part1_tile_run(params, initial);
    terminal_tile_value_related(params, initial, initial);
    if observed.0.is_ok() {
        let a = observed.1.precincts;
        let b = baseline.1.precincts;
        assert forall|i: int| 0 <= i < a.len() implies
            terminal_precinct_related(#[trigger] a[i], #[trigger] b[i]) by {};
        terminal_project_planes(a, b);
    }
}

pub(crate) open spec fn terminal_mode_part_run(
    final_image: bool, params: Part1TilePacketParameters,
    state: Part1TilePacketExecution, coordinate: crate::packet::PacketCoordinate,
    calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<(Result<(), crate::DecodeError>, Part1TilePacketExecution)> {
    if final_image { terminal_tile_packet_run(params, state, coordinate, calls) }
    else { part2_plane_tile_packet_run(params, state, coordinate, calls) }
}

pub(crate) open spec fn terminal_mode_after_packet(
    final_image: bool, params: Part1TilePacketParameters, budget: u64,
    packet: (Result<(), crate::DecodeError>, Part1TilePacketExecution), calls: Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<(Result<(), crate::DecodeError>, Part1TilePacketExecution)> {
    if final_image { terminal_tile_after_packet(params, budget, packet, calls) }
    else { part2_plane_tile_after_packet(params, budget, packet, calls) }
}

pub(crate) proof fn terminal_tile_mode_packet_cut(
    final_image: bool, params: Part1TilePacketParameters, s: Part1TilePacketExecution,
    coordinate: crate::packet::PacketCoordinate, after: Part1TilePacketExecution,
)
    requires part2_plane_tile_run_admit(params, s) == Part2PlaneTileStep::Packet(coordinate, after),
    ensures forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger]
        terminal_tile_mode_run(final_image,params, s, calls) ==
        part2_tier1_storage_bind(
            terminal_mode_part_run(final_image,params, after, coordinate, calls),
            |packet: (Result<(), crate::DecodeError>, Part1TilePacketExecution), rest|
                terminal_mode_after_packet(final_image,params, s.progress.remaining_packets, packet, rest)),
{
    reveal(terminal_tile_run);
    reveal(part2_plane_tile_run);
    assert forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger]
        terminal_tile_mode_run(final_image,params, s, calls) ==
        part2_tier1_storage_bind(
            terminal_mode_part_run(final_image,params,after,coordinate,calls),
            |packet:(Result<(),crate::DecodeError>,Part1TilePacketExecution),rest|
                terminal_mode_after_packet(final_image,params,s.progress.remaining_packets,packet,rest)) by {
        if final_image {
            assert(terminal_tile_run(params,s,calls) == part2_tier1_storage_bind(
                terminal_tile_packet_run(params,after,coordinate,calls),
                |packet:(Result<(),crate::DecodeError>,Part1TilePacketExecution),rest|
                    terminal_tile_after_packet(params,s.progress.remaining_packets,packet,rest)));
        } else {
            part2_plane_tile_run_packet_step(params,s,coordinate,after);
        }
        match terminal_mode_part_run(final_image,params,after,coordinate,calls) {
            None=>{},
            Some((Err(_),_))=>{},
            Some((Ok(value),tail))=>{
                assert(terminal_mode_after_packet(final_image,params,s.progress.remaining_packets,value,tail)
                    == if final_image {terminal_tile_after_packet(params,s.progress.remaining_packets,value,tail)}
                        else {part2_plane_tile_after_packet(params,s.progress.remaining_packets,value,tail)});
            }
        }
    };
}

pub(crate) proof fn terminal_tile_mode_next_cut(
    final_image: bool, params: Part1TilePacketParameters, s: Part1TilePacketExecution,
    after: Part1TilePacketExecution,
)
    requires part2_plane_tile_run_admit(params, s) == Part2PlaneTileStep::Continue(after),
        after.progress.remaining_packets < s.progress.remaining_packets,
    ensures forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger]
        terminal_tile_mode_run(final_image,params, s, calls) ==
        terminal_tile_mode_run(final_image,params, after, calls),
{
    reveal(terminal_tile_run);
    reveal(part2_plane_tile_run);
}

pub(crate) proof fn terminal_tile_mode_return_cut(
    final_image: bool, params: Part1TilePacketParameters, s: Part1TilePacketExecution,
    result: (Result<(), crate::DecodeError>, Part1TilePacketExecution),
)
    requires part2_plane_tile_run_admit(params, s) == Part2PlaneTileStep::Return(result),
    ensures forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger]
        terminal_tile_mode_run(final_image,params, s, calls) == Some((Ok(result), calls)),
{
    reveal(terminal_tile_run);
    reveal(part2_plane_tile_run);
}

pub(crate) proof fn terminal_tile_mode_join(
    final_image: bool, params: Part1TilePacketParameters, s: Part1TilePacketExecution,
    root: spec_fn(Seq<Part2Tier1StorageEvent>) -> Part2Tier1Run<(Result<(), crate::DecodeError>, Part1TilePacketExecution)>,
    output: (Result<(), crate::DecodeError>, Part1TilePacketExecution),
)
    requires part2_tier1_storage_framed(root, Ok(output)),
        forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger] root(calls) ==
            terminal_tile_mode_run(final_image,params, s, calls),
    ensures terminal_tile_mode_frame(final_image,params, s, output),
{
    reveal(part2_plane_tile_run_result);
    part2_tier1_storage_eta(root, Ok(output));
}

pub(crate) proof fn terminal_tile_mode_return_observed(
    mode: bool, params: Part1TilePacketParameters,
    initial: Part1TilePacketExecution, current: Part1TilePacketExecution,
    root: spec_fn(Seq<Part2Tier1StorageEvent>) -> Part2Tier1Run<(Result<(), crate::DecodeError>, Part1TilePacketExecution)>,
    prefix: Seq<Part2Tier1StorageEvent>, output: (Result<(), crate::DecodeError>, Part1TilePacketExecution),
)
    requires
        forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger] root(calls) == terminal_tile_mode_run(mode,params, initial, calls),
        part2_tier1_phase(root, prefix, |calls| terminal_tile_mode_run(mode,params, current, calls)),
        part2_plane_tile_run_admit(params, current) == Part2PlaneTileStep::Return(output),
    ensures terminal_tile_mode_frame(mode,params, initial, output),
        terminal_tile_mode_value(mode,params,current)==output,
{
    reveal(terminal_tile_value);
    reveal(part1_tile_run);
    terminal_tile_mode_return_cut(mode,params, current, output);
    part2_tier1_prefix_finish(root, prefix, Ok(output));
    terminal_tile_mode_join(mode,params, initial, root, output);
}

pub(crate) proof fn terminal_tile_relative_values(
    mode: bool, params: Part1TilePacketParameters, current: Part1TilePacketExecution,
    before: Part1TilePacketExecution, coordinate: crate::packet::PacketCoordinate,
    result: (Result<(),crate::DecodeError>,Part1TilePacketExecution),
)
    requires part2_plane_tile_run_admit(params,current)==Part2PlaneTileStep::Packet(coordinate,before),
        result == if mode {terminal_tile_packet_value(params,before,coordinate)}
            else {part1_tile_packet(params,before,coordinate)},
        result.0.is_ok() ==> result.1.progress.remaining_packets < current.progress.remaining_packets,
    ensures terminal_tile_mode_value(mode,params,current)==
        if result.0.is_ok() {terminal_tile_mode_value(mode,params,result.1)} else {result},
{
    reveal(part1_tile_run);
    reveal(terminal_tile_value);
}

pub(crate) proof fn terminal_tile_mode_continue_values(
    mode: bool, params: Part1TilePacketParameters, current: Part1TilePacketExecution,
    after: Part1TilePacketExecution,
)
    requires part2_plane_tile_run_admit(params,current)==Part2PlaneTileStep::Continue(after),
        after.progress.remaining_packets < current.progress.remaining_packets,
    ensures terminal_tile_mode_value(mode,params,current)==terminal_tile_mode_value(mode,params,after),
{
    reveal(terminal_tile_value);
    reveal(part1_tile_run);
}

pub(crate) proof fn terminal_tile_mode_step_observed(
    mode: bool, model: Part1TilePacketParameters, initial: Part1TilePacketExecution,
    current: Part1TilePacketExecution, before: Part1TilePacketExecution,
    coordinate: crate::packet::PacketCoordinate, observed: (Result<(), crate::DecodeError>, Part1TilePacketExecution),
    root: spec_fn(Seq<Part2Tier1StorageEvent>) -> Part2Tier1Run<(Result<(), crate::DecodeError>, Part1TilePacketExecution)>,
    prefix: Seq<Part2Tier1StorageEvent>,
) -> (joined: Seq<Part2Tier1StorageEvent>)
    requires
        forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger] root(calls) == terminal_tile_mode_run(mode,model,initial,calls),
        part2_tier1_phase(root,prefix,|calls|terminal_tile_mode_run(mode,model,current,calls)),
        part2_plane_tile_run_admit(model,current)==Part2PlaneTileStep::Packet(coordinate,before),
        observed.0.is_ok() ==> observed.1.progress.remaining_packets < current.progress.remaining_packets,
        terminal_exact_observed(observed,|effect|terminal_tile_packet_frame(mode,model,before,coordinate,effect)),
    ensures
        observed.0.is_ok() ==> part2_tier1_phase(root,joined,|calls|terminal_tile_mode_run(mode,model,observed.1,calls)),
        observed.0.is_err() ==> terminal_exact_observed(observed,|effect|terminal_tile_mode_frame(mode,model,initial,effect)),
        !mode && observed.0.is_err() ==>
            terminal_exact_observed(observed,|effect|part2_plane_tile_run_result(model,initial,effect)),
{
    let result=terminal_exact_witness(observed,|effect|terminal_tile_packet_frame(mode,model,before,coordinate,effect));
    if !mode {
        let budget = current.progress.remaining_packets;
        part2_plane_tile_run_packet_step(model,current,coordinate,before);
        assert forall|calls: Seq<Part2Tier1StorageEvent>| #[trigger] root(prefix+calls)
            == part2_tier1_storage_bind(part2_plane_tile_packet_run(model,before,coordinate,calls),
                |packet:(Result<(),crate::DecodeError>,Part1TilePacketExecution),rest|
                    part2_plane_tile_after_packet(model,budget,packet,rest)) by {
            assert(root(prefix+calls)==part2_plane_tile_run(model,current,calls));
        };
        let extended = part2_plane_tile_prefix_observed(model,initial,before,coordinate,budget,root,prefix,result);
        if result.0.is_err() {
            let frame = |effect| part2_plane_tile_run_result(model,initial,effect);
            terminal_exact_publish(observed,result,frame);
            assert(frame =~= (|effect| terminal_tile_mode_frame(mode,model,initial,effect)));
        } else {
            assert(result == observed);
            assert((|calls| part2_plane_tile_run(model,result.1,calls))
                =~= (|calls| terminal_tile_mode_run(mode,model,observed.1,calls)));
        }
        return extended;
    }
    let child = |calls|terminal_mode_part_run(mode,model,before,coordinate,calls);
    let next = |packet: (Result<(),crate::DecodeError>,Part1TilePacketExecution),rest|
        terminal_mode_after_packet(mode,model,current.progress.remaining_packets,packet,rest);
    terminal_tile_mode_packet_cut(mode,model,current,coordinate,before);
    assert forall|calls| #[trigger] root(prefix+calls)==part2_tier1_storage_bind(child(calls),next) by {};
    part2_tier1_storage_eta(|calls|terminal_tile_packet_run(model,before,coordinate,calls),Ok(result));
    assert(part2_tier1_storage_framed(child,Ok(result)));
    let joined=part2_tier1_prefix_advance(root,child,next,prefix,result);
    if observed.0.is_err() {
        part2_tier1_prefix_finish(root,joined,Ok(result));
        terminal_tile_mode_join(mode,model,initial,root,result);
        terminal_exact_publish(observed,result,|effect|terminal_tile_mode_frame(mode,model,initial,effect));
    } else {
        assert(result == observed);
        assert(result.1.progress.remaining_packets < current.progress.remaining_packets);
        assert forall|calls| #[trigger] root(joined+calls)==terminal_tile_mode_run(mode,model,observed.1,calls) by {
            assert(root(joined+calls)==next(result,calls));
            reveal_with_fuel(terminal_tile_after_packet,2);
            reveal_with_fuel(terminal_tile_run,1);
            assert(terminal_tile_after_packet(model,current.progress.remaining_packets,result,calls)
                == terminal_tile_run(model,result.1,calls));
        };
    }
    joined
}

}
