//! Actual caller-planned progressive availability and full/selected update Results.

use super::*;

verus! {

pub type Part2JpipProgressiveDecoder = (Part2JpipPlan, u16);
pub type Part2JpipProgressiveUpdate = (
    crate::jpip::JpipProgressiveStatus, u16, u16, Seq<Part2JpipMissing>, Option<Part1DecodedTypedImage>,
);

pub type Part2JpipAutomaticPacket = (Part2JpipDatabin, Option<Seq<u8>>, u64, bool, u16, u16);
pub type Part2JpipAutomaticTilePart = (Seq<u8>, Seq<Part2JpipAutomaticPacket>, bool, bool);

pub type Part2JpipAutomaticProgressiveDecoder = (u64, u16);
pub type Part2JpipAutomaticProgressiveResult = (
    Result<Part2JpipProgressiveUpdate, crate::DecodeError>, Part2JpipAutomaticProgressiveDecoder, Part2JpipCache,
);

pub closed spec fn part2_jpip_automatic_progressive_normal_run(
    cache: Part2JpipCache, decoder: Part2JpipAutomaticProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>, components: Seq<u16>,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Option<(Part2JpipAutomaticProgressiveResult, Seq<Part2JpipSnapshotEvent>)> {
    let input = Part2JpipSnapshotInput {
        cache, stream: decoder.0,
        selected: match selection { None => None, Some(value) => Some(crate::options::decode_selection_view(value)) },
        components, limits: crate::options::decode_options_limits(options),
    };
    match part2_jpip_snapshot_run(input, events) {
        None => None,
        Some((Err(error), tail)) => Some(((Err(error), decoder, cache), tail)),
        Some((Ok((None, missing)), tail)) => Some(((Ok((
            crate::jpip::JpipProgressiveStatus::WaitingForData, decoder.1, 0, missing, None)), decoder, cache), tail)),
        Some((Ok((Some(snapshot), _outer_missing)), tail)) => {
            let previous = decoder.1;
            let available = snapshot.1;
            let maximum = snapshot.2;
            if !valid_jpip_progressive_update(previous as nat, available as nat, maximum as nat) {
                Some(((Err(part2_jpip_plan_invalid(0)), decoder, cache), tail))
            } else if available <= previous {
                Some(((Ok((if available == maximum { crate::jpip::JpipProgressiveStatus::Complete }
                    else { crate::jpip::JpipProgressiveStatus::WaitingForData },
                    previous, available, snapshot.3, None)), decoder, cache), tail))
            } else {
                match part2_decode_raw_codestream(snapshot.0, crate::options::decode_options_limits(options), selection) {
                    Err(error) => Some(((Err(error), decoder, cache), tail)),
                    Ok(image) => Some(((Ok((
                        if available == maximum { crate::jpip::JpipProgressiveStatus::Complete }
                        else { crate::jpip::JpipProgressiveStatus::QualityAdvanced },
                        previous, available, snapshot.3, Some(image))), (decoder.0, available), cache), tail)),
                }
            }
        },
    }
}

pub open spec fn part2_jpip_automatic_progressive_update_result(
    cache: Part2JpipCache, decoder: Part2JpipAutomaticProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>, components: Seq<u16>,
    result: Part2JpipAutomaticProgressiveResult,
) -> bool {
    exists|events: Seq<Part2JpipAutomaticEvent>|
        part2_jpip_automatic_progressive_run(cache, decoder, options, selection, components, events)
            == Some((result, Seq::empty()))
}

pub(crate) proof fn part2_jpip_automatic_progressive_normal_run_unfold(
    cache: Part2JpipCache, decoder: Part2JpipAutomaticProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>, components: Seq<u16>,
    events: Seq<Part2JpipSnapshotEvent>,
)
    ensures part2_jpip_automatic_progressive_normal_run(cache, decoder, options, selection, components, events)
        == {
            let input = Part2JpipSnapshotInput {
                cache, stream: decoder.0,
                selected: match selection { None => None, Some(value) => Some(crate::options::decode_selection_view(value)) },
                components, limits: crate::options::decode_options_limits(options),
            };
            match part2_jpip_snapshot_run(input, events) {
                None => None,
                Some((Err(error), tail)) => Some(((Err(error), decoder, cache), tail)),
                Some((Ok((None, missing)), tail)) => Some(((Ok((
                    crate::jpip::JpipProgressiveStatus::WaitingForData, decoder.1, 0, missing, None)), decoder, cache), tail)),
                Some((Ok((Some(snapshot), _outer_missing)), tail)) => {
                    let previous = decoder.1;
                    let available = snapshot.1;
                    let maximum = snapshot.2;
                    if !valid_jpip_progressive_update(previous as nat, available as nat, maximum as nat) {
                        Some(((Err(part2_jpip_plan_invalid(0)), decoder, cache), tail))
                    } else if available <= previous {
                        Some(((Ok((if available == maximum { crate::jpip::JpipProgressiveStatus::Complete }
                            else { crate::jpip::JpipProgressiveStatus::WaitingForData },
                            previous, available, snapshot.3, None)), decoder, cache), tail))
                    } else {
                        match part2_decode_raw_codestream(snapshot.0, crate::options::decode_options_limits(options), selection) {
                            Err(error) => Some(((Err(error), decoder, cache), tail)),
                            Ok(image) => Some(((Ok((
                                if available == maximum { crate::jpip::JpipProgressiveStatus::Complete }
                                else { crate::jpip::JpipProgressiveStatus::QualityAdvanced },
                                previous, available, snapshot.3, Some(image))), (decoder.0, available), cache), tail)),
                        }
                    }
                },
            }
        },
{
    reveal(part2_jpip_automatic_progressive_normal_run);
}

pub enum Part2JpipAutomaticEvent {
    Snapshot { calls: Seq<Part2JpipSnapshotEvent> },
    Transcode { calls: Seq<Part2JpipSnapshotEvent> },
    Image { calls: Seq<Part2JpipSnapshotEvent> },
}

pub(crate) type Part2JpipPlannedResult = (
    Result<Part2JpipProgressiveUpdate, crate::DecodeError>, Part2JpipProgressiveDecoder, Part2JpipCache,
);

pub(crate) open spec fn part2_jpip_planned_transcode_call(
    cache: Part2JpipCache, plan: Part2JpipPlan, available: u16, events: Seq<Part2JpipAutomaticEvent>,
) -> Option<(Result<Part2JpipTranscode, crate::DecodeError>, Seq<Part2JpipAutomaticEvent>)> {
    if events.len() == 0 { None } else {
        match events[0] {
            Part2JpipAutomaticEvent::Transcode { calls } =>
                match part2_jpip_transcode_cold_run(cache, plan, available, calls) {
                    Some((result, rest)) => if rest.len() == 0 { Some((result, events.drop_first())) } else { None },
                    None => None,
                },
            _ => None,
        }
    }
}

pub(crate) open spec fn part2_jpip_planned_image_frame(
    cache: Part2JpipCache, decoder: Part2JpipProgressiveDecoder, available: u16,
    missing: Seq<Part2JpipMissing>, decoded: Result<Part1DecodedTypedImage, crate::DecodeError>,
) -> Part2JpipPlannedResult {
    match decoded {
        Err(error) => (Err(error), decoder, cache),
        Ok(image) => (Ok((
            if available == decoder.0.3.len() as u16 { crate::jpip::JpipProgressiveStatus::Complete }
            else { crate::jpip::JpipProgressiveStatus::QualityAdvanced },
            decoder.1, available, missing, Some(image))), (decoder.0, available), cache),
    }
}

pub(crate) open spec fn part2_jpip_planned_cold_run(
    cache: Part2JpipCache, decoder: Part2JpipProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>,
    events: Seq<Part2JpipAutomaticEvent>,
) -> Option<(Part2JpipPlannedResult, Seq<Part2JpipAutomaticEvent>)> {
    let planned = decoder.0.3.len() as u16;
    match part2_jpip_progressive_availability(cache, decoder.0) {
        Err(error) => Some(((Err(error), decoder, cache), events)),
        Ok((available, missing)) => {
            if !valid_jpip_progressive_update(decoder.1 as nat, available as nat, planned as nat) {
                Some(((Err(part2_jpip_plan_invalid(0)), decoder, cache), events))
            } else if available <= decoder.1 {
                Some(((Ok((if available == planned { crate::jpip::JpipProgressiveStatus::Complete }
                    else { crate::jpip::JpipProgressiveStatus::WaitingForData },
                    decoder.1, available, missing, None)), decoder, cache), events))
            } else {
                match part2_jpip_planned_transcode_call(cache, decoder.0, available, events) {
                    None => None,
                    Some((Err(error), rest)) => Some(((Err(error), decoder, cache), rest)),
                    Some((Ok(transcoded), rest)) => match transcoded.2 {
                        None => Some(((Err(part2_jpip_cache_error(0, crate::MalformedKind::MissingRequiredStructure)), decoder, cache), rest)),
                        Some(bytes) => match part2_jpip_automatic_image_call(bytes, options, selection, rest) {
                            None => None,
                            Some((decoded, tail)) => Some((
                                part2_jpip_planned_image_frame(cache, decoder, available, missing, decoded), tail)),
                        },
                    },
                }
            }
        },
    }
}

pub closed spec fn part2_jpip_planned_cold_result(
    cache: Part2JpipCache, decoder: Part2JpipProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>, result: Part2JpipPlannedResult,
) -> bool {
    exists|events: Seq<Part2JpipAutomaticEvent>|
        part2_jpip_planned_cold_run(cache, decoder, options, selection, events)
            == Some((result, Seq::empty()))
}

pub(crate) proof fn part2_jpip_planned_cold_normal(
    cache: Part2JpipCache, decoder: Part2JpipProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>,
)
    ensures part2_jpip_planned_cold_result(cache, decoder, options, selection,
        (part2_jpip_progressive_update(cache, decoder, options, selection).0,
            part2_jpip_progressive_update(cache, decoder, options, selection).1, cache)),
{
    reveal(part2_jpip_planned_cold_result);
    let result = part2_jpip_progressive_update(cache, decoder, options, selection);
    let mut events: Seq<Part2JpipAutomaticEvent> = Seq::empty();
    if let Ok((available, missing)) = part2_jpip_progressive_availability(cache, decoder.0) {
        if valid_jpip_progressive_update(decoder.1 as nat, available as nat, (decoder.0.3.len() as u16) as nat)
            && available > decoder.1 {
            let transcoded = part2_jpip_transcode(cache, decoder.0, available);
            part2_jpip_transcode_cold_normal(cache, decoder.0, available);
            part2_jpip_transcode_cold_frames(cache, decoder.0, available, transcoded);
            let calls = part2_cold_witness(
                |events| part2_jpip_transcode_cold_run(cache, decoder.0, available, events), transcoded);
            events = seq![Part2JpipAutomaticEvent::Transcode { calls }];
            assert(events.drop_first() =~= Seq::empty());
            if let Ok((_, _, Some(bytes))) = transcoded {
                let decoded = part2_decode_raw_codestream(bytes, crate::options::decode_options_limits(options), selection);
                part2_decode_raw_cold_normal(bytes, crate::options::decode_options_limits(options), selection);
                part2_decode_raw_cold_frames(bytes, crate::options::decode_options_limits(options), selection, decoded);
                let image_calls = part2_cold_witness(
                    |events| part2_decode_raw_cold_run(bytes, crate::options::decode_options_limits(options), selection, events), decoded);
                events = events + seq![Part2JpipAutomaticEvent::Image { calls: image_calls }];
                assert(events.drop_first() =~= seq![Part2JpipAutomaticEvent::Image { calls: image_calls }]);
                assert(events.drop_first().drop_first() =~= Seq::empty());
            }
        }
    }
    assert(part2_jpip_planned_cold_run(cache, decoder, options, selection, events)
        == Some(((result.0, result.1, cache), Seq::empty())));
}

pub(crate) proof fn part2_jpip_planned_transcode_error(
    cache: Part2JpipCache, decoder: Part2JpipProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>,
    available: u16, missing: Seq<Part2JpipMissing>, error: crate::DecodeError,
)
    requires part2_jpip_progressive_availability(cache, decoder.0) == Ok((available, missing)),
        valid_jpip_progressive_update(decoder.1 as nat, available as nat, (decoder.0.3.len() as u16) as nat),
        available > decoder.1, part2_jpip_transcode_cold_result(cache, decoder.0, available, Err(error)),
    ensures part2_jpip_planned_cold_result(cache, decoder, options, selection, (Err(error), decoder, cache)),
{
    reveal(part2_jpip_planned_cold_result);
    part2_jpip_transcode_cold_frames(cache, decoder.0, available, Err(error));
    let calls = part2_cold_witness(
        |events| part2_jpip_transcode_cold_run(cache, decoder.0, available, events), Err(error));
    let events = seq![Part2JpipAutomaticEvent::Transcode { calls }];
    assert(events.drop_first() =~= Seq::empty());
    assert(part2_jpip_planned_cold_run(cache, decoder, options, selection, events)
        == Some(((Err(error), decoder, cache), Seq::empty())));
}

pub(crate) proof fn part2_jpip_planned_image_actual(
    cache: Part2JpipCache, decoder: Part2JpipProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>,
    available: u16, missing: Seq<Part2JpipMissing>, transcoded: Part2JpipTranscode,
    bytes: Seq<u8>, decoded: Result<Part1DecodedTypedImage, crate::DecodeError>,
)
    requires part2_jpip_progressive_availability(cache, decoder.0) == Ok((available, missing)),
        valid_jpip_progressive_update(decoder.1 as nat, available as nat, (decoder.0.3.len() as u16) as nat),
        available > decoder.1,
        part2_jpip_transcode_cold_result(cache, decoder.0, available, Ok(transcoded)), transcoded.2 == Some(bytes),
        part2_decode_raw_cold_result(bytes, crate::options::decode_options_limits(options), selection, decoded),
    ensures part2_jpip_planned_cold_result(cache, decoder, options, selection,
        part2_jpip_planned_image_frame(cache, decoder, available, missing, decoded)),
{
    reveal(part2_jpip_planned_cold_result);
    part2_jpip_transcode_cold_frames(cache, decoder.0, available, Ok(transcoded));
    let calls = part2_cold_witness(
        |events| part2_jpip_transcode_cold_run(cache, decoder.0, available, events), Ok(transcoded));
    part2_cold_prefix_at(
        |events| part2_jpip_transcode_cold_run(cache, decoder.0, available, events),
        calls, Ok(transcoded), Seq::empty());
    assert(calls + Seq::empty() =~= calls);
    part2_decode_raw_cold_frames(bytes, crate::options::decode_options_limits(options), selection, decoded);
    let image_calls = part2_cold_witness(
        |events| part2_decode_raw_cold_run(bytes, crate::options::decode_options_limits(options), selection, events), decoded);
    part2_cold_prefix_at(
        |events| part2_decode_raw_cold_run(bytes, crate::options::decode_options_limits(options), selection, events),
        image_calls, decoded, Seq::empty());
    assert(image_calls + Seq::empty() =~= image_calls);
    let events = seq![Part2JpipAutomaticEvent::Transcode { calls },
        Part2JpipAutomaticEvent::Image { calls: image_calls }];
    assert(events.drop_first() =~= seq![Part2JpipAutomaticEvent::Image { calls: image_calls }]);
    assert(events.drop_first().drop_first() =~= Seq::empty());
    assert(part2_jpip_planned_cold_run(cache, decoder, options, selection, events)
        == Some((part2_jpip_planned_image_frame(cache, decoder, available, missing, decoded), Seq::empty())));
}

pub(crate) open spec fn part2_jpip_automatic_snapshot_call(
    input: Part2JpipSnapshotInput<'_>, events: Seq<Part2JpipAutomaticEvent>,
) -> Option<(Result<Part2JpipAutomaticSnapshotResult, crate::DecodeError>, Seq<Part2JpipAutomaticEvent>)> {
    if events.len() == 0 { None } else {
        match events[0] {
            Part2JpipAutomaticEvent::Snapshot { calls } => match part2_jpip_snapshot_run(input, calls) {
                Some((result, rest)) => if rest.len() == 0 { Some((result, events.drop_first())) } else { None },
                None => None,
            },
            _ => None,
        }
    }
}

pub(crate) open spec fn part2_jpip_automatic_image_call(
    bytes: Seq<u8>, options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>,
    events: Seq<Part2JpipAutomaticEvent>,
) -> Option<(Result<Part1DecodedTypedImage, crate::DecodeError>, Seq<Part2JpipAutomaticEvent>)> {
    if events.len() == 0 { None } else {
        match events[0] {
            Part2JpipAutomaticEvent::Image { calls } => match part2_decode_raw_cold_run(
                bytes, crate::options::decode_options_limits(options), selection, calls) {
                Some((result, rest)) => if rest.len() == 0 { Some((result, events.drop_first())) } else { None },
                None => None,
            },
            _ => None,
        }
    }
}

pub(crate) open spec fn part2_jpip_automatic_image_frame(
    cache: Part2JpipCache, decoder: Part2JpipAutomaticProgressiveDecoder,
    snapshot: Part2JpipAutomaticSnapshot, image: Result<Part1DecodedTypedImage, crate::DecodeError>,
) -> Part2JpipAutomaticProgressiveResult {
    match image {
        Err(error) => (Err(error), decoder, cache),
        Ok(image) => (Ok((
            if snapshot.1 == snapshot.2 { crate::jpip::JpipProgressiveStatus::Complete }
            else { crate::jpip::JpipProgressiveStatus::QualityAdvanced },
            decoder.1, snapshot.1, snapshot.3, Some(image))), (decoder.0, snapshot.1), cache),
    }
}

pub(crate) open spec fn part2_jpip_automatic_after_snapshot(
    cache: Part2JpipCache, decoder: Part2JpipAutomaticProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>,
    snapshot: Part2JpipAutomaticSnapshotResult, events: Seq<Part2JpipAutomaticEvent>,
) -> Option<(Part2JpipAutomaticProgressiveResult, Seq<Part2JpipAutomaticEvent>)> {
    match snapshot {
        (None, missing) => Some(((Ok((
            crate::jpip::JpipProgressiveStatus::WaitingForData, decoder.1, 0, missing, None)), decoder, cache), events)),
        (Some(snapshot), _) => {
            if !valid_jpip_progressive_update(decoder.1 as nat, snapshot.1 as nat, snapshot.2 as nat) {
                Some(((Err(part2_jpip_plan_invalid(0)), decoder, cache), events))
            } else if snapshot.1 <= decoder.1 {
                Some(((Ok((if snapshot.1 == snapshot.2 { crate::jpip::JpipProgressiveStatus::Complete }
                    else { crate::jpip::JpipProgressiveStatus::WaitingForData },
                    decoder.1, snapshot.1, snapshot.3, None)), decoder, cache), events))
            } else {
                match part2_jpip_automatic_image_call(snapshot.0, options, selection, events) {
                    None => None,
                    Some((image, rest)) => Some((part2_jpip_automatic_image_frame(cache, decoder, snapshot, image), rest)),
                }
            }
        },
    }
}

pub closed spec fn part2_jpip_automatic_progressive_run(
    cache: Part2JpipCache, decoder: Part2JpipAutomaticProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>, components: Seq<u16>,
    events: Seq<Part2JpipAutomaticEvent>,
) -> Option<(Part2JpipAutomaticProgressiveResult, Seq<Part2JpipAutomaticEvent>)> {
    let input = Part2JpipSnapshotInput {
        cache, stream: decoder.0,
        selected: match selection { None => None, Some(value) => Some(crate::options::decode_selection_view(value)) },
        components, limits: crate::options::decode_options_limits(options),
    };
    match part2_jpip_automatic_snapshot_call(input, events) {
        None => None,
        Some((Err(error), rest)) => Some(((Err(error), decoder, cache), rest)),
        Some((Ok(snapshot), rest)) => part2_jpip_automatic_after_snapshot(cache, decoder, options, selection, snapshot, rest),
    }
}

pub(crate) proof fn part2_jpip_automatic_progressive_run_unfold(
    cache: Part2JpipCache, decoder: Part2JpipAutomaticProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>, components: Seq<u16>,
    events: Seq<Part2JpipAutomaticEvent>,
)
    ensures part2_jpip_automatic_progressive_run(cache, decoder, options, selection, components, events)
        == {
            let input = Part2JpipSnapshotInput {
                cache, stream: decoder.0,
                selected: match selection { None => None, Some(value) => Some(crate::options::decode_selection_view(value)) },
                components, limits: crate::options::decode_options_limits(options),
            };
            match part2_jpip_automatic_snapshot_call(input, events) {
                None => None,
                Some((Err(error), rest)) => Some(((Err(error), decoder, cache), rest)),
                Some((Ok(snapshot), rest)) => part2_jpip_automatic_after_snapshot(cache, decoder, options, selection, snapshot, rest),
            }
        },
{
    reveal(part2_jpip_automatic_progressive_run);
}

pub(crate) proof fn part2_jpip_automatic_image_actual(
    cache: Part2JpipCache, decoder: Part2JpipAutomaticProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>, components: Seq<u16>,
    snapshot_calls: Seq<Part2JpipSnapshotEvent>, snapshot: Part2JpipAutomaticSnapshot,
    outer_missing: Seq<Part2JpipMissing>, decoded: Result<Part1DecodedTypedImage, crate::DecodeError>,
)
    requires part2_jpip_snapshot_run(Part2JpipSnapshotInput {
            cache, stream: decoder.0,
            selected: match selection { None => None, Some(value) => Some(crate::options::decode_selection_view(value)) },
            components, limits: crate::options::decode_options_limits(options),
        }, snapshot_calls) == Some((Ok((Some(snapshot), outer_missing)), Seq::empty())),
        valid_jpip_progressive_update(decoder.1 as nat, snapshot.1 as nat, snapshot.2 as nat),
        snapshot.1 > decoder.1,
        part2_decode_raw_cold_result(snapshot.0, crate::options::decode_options_limits(options), selection, decoded),
    ensures part2_jpip_automatic_progressive_update_result(cache, decoder, options, selection, components,
        part2_jpip_automatic_image_frame(cache, decoder, snapshot, decoded)),
{
    part2_decode_raw_cold_frames(snapshot.0, crate::options::decode_options_limits(options), selection, decoded);
    let image_calls = part2_cold_witness(
        |events| part2_decode_raw_cold_run(snapshot.0, crate::options::decode_options_limits(options), selection, events), decoded);
    part2_cold_prefix_at(
        |events| part2_decode_raw_cold_run(snapshot.0, crate::options::decode_options_limits(options), selection, events),
        image_calls, decoded, Seq::empty());
    assert(image_calls + Seq::empty() =~= image_calls);
    let events = seq![Part2JpipAutomaticEvent::Snapshot { calls: snapshot_calls },
        Part2JpipAutomaticEvent::Image { calls: image_calls }];
    assert(events.drop_first() =~= seq![Part2JpipAutomaticEvent::Image { calls: image_calls }]);
    assert(events.drop_first().drop_first() =~= Seq::empty());
    part2_jpip_automatic_progressive_run_unfold(cache, decoder, options, selection, components, events);
    assert(part2_jpip_automatic_progressive_run(cache, decoder, options, selection, components, events)
        == Some((part2_jpip_automatic_image_frame(cache, decoder, snapshot, decoded), Seq::empty())));
}

#[verifier::opaque]
pub open spec fn part2_jpip_partition_bytes(
    packets: Seq<Part2JpipAutomaticPacket>, target: u64, end: nat, consumed: u64,
) -> Result<Option<usize>, crate::DecodeError>
    decreases if end < packets.len() { packets.len() - end } else { 0 },
{
    if end < packets.len() && consumed < target {
        match packets[end as int].1 {
            None => Ok(None),
            Some(bytes) => {
                let next = consumed as nat + (bytes.len() as u64) as nat;
                if next > u64::MAX as nat { Err(part2_jpip_range_overflow(0)) }
                else { part2_jpip_partition_bytes(packets, target, end + 1, next as u64) }
            },
        }
    } else if consumed != target {
        Err(part2_jpip_cache_error(consumed, crate::MalformedKind::InvalidPacketLength))
    } else { Ok(Some(end as usize)) }
}

pub open spec fn part2_jpip_partition_end(
    packets: Seq<Part2JpipAutomaticPacket>, transition: Part2JpipTransition,
    part: nat, count: nat, start: usize,
) -> Result<Option<usize>, crate::DecodeError> {
    if part + 1 == count { Ok(Some(packets.len() as usize)) }
    else {
        match transition.2 {
            Some(packets_in_part) => if packets_in_part > usize::MAX as u64 {
                Err(part2_jpip_range_overflow(0))
            } else if start as nat + packets_in_part as nat > usize::MAX as nat {
                Err(part2_jpip_range_overflow(0))
            } else {
                let end = (start as nat + packets_in_part as nat) as usize;
                if end as nat > packets.len() {
                    Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidPacketLength))
                } else { Ok(Some(end)) }
            },
            None => match transition.3 {
                Some(target) => part2_jpip_partition_bytes(packets, target, start as nat, 0),
                None => Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart)),
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_partition_parts(
    headers: Seq<Seq<u8>>, states: Seq<Part2OwnedTilePart>, transitions: Seq<Part2JpipTransition>,
    packets: Seq<Part2JpipAutomaticPacket>, part: nat, start: usize,
    output: Seq<Part2JpipAutomaticTilePart>,
) -> Result<Option<Seq<Part2JpipAutomaticTilePart>>, crate::DecodeError>
    decreases if part < headers.len() { headers.len() - part } else { 0 },
{
    if part >= headers.len() {
        if start as nat != packets.len() {
            Err(part2_jpip_cache_error(start as u64, crate::MalformedKind::InvalidPacketLength))
        } else { Ok(Some(output)) }
    } else if part >= transitions.len() || part >= states.len() {
        Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart))
    } else {
        match part2_jpip_partition_end(packets, transitions[part as int], part, headers.len(), start) {
            Err(error) => Err(error),
            Ok(None) => Ok(None),
            Ok(Some(end)) => if start > end || end as nat > packets.len() {
                Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidPacketLength))
            } else {
                let state = states[part as int];
                part2_jpip_partition_parts(headers, states, transitions, packets, part + 1, end,
                    output.push((headers[part as int], packets.subrange(start as int, end as int),
                        state.coding_style.sop_markers, state.coding_style.eph_markers)))
            },
        }
    }
}

pub open spec fn part2_jpip_partition_automatic_tiles(
    headers: Seq<Seq<u8>>, states: Seq<Part2OwnedTilePart>, transitions: Seq<Part2JpipTransition>,
    packets: Seq<Part2JpipAutomaticPacket>,
) -> Result<Option<Seq<Part2JpipAutomaticTilePart>>, crate::DecodeError> {
    if headers.len() != states.len() || headers.len() != transitions.len() || headers.len() == 0 {
        Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart))
    } else { part2_jpip_partition_parts(headers, states, transitions, packets, 0, 0, Seq::empty()) }
}

pub open spec fn part2_jpip_ordinal_matrix_write(
    before: Seq<Seq<Option<u16>>>, after: Seq<Seq<Option<u16>>>,
    execution: usize, layer: u16, sequence: u16,
) -> bool {
    (execution as nat) < before.len()
        && (layer as nat) < before[execution as int].len()
        && before[execution as int][layer as int].is_none()
        && after == before.update(execution as int,
            before[execution as int].update(layer as int, Some(sequence)))
}

pub open spec fn part2_jpip_packet_matrix_write(
    before: Seq<Seq<Option<Seq<u8>>>>, after: Seq<Seq<Option<Seq<u8>>>>,
    execution: usize, layer: u16, bytes: Seq<u8>,
) -> bool {
    (execution as nat) < before.len()
        && (layer as nat) < before[execution as int].len()
        && after == before.update(execution as int,
            before[execution as int].update(layer as int, Some(bytes)))
}

#[verifier::opaque]
pub open spec fn part2_jpip_progressive_layers(
    cache: Part2JpipCache, packets: Seq<Part2JpipPacket>, ends: Seq<usize>, layer: nat, start: usize,
) -> Result<(u16, Seq<Part2JpipMissing>), crate::DecodeError>
    decreases if layer < ends.len() { ends.len() - layer } else { 0 },
{
    if layer >= ends.len() {
        if layer > u16::MAX as nat { Err(part2_jpip_range_overflow(0)) }
        else { Ok((layer as u16, Seq::empty())) }
    } else {
        let end = ends[layer as int];
        if start > end || end as nat > packets.len() { Err(part2_jpip_range_overflow(0)) }
        else {
            let ranges = packets.subrange(start as int, end as int).map_values(|packet: Part2JpipPacket| packet.0);
            match part2_jpip_cache_availability(cache, ranges) {
                Err(error) => Err(error),
                Ok(report) => if report.0 != crate::jpip::JpipAvailability::Available {
                    if layer > u16::MAX as nat { Err(part2_jpip_range_overflow(0)) }
                    else { Ok((layer as u16, report.3)) }
                } else { part2_jpip_progressive_layers(cache, packets, ends, layer + 1, end) },
            }
        }
    }
}

pub open spec fn part2_jpip_progressive_availability(cache: Part2JpipCache, plan: Part2JpipPlan)
    -> Result<(u16, Seq<Part2JpipMissing>), crate::DecodeError> {
    let main = part2_jpip_append_complete_requirement(cache, plan.0,
        (crate::jpip::JpipAvailability::Available, 0, 0, Seq::empty()));
    match main.0 {
        Err(error) => Err(error),
        Ok(()) => {
            let tile = part2_jpip_append_complete_requirement(cache, plan.1, main.1);
            match tile.0 {
                Err(error) => Err(error),
                Ok(()) => if tile.1.3.len() != 0 { Ok((0, tile.1.3)) }
                else { part2_jpip_progressive_layers(cache, plan.2, plan.3, 0, 0) },
            }
        },
    }
}

pub open spec fn part2_jpip_progressive_update(
    cache: Part2JpipCache, decoder: Part2JpipProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>,
) -> (Result<Part2JpipProgressiveUpdate, crate::DecodeError>, Part2JpipProgressiveDecoder) {
    let previous = decoder.1;
    let planned = decoder.0.3.len() as u16;
    match part2_jpip_progressive_availability(cache, decoder.0) {
        Err(error) => (Err(error), decoder),
        Ok((available, missing)) => {
            if !valid_jpip_progressive_update(previous as nat, available as nat, planned as nat) {
                (Err(part2_jpip_plan_invalid(0)), decoder)
            } else if available <= previous {
                (Ok((if available == planned { crate::jpip::JpipProgressiveStatus::Complete }
                    else { crate::jpip::JpipProgressiveStatus::WaitingForData }, previous, available, missing, None)), decoder)
            } else {
                match part2_jpip_transcode(cache, decoder.0, available) {
                    Err(error) => (Err(error), decoder),
                    Ok(transcoded) => match transcoded.2 {
                        None => (Err(part2_jpip_cache_error(0, crate::MalformedKind::MissingRequiredStructure)), decoder),
                        Some(bytes) => match part2_decode_raw_codestream(
                            bytes, crate::options::decode_options_limits(options), selection) {
                            Err(error) => (Err(error), decoder),
                            Ok(image) => (Ok((
                                if available == planned { crate::jpip::JpipProgressiveStatus::Complete }
                                else { crate::jpip::JpipProgressiveStatus::QualityAdvanced },
                                previous, available, missing, Some(image),
                            )), (decoder.0, available)),
                        },
                    },
                }
            }
        },
    }
}

}
