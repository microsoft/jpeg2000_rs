//! Ordered actual cache/caller preparation for automatic snapshots.

use super::*;

verus! {

pub enum Part2JpipSnapshotEvent {
    Capacity { site: u8, tile: usize, elements: usize, succeeded: bool },
    Main { calls: Seq<Part2JpipStorageEvent> },
}

pub(crate) open spec fn part2_jpip_snapshot_normalized_events(
    count: u64, raw_count: usize, calls: Seq<Part2JpipStorageEvent>,
) -> Seq<Part2JpipSnapshotEvent> {
    seq![Part2JpipSnapshotEvent::Capacity { site: 0, tile: 0, elements: count as usize, succeeded: true },
        Part2JpipSnapshotEvent::Main { calls },
        Part2JpipSnapshotEvent::Capacity { site: 1, tile: 0, elements: raw_count, succeeded: true }]
}

pub(crate) type Part2JpipSnapshotRun<T> =
    Option<(Result<T, crate::DecodeError>, Seq<Part2JpipSnapshotEvent>)>;

pub(crate) struct Part2JpipSnapshotInput<'a> {
    pub cache: Part2JpipCache,
    pub stream: u64,
    pub selected: Option<Part2DecodeSelection>,
    pub components: Seq<u16>,
    pub limits: &'a crate::ResourceLimits,
}

pub(crate) struct Part2JpipSnapshotTileRoot<'a> {
    pub input: Part2JpipSnapshotInput<'a>,
    pub events: Seq<Part2JpipSnapshotEvent>,
    pub count: u64,
    pub components: u16,
    pub main: Seq<u8>,
    pub raw: Seq<Seq<u8>>,
    pub headers: Seq<Seq<Seq<u8>>>,
    pub layout: Part2DecoderLayoutInput,
    pub tile: nat,
    pub before: Part2JpipAutomaticTiles,
    pub maximum: u16,
}

pub(crate) open spec fn part2_jpip_snapshot_tile_root(root: Part2JpipSnapshotTileRoot<'_>) -> bool {
    forall|tail: Seq<Part2JpipSnapshotEvent>| part2_jpip_snapshot_run(root.input, root.events + tail)
        == part2_jpip_snapshot_tiles(root.input, root.count, root.components, root.main, root.raw,
            root.headers, root.layout, root.tile, root.before, root.maximum, tail)
}

pub(crate) open spec fn part2_jpip_snapshot_lift<T>(
    result: Result<T, crate::DecodeError>, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2JpipSnapshotRun<T> { Some((result, events)) }

pub(crate) open spec fn part2_jpip_snapshot_bind<A, B>(
    result: Part2JpipSnapshotRun<A>,
    next: spec_fn(A, Seq<Part2JpipSnapshotEvent>) -> Part2JpipSnapshotRun<B>,
) -> Part2JpipSnapshotRun<B> {
    match result {
        None => None,
        Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(value), rest)) => next(value, rest),
    }
}

pub(crate) open spec fn part2_jpip_snapshot_capacity(
    events: Seq<Part2JpipSnapshotEvent>, site: u8, tile: usize, elements: usize,
) -> Part2JpipSnapshotRun<()> {
    if events.len() == 0 { None }
    else {
        match events[0] {
            Part2JpipSnapshotEvent::Capacity { site: actual, tile: at, elements: count, succeeded } =>
                if actual == site && at == tile && count == elements {
                    Some((if succeeded { Ok(()) } else { Err(crate::DecodeError::AllocationFailed) },
                        events.drop_first()))
                } else { None },
            _ => None,
        }
    }
}

pub(crate) open spec fn part2_jpip_snapshot_component_selection(
    selected: Seq<u16>, components: u16,
) -> Result<(), crate::DecodeError> {
    if exists|index: int| 0 <= index < selected.len() &&
        (selected[index] >= components || exists|previous: int|
            0 <= previous < index && selected[previous] == selected[index]) {
        Err(crate::DecodeError::InvalidSelection {
            reason: crate::SelectionError::EmptyComponentIntersection })
    } else { Ok(()) }
}

pub(crate) open spec fn part2_jpip_snapshot_tile_selected(
    selected: Option<Part2DecodeSelection>, tile: u16,
) -> bool {
    match selected { None => true, Some(selection) => match selection.0 {
        Part2TileSelection::All => true,
        Part2TileSelection::Index(index) => index == tile,
        Part2TileSelection::Set(indices) => indices.contains(tile),
    } }
}

pub(crate) open spec fn part2_jpip_snapshot_component_included(selected: Seq<u16>, component: u16) -> bool {
    selected.len() == 0 || selected.contains(component)
}

pub(crate) open spec fn part2_jpip_snapshot_required(
    input: Part2JpipSnapshotInput<'_>, tile: u16, coordinate: crate::packet::PacketCoordinate,
    styles: crate::codestream::ComponentCodingStyles,
) -> Result<bool, crate::DecodeError> {
    if !part2_jpip_snapshot_tile_selected(input.selected, tile)
        || !part2_jpip_snapshot_component_included(input.components, coordinate.component) { Ok(false) }
    else { part2_jpip_snapshot_resolution(input.selected, coordinate.component, coordinate.resolution, styles) }
}

pub(crate) open spec fn part2_jpip_snapshot_resolution(
    selected: Option<Part2DecodeSelection>, component: u16, resolution: u8,
    styles: crate::codestream::ComponentCodingStyles,
) -> Result<bool, crate::DecodeError> {
        let discard = match selected { None => 0u8, Some(selection) => selection.2 };
        match crate::codestream::component_coding_style_result(&styles, component) {
            Err(error) => Err(error),
            Ok(style) => if style.decomposition_levels == u8::MAX
                || style.decomposition_levels as nat + 1 < discard as nat {
                Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::ReductionTooLarge })
            } else { Ok((resolution as nat) < style.decomposition_levels as nat + 1 - discard as nat) },
        }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_snapshot_level_start(
    grid: Part1PacketGrid, component: u16, resolution: u8, level: u8, before: u64,
) -> Result<u64, crate::DecodeError>
    decreases resolution as int - level as int,
{
    if level >= resolution { Ok(before) }
    else {
        match part1_packet_grid_precinct_count(grid, component, level) {
            Err(error) => Err(error),
            Ok(count) => if before as nat + count as nat > u64::MAX as nat { Err(part2_jpip_range_overflow(0)) }
            else { part2_jpip_snapshot_level_start(grid, component, resolution,
                (level + 1) as u8, (before as nat + count as nat) as u64) },
        }
    }
}

pub(crate) open spec fn part2_jpip_snapshot_in_class(
    tiles: u64, components: u64, tile: u64, component: u16, resolution: u8, precinct: u32,
    grid: Part1PacketGrid,
) -> Result<u64, crate::DecodeError> {
    if tiles == 0 || components == 0 || tile >= tiles || component as u64 >= components {
        Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidJpipLayout))
    } else {
        match part2_jpip_snapshot_level_start(grid, component, resolution, 0, 0) {
            Err(error) => Err(error),
            Ok(start) => {
                let index = start as nat + precinct as nat;
                let scaled = index * components as nat;
                let without = component as nat + scaled;
                let product = without * tiles as nat;
                let result = tile as nat + product;
                if index > u64::MAX as nat || scaled > u64::MAX as nat || without > u64::MAX as nat
                    || product > u64::MAX as nat || result > u64::MAX as nat {
                    Err(part2_jpip_range_overflow(0))
                } else { Ok(result as u64) }
            },
        }
    }
}

pub(crate) type Part2JpipSnapshotOrder = Seq<(crate::packet::PacketCoordinate, usize)>;

pub(crate) open spec fn part2_jpip_snapshot_order(
    iterator: Part1ProgressionPacketIterator, remaining: u64, ordinal: u64,
    ordinals: Seq<Seq<Option<u16>>>, before: Part2JpipSnapshotOrder,
) -> Result<Part2JpipSnapshotOrder, crate::DecodeError> {
    let phase = part2_jpip_order_phase(iterator.grid, iterator, ordinals, before, ordinal, remaining);
    match phase.0 { Err(error) => Err(error), Ok(()) => Ok(phase.3) }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_snapshot_databins(
    input: Part2JpipSnapshotInput<'_>, tiles: u64, components: u16, tile: usize,
    plan: Part2ProgressionTilePlan, index: nat, before: Seq<Part2JpipDatabin>,
) -> Result<Seq<Part2JpipDatabin>, crate::DecodeError>
    decreases if index < plan.precincts.len() { plan.precincts.len() - index } else { 0 },
{
    if index >= plan.precincts.len() { Ok(before) }
    else {
        let precinct = plan.precincts[index as int];
        match part2_jpip_snapshot_in_class(tiles, components as u64, tile as u64,
            precinct.component, precinct.resolution, precinct.precinct, plan.grid) {
            Err(error) => Err(error),
            Ok(in_class) => match part2_jpip_databin(0, input.stream, in_class) {
                Err(error) => Err(error),
                Ok(id) => part2_jpip_snapshot_databins(input, tiles, components, tile, plan,
                    index + 1, before.push(id)),
            },
        }
    }
}

pub(crate) struct Part2JpipSnapshotPacketState {
    pub precincts: Seq<Part1PacketPrecinctState>,
    pub parsed: Seq<Seq<Option<Seq<u8>>>>,
    pub offsets: Seq<u64>,
    pub blocked: Seq<bool>,
    pub transition: usize,
    pub packets: u64,
    pub bytes: u64,
}

pub(crate) open spec fn part2_jpip_snapshot_decode_packet(
    initial: Part1PacketPrecinctState, part: Part2OwnedTilePart,
    data: Seq<u8>, sequence: u16, layer: u16, limits: &crate::ResourceLimits,
) -> (Result<usize, crate::DecodeError>, Part1PacketPrecinctState) {
    let state = part1_precinct_context_layer(initial, layer);
    let packet = part1_precinct_packet_fields(state, data, &part.component_coding_styles,
        &part.coding_style, false, 0, Seq::empty(), 0, None, sequence, false,
        crate::limits::resource_code_block_limit(limits),
        crate::limits::resource_packet_header_byte_limit(limits),
        crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),
        crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits));
    let result = match packet.0 {
        Err(error) => Err(error),
        Ok((decoded, consumed, packed)) => if packed != 0 {
            Err(part1_packet_reader_error(0, crate::MalformedKind::InvalidPacketLength))
        } else if decoded.bytes_consumed as nat > usize::MAX as nat { Err(part2_jpip_range_overflow(0)) }
        else if consumed != decoded.bytes_consumed as nat {
            Err(part1_packet_reader_error(0, crate::MalformedKind::InvalidPacketLength))
        }
        else { Ok(consumed) },
    };
    (result, if result.is_err() { initial } else { packet.1 })
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_snapshot_parse_packets(
    input: Part2JpipSnapshotInput<'_>, parts: Seq<Part2OwnedTilePart>,
    transitions: Seq<Part2JpipTransition>, databins: Seq<Part2JpipDatabin>,
    order: Part2JpipSnapshotOrder, index: nat, state: Part2JpipSnapshotPacketState,
) -> Result<Part2JpipSnapshotPacketState, crate::DecodeError>
    decreases if index < order.len() { order.len() - index } else { 0 },
{
    if index >= order.len() { Ok(state) }
    else {
        let coordinate = order[index as int].0;
        let execution = order[index as int].1;
        if execution as nat >= state.blocked.len() { Err(part2_jpip_range_overflow(0)) }
        else if state.blocked[execution as int] {
            part2_jpip_snapshot_parse_packets(input, parts, transitions, databins, order, index + 1, state)
        } else if state.transition as nat >= parts.len() {
            Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart))
        } else if execution as nat >= databins.len() || execution as nat >= state.offsets.len() {
            Err(part2_jpip_range_overflow(0))
        } else {
            let id = databins[execution as int];
            let prefix = part2_jpip_cache_prefix(input.cache, id);
            let offset = state.offsets[execution as int];
            if offset > usize::MAX as u64 { Err(part2_jpip_range_overflow(0)) }
            else if offset as nat >= prefix.len() {
                part2_jpip_snapshot_parse_packets(input, parts, transitions, databins, order, index + 1,
                    Part2JpipSnapshotPacketState { blocked: state.blocked.update(execution as int, true), ..state })
            } else if execution as nat >= state.precincts.len() { Err(part2_jpip_range_overflow(0)) }
            else {
                let decoded = part2_jpip_snapshot_decode_packet(state.precincts[execution as int],
                    parts[state.transition as int], prefix.subrange(offset as int, prefix.len() as int),
                    ((index as usize) & 65535) as u16, coordinate.layer, input.limits);
                let state = Part2JpipSnapshotPacketState {
                    precincts: state.precincts.update(execution as int, decoded.1), ..state };
                match decoded.0 {
                    Err(crate::DecodeError::MalformedInput { offset: _, kind: crate::MalformedKind::Truncated })
                        if !part2_jpip_cache_complete(input.cache, id) =>
                            part2_jpip_snapshot_parse_packets(input, parts, transitions, databins, order, index + 1,
                                Part2JpipSnapshotPacketState { blocked: state.blocked.update(execution as int, true), ..state }),
                    Err(error) => Err(error),
                    Ok(consumed) => if consumed == 0 {
                        Err(part2_jpip_cache_error(offset, crate::MalformedKind::InvalidPacketLength))
                    } else if offset as nat + consumed as nat > usize::MAX as nat {
                        Err(part2_jpip_range_overflow(offset))
                    } else {
                        let end = offset as nat + consumed as nat;
                        if end > prefix.len() { Err(part2_jpip_cache_error(offset, crate::MalformedKind::Truncated)) }
                        else if execution as nat >= state.parsed.len()
                            || coordinate.layer as nat >= state.parsed[execution as int].len() {
                            Err(part2_jpip_range_overflow(0))
                        } else if state.packets == u64::MAX
                            || state.bytes as nat + (consumed as u64) as nat > u64::MAX as nat {
                            Err(part2_jpip_range_overflow(0))
                        } else if state.transition as nat >= transitions.len() {
                            Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart))
                        } else if state.transition == usize::MAX { Err(part2_jpip_range_overflow(0)) }
                        else {
                            let packets = (state.packets + 1) as u64;
                            let bytes = (state.bytes as nat + (consumed as u64) as nat) as u64;
                            let transition = transitions[state.transition as int];
                            let boundary = match transition.2 {
                                Some(count) => packets == count,
                                None => match transition.3 { Some(length) => bytes == length, None => false },
                            };
                            let advance = boundary && state.transition as nat + 1 < transitions.len();
                            part2_jpip_snapshot_parse_packets(input, parts, transitions, databins, order, index + 1,
                                Part2JpipSnapshotPacketState {
                                    parsed: state.parsed.update(execution as int, state.parsed[execution as int].update(
                                        coordinate.layer as int, Some(prefix.subrange(offset as int, end as int)))),
                                    offsets: state.offsets.update(execution as int, end as u64),
                                    transition: if advance { (state.transition + 1) as usize } else { state.transition },
                                    packets: if advance { 0 } else { packets },
                                    bytes: if advance { 0 } else { bytes }, ..state })
                        }
                    },
                }
            }
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_snapshot_make_packets(
    input: Part2JpipSnapshotInput<'_>, tile: u16, style: crate::codestream::ComponentCodingStyles,
    order: Part2JpipSnapshotOrder, databins: Seq<Part2JpipDatabin>,
    state: Part2JpipSnapshotPacketState, index: nat, before: Seq<Part2JpipAutomaticPacket>,
) -> Result<Seq<Part2JpipAutomaticPacket>, crate::DecodeError>
    decreases if index < order.len() { order.len() - index } else { 0 },
{
    if index >= order.len() { Ok(before) }
    else {
        let coordinate = order[index as int].0;
        let execution = order[index as int].1;
        match part2_jpip_snapshot_required(input, tile, coordinate, style) {
            Err(error) => Err(error),
            Ok(required) => if execution as nat >= state.parsed.len()
                || coordinate.layer as nat >= state.parsed[execution as int].len()
                || execution as nat >= databins.len() || execution as nat >= state.offsets.len() {
                Err(part2_jpip_range_overflow(0))
            } else {
                part2_jpip_snapshot_make_packets(input, tile, style, order, databins, state, index + 1,
                    before.push((databins[execution as int],
                        state.parsed[execution as int][coordinate.layer as int], state.offsets[execution as int],
                        required, ((index as usize) & 65535) as u16, coordinate.layer)))
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_snapshot_partition_missing(
    cache: Part2JpipCache, packets: Seq<Part2JpipAutomaticPacket>, index: nat, before: Seq<Part2JpipMissing>,
) -> Seq<Part2JpipMissing>
    decreases if index < packets.len() { packets.len() - index } else { 0 },
{
    if index >= packets.len() { before }
    else {
        let packet = packets[index as int];
        let next = if packet.1.is_none()
            && !(exists|at: int| 0 <= at < before.len() && part2_jpip_identity(before[at].0, packet.0)) {
            before.push((packet.0, packet.2, match part2_jpip_cache_status(cache, packet.0) {
                Some(status) => match status.0 {
                    Some(length) => Some(if length > packet.2 { (length - packet.2) as u64 } else { 0u64 }),
                    None => None,
                }, None => None,
            }))
        } else { before };
        part2_jpip_snapshot_partition_missing(cache, packets, index + 1, next)
    }
}

pub(crate) proof fn part2_jpip_snapshot_resolution_current_error(
    input: Part2JpipSnapshotInput<'_>, tile: u16, style: crate::codestream::ComponentCodingStyles,
    order: Part2JpipSnapshotOrder, databins: Seq<Part2JpipDatabin>,
    state: Part2JpipSnapshotPacketState, index: nat, before: Seq<Part2JpipAutomaticPacket>,
    error: crate::DecodeError,
)
    ensures index < order.len()
        && part2_jpip_snapshot_tile_selected(input.selected, tile)
        && (input.components.len() == 0 || input.components.contains(order[index as int].0.component))
        && part2_jpip_snapshot_resolution(input.selected, order[index as int].0.component,
            order[index as int].0.resolution, style) == Err(error)
        ==> part2_jpip_snapshot_make_packets(input, tile, style, order, databins, state, index, before) == Err(error),
{
    reveal(part2_jpip_snapshot_make_packets);
}

pub(crate) type Part2JpipSnapshotTile =
    (Option<Seq<Part2JpipAutomaticTilePart>>, Seq<Part2JpipAutomaticPacket>, u16);

pub(crate) open spec fn part2_jpip_snapshot_acquired_packets(
    input: Part2JpipSnapshotInput<'_>, parts: Seq<Part2OwnedTilePart>,
    transitions: Seq<Part2JpipTransition>, databins: Seq<Part2JpipDatabin>,
    order: Part2JpipSnapshotOrder, initial: Part2JpipSnapshotPacketState,
    tile: usize, styles: crate::codestream::ComponentCodingStyles,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2JpipSnapshotRun<Seq<Part2JpipAutomaticPacket>> {
    let parsed = part2_jpip_snapshot_parse_packets(input, parts, transitions, databins, order, 0, initial);
    part2_jpip_snapshot_bind(part2_jpip_snapshot_lift(parsed, events),
        |state: Part2JpipSnapshotPacketState, events| {
        part2_jpip_snapshot_bind(part2_jpip_snapshot_capacity(events, 4, tile, order.len() as usize),
            |_unit: (), events| {
            part2_jpip_snapshot_lift(part2_jpip_snapshot_make_packets(input, tile as u16,
                styles, order, databins, state, 0, Seq::empty()), events)
        })
    })
}

pub(crate) proof fn part2_jpip_snapshot_acquired_resolution_error(
    input: Part2JpipSnapshotInput<'_>, parts: Seq<Part2OwnedTilePart>,
    transitions: Seq<Part2JpipTransition>, databins: Seq<Part2JpipDatabin>,
    order: Part2JpipSnapshotOrder, initial: Part2JpipSnapshotPacketState,
    state: Part2JpipSnapshotPacketState, tile: usize, styles: crate::codestream::ComponentCodingStyles,
    index: nat, before: Seq<Part2JpipAutomaticPacket>, events: Seq<Part2JpipSnapshotEvent>,
    tail: Seq<Part2JpipSnapshotEvent>, error: crate::DecodeError,
)
    requires
        part2_jpip_snapshot_parse_packets(input, parts, transitions, databins, order, 0, initial) == Ok(state),
        part2_jpip_snapshot_make_packets(input, tile as u16, styles, order, databins, state, 0, Seq::empty())
            == part2_jpip_snapshot_make_packets(input, tile as u16, styles, order, databins, state, index, before),
        part2_jpip_snapshot_capacity(events, 4, tile, order.len() as usize) == Some((Ok(()), tail)),
    ensures index < order.len()
        && part2_jpip_snapshot_tile_selected(input.selected, tile as u16)
        && part2_jpip_snapshot_component_included(input.components, order[index as int].0.component)
        && part2_jpip_snapshot_resolution(input.selected, order[index as int].0.component,
            order[index as int].0.resolution, styles) == Err(error)
        ==> part2_jpip_snapshot_acquired_packets(input, parts, transitions, databins, order,
            initial, tile, styles, events) == Some((Err(error), tail)),
{
    part2_jpip_snapshot_resolution_current_error(input, tile as u16, styles, order, databins,
        state, index, before, error);
}

pub(crate) proof fn part2_jpip_snapshot_acquired_packets_continuation<T>(
    input: Part2JpipSnapshotInput<'_>, parts: Seq<Part2OwnedTilePart>,
    transitions: Seq<Part2JpipTransition>, databins: Seq<Part2JpipDatabin>,
    order: Part2JpipSnapshotOrder, initial: Part2JpipSnapshotPacketState,
    tile: usize, styles: crate::codestream::ComponentCodingStyles,
    events: Seq<Part2JpipSnapshotEvent>,
    next: spec_fn(Seq<Part2JpipAutomaticPacket>, Seq<Part2JpipSnapshotEvent>) -> Part2JpipSnapshotRun<T>,
)
    ensures part2_jpip_snapshot_bind(part2_jpip_snapshot_acquired_packets(input, parts, transitions,
        databins, order, initial, tile, styles, events), next)
        == part2_jpip_snapshot_bind(part2_jpip_snapshot_lift(
            part2_jpip_snapshot_parse_packets(input, parts, transitions, databins, order, 0, initial), events),
            |state: Part2JpipSnapshotPacketState, events| {
            part2_jpip_snapshot_bind(part2_jpip_snapshot_capacity(events, 4, tile, order.len() as usize),
                |_unit: (), events| {
                part2_jpip_snapshot_bind(part2_jpip_snapshot_lift(part2_jpip_snapshot_make_packets(
                    input, tile as u16, styles, order, databins, state, 0, Seq::empty()), events), next)
            })
        }),
{
}

pub(crate) open spec fn part2_jpip_snapshot_tile(
    input: Part2JpipSnapshotInput<'_>, count: u64, components: u16, tile: usize,
    layout: Part2DecoderLayoutInput, raw: Seq<Seq<u8>>, headers: Seq<Seq<Seq<u8>>>,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2JpipSnapshotRun<Part2JpipSnapshotTile> {
    if tile > u16::MAX as usize {
        part2_jpip_snapshot_lift(Err(part2_jpip_range_overflow(0)), events)
    } else {
        let parts = layout.parts.filter(|part: Part2OwnedTilePart| part.tile_index == tile as u16);
        if parts.len() == 0 {
            part2_jpip_snapshot_lift(Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart)), events)
        } else {
            let first = parts[0];
            let planned = part2_progression_tile_plan_owned(&layout.size, first.coding_style,
                &first.component_coding_styles, first.component_quantizations, &first.roi_shifts,
                (tile as u16, 0), (false, 74, false), input.limits);
            part2_jpip_snapshot_bind(part2_jpip_snapshot_lift(planned, events), |plan: Part2ProgressionTilePlan, events| {
                let iterator = part1_progression_iterator_initial(plan.grid, first.coding_style.progression_order,
                    first.progression_changes, crate::limits::resource_work_limit(input.limits));
                part2_jpip_snapshot_bind(part2_jpip_snapshot_lift(iterator, events),
                    |iterator: Part1ProgressionPacketIterator, events| {
                    let ordinals = Seq::new(plan.precincts.len(), |_index: int|
                        Seq::new(first.coding_style.layers as nat, |_layer: int| None::<u16>));
                    let order = part2_jpip_snapshot_order(iterator,
                        crate::limits::resource_work_limit(input.limits), 0, ordinals, Seq::empty());
                    part2_jpip_snapshot_bind(part2_jpip_snapshot_lift(order, events),
                        |order: Part2JpipSnapshotOrder, events| {
                        part2_jpip_snapshot_bind(part2_jpip_snapshot_capacity(events, 3, tile,
                            plan.precincts.len() as usize), |_unit: (), events| {
                            let databins = part2_jpip_snapshot_databins(input, count, components, tile, plan, 0, Seq::empty());
                            part2_jpip_snapshot_bind(part2_jpip_snapshot_lift(databins, events),
                                |databins: Seq<Part2JpipDatabin>, events| {
                                if tile as nat >= raw.len() {
                                    part2_jpip_snapshot_lift(Err(part2_jpip_range_overflow(0)), events)
                                } else {
                                    let transitions = part2_jpip_parse_transitions(raw[tile as int], tile as u16);
                                    part2_jpip_snapshot_bind(part2_jpip_snapshot_lift(transitions, events),
                                        |transitions: Seq<Part2JpipTransition>, events| {
                                        let state = Part2JpipSnapshotPacketState {
                                            precincts: plan.precincts,
                                            parsed: Seq::new(plan.precincts.len(), |_index: int|
                                                Seq::new(first.coding_style.layers as nat, |_layer: int| None::<Seq<u8>>)),
                                            offsets: Seq::new(plan.precincts.len(), |_index: int| 0u64),
                                            blocked: Seq::new(plan.precincts.len(), |_index: int| false),
                                            transition: 0, packets: 0, bytes: 0,
                                        };
                                        part2_jpip_snapshot_bind(part2_jpip_snapshot_acquired_packets(
                                            input, parts, transitions, databins, order, state, tile,
                                            first.component_coding_styles, events),
                                            |packets: Seq<Part2JpipAutomaticPacket>, events| {
                                            if tile as nat >= headers.len() {
                                                part2_jpip_snapshot_lift(Err(part2_jpip_range_overflow(0)), events)
                                            } else {
                                                match part2_jpip_partition_automatic_tiles(
                                                    headers[tile as int], parts, transitions, packets) {
                                                    Err(error) => part2_jpip_snapshot_lift(Err(error), events),
                                                    Ok(parts) => part2_jpip_snapshot_lift(
                                                        Ok((parts, packets, first.coding_style.layers)), events),
                                                }
                                            }
                                        })
                                    })
                                }
                            })
                        })
                    })
                })
            })
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_snapshot_tiles(
    input: Part2JpipSnapshotInput<'_>, count: u64, components: u16, main: Seq<u8>,
    raw: Seq<Seq<u8>>, headers: Seq<Seq<Seq<u8>>>, layout: Part2DecoderLayoutInput,
    tile: nat, before: Part2JpipAutomaticTiles, maximum: u16, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2JpipSnapshotRun<Part2JpipAutomaticSnapshotResult>
    decreases if tile < headers.len() { headers.len() - tile } else { 0 },
{
    if tile >= headers.len() {
        part2_jpip_snapshot_lift(part2_jpip_snapshot_ready(input.cache, before, main, maximum, input.limits), events)
    } else {
        part2_jpip_snapshot_bind(part2_jpip_snapshot_tile(input, count, components, tile as usize,
            layout, raw, headers, events), |value: Part2JpipSnapshotTile, events| {
            match value.0 {
                None => part2_jpip_snapshot_lift(Ok((None,
                    part2_jpip_snapshot_partition_missing(input.cache, value.1, 0, Seq::empty()))), events),
                Some(parts) => part2_jpip_snapshot_tiles(input, count, components, main, raw, headers, layout,
                    tile + 1, before.push(parts), if value.2 > maximum { value.2 } else { maximum }, events),
            }
        })
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_snapshot_gather(
    input: Part2JpipSnapshotInput<'_>, count: u64, tile: u64,
    before: Seq<Seq<u8>>, missing: Seq<Part2JpipMissing>,
) -> Result<(Seq<Seq<u8>>, Seq<Part2JpipMissing>), crate::DecodeError>
    decreases count as int - tile as int,
{
    if tile >= count { Ok((before, missing)) }
    else {
        match part2_jpip_databin(2, input.stream, tile) {
            Err(error) => Err(error),
            Ok(id) => if part2_jpip_cache_complete(input.cache, id) {
                match part2_jpip_cache_view(input.cache, id) {
                    Err(error) => Err(error),
                    Ok(bytes) => part2_jpip_snapshot_gather(input, count, (tile + 1) as u64,
                        before.push(bytes), missing),
                }
            } else {
                part2_jpip_snapshot_gather(input, count, (tile + 1) as u64, before,
                    missing + part2_jpip_complete_missing(input.cache, id))
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_snapshot_normalize_tiles(
    raw: Seq<Seq<u8>>, tile: nat, before: Seq<Seq<Seq<u8>>>,
) -> Result<Seq<Seq<Seq<u8>>>, crate::DecodeError>
    decreases if tile < raw.len() { raw.len() - tile } else { 0 },
{
    if tile >= raw.len() { Ok(before) }
    else if tile > u16::MAX as nat { Err(part2_jpip_range_overflow(0)) }
    else {
        match part2_jpip_normalize_automatic_tile_headers(raw[tile as int], tile as u16) {
            Err(error) => Err(error),
            Ok(headers) => part2_jpip_snapshot_normalize_tiles(raw, tile + 1, before.push(headers)),
        }
    }
}

pub(crate) open spec fn part2_jpip_snapshot_after_gather(
    input: Part2JpipSnapshotInput<'_>, main: Seq<u8>, raw: Seq<Seq<u8>>, count: u64, components: u16,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2JpipSnapshotRun<Part2JpipAutomaticSnapshotResult> {
    if events.len() == 0 { None }
    else {
        match events[0] {
            Part2JpipSnapshotEvent::Main { calls } => {
                match part2_jpip_normalize_main_header(main, calls) {
                    None => None,
                    Some(normalized) => part2_jpip_snapshot_bind(
                        part2_jpip_snapshot_lift(normalized, events.drop_first()), |main: Seq<u8>, events| {
                        part2_jpip_snapshot_bind(part2_jpip_snapshot_capacity(events, 1, 0, raw.len() as usize),
                            |_unit: (), events| {
                            part2_jpip_snapshot_bind(part2_jpip_snapshot_lift(
                                part2_jpip_snapshot_normalize_tiles(raw, 0, Seq::empty()), events),
                                |headers: Seq<Seq<Seq<u8>>>, events| {
                                part2_jpip_snapshot_after_normalized(input, main, raw, count, components, headers, events)
                            })
                        })
                    }),
                }
            },
            _ => None,
        }
    }
}

pub(crate) open spec fn part2_jpip_snapshot_after_normalized(
    input: Part2JpipSnapshotInput<'_>, main: Seq<u8>, raw: Seq<Seq<u8>>, count: u64, components: u16,
    headers: Seq<Seq<Seq<u8>>>, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2JpipSnapshotRun<Part2JpipAutomaticSnapshotResult> {
    match part2_jpip_transition_template(main, headers, input.limits) {
        Err(error) => Some((Err(error), events)),
        Ok(template) => match part1_parse_layout(template, input.limits) {
            Err(error) => Some((Err(error), events)),
            Ok(layout) => match part2_jpip_snapshot_capacity(events, 2, 0, headers.len() as usize) {
                None => None,
                Some((Err(error), tail)) => Some((Err(error), tail)),
                Some((Ok(()), tail)) => part2_jpip_snapshot_tiles(input, count, components, main, raw, headers,
                    part2_decoder_input_from_raw(layout), 0, Seq::empty(), 0, tail),
            },
        },
    }
}

pub(crate) open spec fn part2_jpip_snapshot_admit(input: Part2JpipSnapshotInput<'_>)
    -> Result<(Seq<u8>, u64, u16), crate::DecodeError> {
    match part2_jpip_cache_view(input.cache, (6u64, crate::jpip::DatabinClass::MainHeader, input.stream, 0u64)) {
        Err(error) => Err(error),
        Ok(main) => match part2_jpip_siz_cardinality(main, input.limits) {
            Err(error) => Err(error),
            Ok(cardinality) => match part2_jpip_snapshot_component_selection(input.components, cardinality.1) {
                Err(error) => Err(error),
                Ok(()) => if cardinality.0 > usize::MAX as u64 { Err(part2_jpip_range_overflow(0)) }
                    else { Ok((main, cardinality.0, cardinality.1)) },
            },
        },
    }
}

pub(crate) open spec fn part2_jpip_snapshot_run(
    input: Part2JpipSnapshotInput<'_>, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2JpipSnapshotRun<Part2JpipAutomaticSnapshotResult> {
    match part2_jpip_databin(6, input.stream, 0) {
        Err(error) => part2_jpip_snapshot_lift(Err(error), events),
        Ok(id) => if !part2_jpip_cache_complete(input.cache, id) {
            part2_jpip_snapshot_lift(Ok((None, part2_jpip_complete_missing(input.cache, id))), events)
        } else {
            part2_jpip_snapshot_bind(part2_jpip_snapshot_lift(part2_jpip_snapshot_admit(input), events),
                |admitted: (Seq<u8>, u64, u16), events| {
                part2_jpip_snapshot_bind(part2_jpip_snapshot_capacity(
                    events, 0, 0, admitted.1 as usize), |_unit: (), events| {
                    part2_jpip_snapshot_bind(part2_jpip_snapshot_lift(
                        part2_jpip_snapshot_gather(input, admitted.1, 0, Seq::empty(), Seq::empty()), events),
                        |gathered: (Seq<Seq<u8>>, Seq<Part2JpipMissing>), events| {
                        part2_jpip_snapshot_gathered(input, admitted.0, (admitted.1, admitted.2),
                            gathered.0, gathered.1, events)
                    })
                })
            })
        },
    }
}

pub(crate) open spec fn part2_jpip_snapshot_gathered(
    input: Part2JpipSnapshotInput<'_>, main: Seq<u8>, cardinality: (u64, u16),
    raw: Seq<Seq<u8>>, missing: Seq<Part2JpipMissing>, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2JpipSnapshotRun<Part2JpipAutomaticSnapshotResult> {
    if missing.len() != 0 { part2_jpip_snapshot_lift(Ok((None, missing)), events) }
    else { part2_jpip_snapshot_after_gather(input, main, raw, cardinality.0, cardinality.1, events) }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_automatic_snapshot_result(
    cache: Part2JpipCache, stream: u64, selection: Option<Part2DecodeSelection>, components: Seq<u16>,
    limits: &crate::ResourceLimits, result: Result<Part2JpipAutomaticSnapshotResult, crate::DecodeError>,
) -> bool {
    exists|events: Seq<Part2JpipSnapshotEvent>| part2_jpip_snapshot_run(
        Part2JpipSnapshotInput { cache, stream, selected: selection, components, limits }, events)
            == Some((result, Seq::empty()))
}

}
