#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) proof fn jpip_snapshot_plan_errors(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
            root.tile <= u16::MAX as nat, parts.len() != 0,
            parts == root.layout.parts.filter(|part: crate::specs::Part2OwnedTilePart| part.tile_index == root.tile as u16),
        ensures forall|error: DecodeError|
            crate::specs::part2_progression_tile_plan_owned(&root.layout.size, parts[0].coding_style,
                &parts[0].component_coding_styles, parts[0].component_quantizations, &parts[0].roi_shifts,
                (root.tile as u16, 0), (false, 74, false), root.input.limits) == Err(error)
            ==> crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
                root.input.selected, root.input.components, root.input.limits, Err(error)),
    {
        assert forall|error: DecodeError|
            crate::specs::part2_progression_tile_plan_owned(&root.layout.size, parts[0].coding_style,
                &parts[0].component_coding_styles, parts[0].component_quantizations, &parts[0].roi_shifts,
                (root.tile as u16, 0), (false, 74, false), root.input.limits) == Err(error)
            implies crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
                root.input.selected, root.input.components, root.input.limits, Err(error)) by {
            jpip_snapshot_plan_error(root, parts, error);
        }
    }

    pub(crate) proof fn jpip_snapshot_iterator_errors(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>,
        plan: crate::specs::Part2ProgressionTilePlan,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
            root.tile <= u16::MAX as nat, parts.len() != 0,
            parts == root.layout.parts.filter(|part: crate::specs::Part2OwnedTilePart| part.tile_index == root.tile as u16),
            crate::specs::part2_progression_tile_plan_owned(&root.layout.size, parts[0].coding_style,
                &parts[0].component_coding_styles, parts[0].component_quantizations, &parts[0].roi_shifts,
                (root.tile as u16, 0), (false, 74, false), root.input.limits) == Ok(plan),
        ensures forall|error: DecodeError|
            crate::specs::part1_progression_iterator_initial(plan.grid, parts[0].coding_style.progression_order,
                parts[0].progression_changes, crate::limits::resource_work_limit(root.input.limits)) == Err(error)
            ==> crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
                root.input.selected, root.input.components, root.input.limits, Err(error)),
    {
        assert forall|error: DecodeError|
            crate::specs::part1_progression_iterator_initial(plan.grid, parts[0].coding_style.progression_order,
                parts[0].progression_changes, crate::limits::resource_work_limit(root.input.limits)) == Err(error)
            implies crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
                root.input.selected, root.input.components, root.input.limits, Err(error)) by {
            jpip_snapshot_iterator_error(root, parts, plan, error);
        }
    }

    pub(crate) proof fn jpip_snapshot_order_errors(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>,
        plan: crate::specs::Part2ProgressionTilePlan, iterator: crate::specs::Part1ProgressionPacketIterator,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
            root.tile <= u16::MAX as nat, parts.len() != 0,
            parts == root.layout.parts.filter(|part: crate::specs::Part2OwnedTilePart| part.tile_index == root.tile as u16),
            crate::specs::part2_progression_tile_plan_owned(&root.layout.size, parts[0].coding_style,
                &parts[0].component_coding_styles, parts[0].component_quantizations, &parts[0].roi_shifts,
                (root.tile as u16, 0), (false, 74, false), root.input.limits) == Ok(plan),
            crate::specs::part1_progression_iterator_initial(plan.grid, parts[0].coding_style.progression_order,
                parts[0].progression_changes, crate::limits::resource_work_limit(root.input.limits)) == Ok(iterator),
        ensures forall|error: DecodeError|
            crate::specs::part2_jpip_snapshot_order(iterator, crate::limits::resource_work_limit(root.input.limits), 0,
                Seq::new(plan.precincts.len(), |_row: int| Seq::new(parts[0].coding_style.layers as nat, |_layer: int| None::<u16>)),
                Seq::empty()) == Err(error)
            ==> crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
                root.input.selected, root.input.components, root.input.limits, Err(error)),
    {
        assert forall|error: DecodeError|
            crate::specs::part2_jpip_snapshot_order(iterator, crate::limits::resource_work_limit(root.input.limits), 0,
                Seq::new(plan.precincts.len(), |_row: int| Seq::new(parts[0].coding_style.layers as nat, |_layer: int| None::<u16>)),
                Seq::empty()) == Err(error)
            implies crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
                root.input.selected, root.input.components, root.input.limits, Err(error)) by {
            jpip_snapshot_order_error(root, parts, plan, iterator, error);
        }
    }
    pub(crate) proof fn jpip_missing_ref_projection(
        values: Seq<JpipMissingRange>, projected: Seq<crate::specs::Part2JpipMissing>,
        id: crate::specs::Part2JpipDatabin,
    )
        requires projected == values.map_values(|entry: JpipMissingRange| jpip_missing_view(entry)),
        ensures
            (exists|index: int| 0 <= index < values.as_ref().len()
                && crate::specs::part2_jpip_identity(jpip_missing_view(*values.as_ref()[index]).0, id))
            <==> (exists|index: int| 0 <= index < projected.len()
                && crate::specs::part2_jpip_identity(projected[index].0, id)),
    {
        assert forall|index: int| 0 <= index < values.len()
            implies jpip_missing_view(*#[trigger] values.as_ref()[index]) == projected[index] by {
            values.lemma_as_ref_index(index);
        }
        assert(values.as_ref().len() == projected.len());
        if exists|index: int| 0 <= index < values.as_ref().len()
            && crate::specs::part2_jpip_identity(jpip_missing_view(*values.as_ref()[index]).0, id) {
            let index = choose|index: int| 0 <= index < values.as_ref().len()
                && crate::specs::part2_jpip_identity(jpip_missing_view(*values.as_ref()[index]).0, id);
            values.lemma_as_ref_index(index);
            assert(crate::specs::part2_jpip_identity(projected[index].0, id));
        }
        if exists|index: int| 0 <= index < projected.len()
            && crate::specs::part2_jpip_identity(projected[index].0, id) {
            let index = choose|index: int| 0 <= index < projected.len()
                && crate::specs::part2_jpip_identity(projected[index].0, id);
            values.lemma_as_ref_index(index);
            assert(crate::specs::part2_jpip_identity(jpip_missing_view(*values.as_ref()[index]).0, id));
        }
    }
    pub(crate) proof fn jpip_snapshot_packet_error(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>,
        transitions: Seq<crate::specs::Part2JpipTransition>, databins: Seq<crate::specs::Part2JpipDatabin>,
        order: crate::specs::Part2JpipSnapshotOrder, initial: crate::specs::Part2JpipSnapshotPacketState,
        final_state: crate::specs::Part2JpipSnapshotPacketState,
        capacity: crate::specs::Part2JpipSnapshotEvent, error: DecodeError,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(), parts.len() != 0,
            root.tile <= u16::MAX as nat,
            jpip_snapshot_tile_acquisition_known(root, parts, transitions, databins, order, initial, capacity),
            crate::specs::part2_jpip_snapshot_parse_packets(root.input, parts, transitions, databins, order, 0, initial) == Ok(final_state),
            crate::specs::part2_jpip_snapshot_make_packets(root.input, root.tile as u16, parts[0].component_coding_styles,
                order, databins, final_state, 0, Seq::empty()) == Err(error),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
            root.input.selected, root.input.components, root.input.limits, Err(error)),
    {
        let accepted = crate::specs::Part2JpipSnapshotEvent::Capacity {
            site: 4, tile: root.tile as usize, elements: order.len() as usize, succeeded: true };
        assert(seq![accepted].drop_first() =~= Seq::empty());
        reveal(jpip_snapshot_tile_acquisition_known);
        assert(seq![capacity, accepted] =~= seq![capacity] + seq![accepted]);
        assert(crate::specs::part2_jpip_snapshot_acquired_packets(root.input, parts, transitions, databins,
            order, initial, root.tile as usize, parts[0].component_coding_styles, seq![accepted])
            == Some((Err(error), Seq::empty())));
        jpip_snapshot_tile_root_error(root, seq![capacity, accepted], error);
    }
    pub(crate) proof fn jpip_snapshot_mapping_capacity_error(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>,
        plan: crate::specs::Part2ProgressionTilePlan, iterator: crate::specs::Part1ProgressionPacketIterator,
        order: crate::specs::Part2JpipSnapshotOrder,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
            jpip_snapshot_plan_order_known(root, parts, plan, iterator, order),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
            root.input.selected, root.input.components, root.input.limits, Err(DecodeError::AllocationFailed)),
    {
        let events = seq![crate::specs::Part2JpipSnapshotEvent::Capacity {
            site: 3, tile: root.tile as usize, elements: plan.precincts.len() as usize, succeeded: false }];
        assert(events.drop_first() =~= Seq::empty());
        jpip_snapshot_tile_root_error(root, events, DecodeError::AllocationFailed);
    }

    pub(crate) proof fn jpip_snapshot_packet_capacity_error(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>,
        transitions: Seq<crate::specs::Part2JpipTransition>, databins: Seq<crate::specs::Part2JpipDatabin>,
        order: crate::specs::Part2JpipSnapshotOrder, initial: crate::specs::Part2JpipSnapshotPacketState,
        final_state: crate::specs::Part2JpipSnapshotPacketState,
        capacity: crate::specs::Part2JpipSnapshotEvent,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
            jpip_snapshot_tile_acquisition_known(root, parts, transitions, databins, order, initial, capacity),
            crate::specs::part2_jpip_snapshot_parse_packets(root.input, parts, transitions, databins, order, 0, initial) == Ok(final_state),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
            root.input.selected, root.input.components, root.input.limits, Err(DecodeError::AllocationFailed)),
    {
        let refused = crate::specs::Part2JpipSnapshotEvent::Capacity {
            site: 4, tile: root.tile as usize, elements: order.len() as usize, succeeded: false };
        assert(seq![refused].drop_first() =~= Seq::empty());
        reveal(jpip_snapshot_tile_acquisition_known);
        assert(seq![capacity, refused] =~= seq![capacity] + seq![refused]);
        assert(crate::specs::part2_jpip_snapshot_acquired_packets(root.input, parts, transitions, databins,
            order, initial, root.tile as usize, parts[0].component_coding_styles, seq![refused])
            == Some((Err(DecodeError::AllocationFailed), Seq::empty())));
        jpip_snapshot_tile_root_error(root, seq![capacity, refused], DecodeError::AllocationFailed);
    }
    pub(crate) proof fn jpip_snapshot_plan_error(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>, error: DecodeError,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
            root.tile <= u16::MAX as nat, parts.len() != 0,
            parts == root.layout.parts.filter(|part: crate::specs::Part2OwnedTilePart| part.tile_index == root.tile as u16),
            crate::specs::part2_progression_tile_plan_owned(&root.layout.size, parts[0].coding_style,
                &parts[0].component_coding_styles, parts[0].component_quantizations, &parts[0].roi_shifts,
                (root.tile as u16, 0), (false, 74, false), root.input.limits) == Err(error),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
            root.input.selected, root.input.components, root.input.limits, Err(error)),
    {
        jpip_snapshot_tile_root_error(root, Seq::empty(), error);
    }

    pub(crate) proof fn jpip_snapshot_iterator_error(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>,
        plan: crate::specs::Part2ProgressionTilePlan, error: DecodeError,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
            root.tile <= u16::MAX as nat, parts.len() != 0,
            parts == root.layout.parts.filter(|part: crate::specs::Part2OwnedTilePart| part.tile_index == root.tile as u16),
            crate::specs::part2_progression_tile_plan_owned(&root.layout.size, parts[0].coding_style,
                &parts[0].component_coding_styles, parts[0].component_quantizations, &parts[0].roi_shifts,
                (root.tile as u16, 0), (false, 74, false), root.input.limits) == Ok(plan),
            crate::specs::part1_progression_iterator_initial(plan.grid, parts[0].coding_style.progression_order,
                parts[0].progression_changes, crate::limits::resource_work_limit(root.input.limits)) == Err(error),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
            root.input.selected, root.input.components, root.input.limits, Err(error)),
    {
        jpip_snapshot_tile_root_error(root, Seq::empty(), error);
    }

    pub(crate) proof fn jpip_snapshot_order_error(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>,
        plan: crate::specs::Part2ProgressionTilePlan, iterator: crate::specs::Part1ProgressionPacketIterator,
        error: DecodeError,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
            root.tile <= u16::MAX as nat, parts.len() != 0,
            parts == root.layout.parts.filter(|part: crate::specs::Part2OwnedTilePart| part.tile_index == root.tile as u16),
            crate::specs::part2_progression_tile_plan_owned(&root.layout.size, parts[0].coding_style,
                &parts[0].component_coding_styles, parts[0].component_quantizations, &parts[0].roi_shifts,
                (root.tile as u16, 0), (false, 74, false), root.input.limits) == Ok(plan),
            crate::specs::part1_progression_iterator_initial(plan.grid, parts[0].coding_style.progression_order,
                parts[0].progression_changes, crate::limits::resource_work_limit(root.input.limits)) == Ok(iterator),
            crate::specs::part2_jpip_snapshot_order(iterator, crate::limits::resource_work_limit(root.input.limits), 0,
                Seq::new(plan.precincts.len(), |_row: int| Seq::new(parts[0].coding_style.layers as nat, |_layer: int| None::<u16>)),
                Seq::empty()) == Err(error),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
            root.input.selected, root.input.components, root.input.limits, Err(error)),
    {
        jpip_snapshot_tile_root_error(root, Seq::empty(), error);
    }

    pub(crate) proof fn jpip_snapshot_mapping_error(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>,
        plan: crate::specs::Part2ProgressionTilePlan, iterator: crate::specs::Part1ProgressionPacketIterator,
        order: crate::specs::Part2JpipSnapshotOrder, error: DecodeError,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
            jpip_snapshot_plan_order_known(root, parts, plan, iterator, order),
            crate::specs::part2_jpip_snapshot_databins(root.input, root.count, root.components,
                root.tile as usize, plan, 0, Seq::empty()) == Err(error),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
            root.input.selected, root.input.components, root.input.limits, Err(error)),
    {
        let events = seq![crate::specs::Part2JpipSnapshotEvent::Capacity {
            site: 3, tile: root.tile as usize, elements: plan.precincts.len() as usize, succeeded: true }];
        assert(events.drop_first() =~= Seq::empty());
        jpip_snapshot_tile_root_error(root, events, error);
    }

    pub(crate) proof fn jpip_snapshot_acquisition_error(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>,
        transitions: Seq<crate::specs::Part2JpipTransition>, databins: Seq<crate::specs::Part2JpipDatabin>,
        order: crate::specs::Part2JpipSnapshotOrder, initial: crate::specs::Part2JpipSnapshotPacketState,
        capacity: crate::specs::Part2JpipSnapshotEvent, error: DecodeError,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
            jpip_snapshot_tile_acquisition_known(root, parts, transitions, databins, order, initial, capacity),
            crate::specs::part2_jpip_snapshot_parse_packets(root.input, parts, transitions, databins, order, 0, initial) == Err(error),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
            root.input.selected, root.input.components, root.input.limits, Err(error)),
    {
        reveal(jpip_snapshot_tile_acquisition_known);
        assert(seq![capacity] =~= seq![capacity] + Seq::<crate::specs::Part2JpipSnapshotEvent>::empty());
        assert(crate::specs::part2_jpip_snapshot_acquired_packets(root.input, parts, transitions, databins,
            order, initial, root.tile as usize, parts[0].component_coding_styles, Seq::empty())
            == Some((Err(error), Seq::empty())));
        assert(crate::specs::part2_jpip_snapshot_tile(root.input, root.count, root.components, root.tile as usize,
            root.layout, root.raw, root.headers, seq![capacity]) == Some((Err(error), Seq::empty())));
        jpip_snapshot_tile_root_error(root, seq![capacity], error);
    }
    pub(crate) proof fn jpip_snapshot_root_emit_error(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, available: u16, error: DecodeError,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile >= root.headers.len(),
            crate::specs::part2_jpip_snapshot_available(root.before, 0, 0, 0, root.maximum) == available,
            available > 0,
            crate::specs::part2_jpip_snapshot_emit_tiles(root.before, available, 0, root.main) == Err(error),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
            root.input.selected, root.input.components, root.input.limits, Err(error)),
    {
        jpip_snapshot_root_ready_result(root, Err(error));
    }
    pub(crate) proof fn jpip_snapshot_tile_root_missing(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>,
        events: Seq<crate::specs::Part2JpipSnapshotEvent>,
        packets: Seq<crate::specs::Part2JpipAutomaticPacket>, layers: u16,
        missing: Seq<crate::specs::Part2JpipMissing>,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
            crate::specs::part2_jpip_snapshot_tile(root.input, root.count, root.components, root.tile as usize,
                root.layout, root.raw, root.headers, events) == Some((Ok((None, packets, layers)), Seq::empty())),
            missing == crate::specs::part2_jpip_snapshot_partition_missing(root.input.cache, packets, 0, Seq::empty()),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
            root.input.selected, root.input.components, root.input.limits, Ok((None, missing))),
    {
        reveal(crate::specs::part2_jpip_snapshot_tile_root);
        reveal(crate::specs::part2_jpip_snapshot_tiles);
        assert(root.events + events + Seq::empty() =~= root.events + events);
        assert(crate::specs::part2_jpip_snapshot_run(root.input, root.events + events)
            == crate::specs::part2_jpip_snapshot_tiles(root.input, root.count, root.components, root.main,
                root.raw, root.headers, root.layout, root.tile, root.before, root.maximum, events));
        assert(crate::specs::part2_jpip_snapshot_run(root.input, root.events + events)
            == Some((Ok((None, missing)), Seq::empty())));
        jpip_snapshot_result_witness(root.input, root.events + events, Ok((None, missing)));
    }
    pub(crate) open spec fn jpip_snapshot_ready_context(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, input: crate::specs::Part2JpipSnapshotInput<'_>,
        tiles: crate::specs::Part2JpipAutomaticTiles, main: Seq<u8>, maximum: u16,
    ) -> bool {
        crate::specs::part2_jpip_snapshot_tile_root(root) && root.tile >= root.headers.len()
            && root.input == input && root.before == tiles && root.main == main && root.maximum == maximum
    }
    pub(crate) closed spec fn jpip_automatic_snapshot_view(value: &AutomaticSnapshot)
        -> crate::specs::Part2JpipAutomaticSnapshot {
        (jpip_byte_view(&value.codestream), value.available_layers, value.layers,
            jpip_missing_views(&value.missing))
    }

    pub(crate) closed spec fn jpip_automatic_snapshot_result_view(value: &AutomaticSnapshotResult)
        -> crate::specs::Part2JpipAutomaticSnapshotResult {
        (match value.ready { None => None, Some(snapshot) => Some(jpip_automatic_snapshot_view(&snapshot)) },
            jpip_missing_views(&value.missing))
    }

    pub(crate) open spec fn jpip_automatic_snapshot_outcome(value: Result<AutomaticSnapshotResult, DecodeError>)
        -> Result<crate::specs::Part2JpipAutomaticSnapshotResult, DecodeError> {
        match value { Err(error) => Err(error), Ok(snapshot) => Ok(jpip_automatic_snapshot_result_view(&snapshot)) }
    }

    pub(crate) proof fn jpip_snapshot_root_ready_result(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>,
        result: Result<crate::specs::Part2JpipAutomaticSnapshotResult, DecodeError>,
    )
        requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile >= root.headers.len(),
            crate::specs::part2_jpip_snapshot_ready(root.input.cache, root.before, root.main,
                root.maximum, root.input.limits) == result,
        ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
            root.input.selected, root.input.components, root.input.limits, result),
    {
        reveal(crate::specs::part2_jpip_snapshot_tile_root);
        reveal(crate::specs::part2_jpip_snapshot_tiles);
        assert(root.events + Seq::empty() =~= root.events);
        assert(crate::specs::part2_jpip_snapshot_run(root.input, root.events + Seq::empty())
            == crate::specs::part2_jpip_snapshot_tiles(root.input, root.count, root.components, root.main,
                root.raw, root.headers, root.layout, root.tile, root.before, root.maximum, Seq::empty()));
        assert(crate::specs::part2_jpip_snapshot_tiles(root.input, root.count, root.components, root.main,
            root.raw, root.headers, root.layout, root.tile, root.before, root.maximum, Seq::empty())
            == Some((result, Seq::empty())));
        assert(crate::specs::part2_jpip_snapshot_run(root.input, root.events)
            == Some((result, Seq::empty())));
        jpip_snapshot_result_witness(root.input, root.events, result);
    }

    pub(crate) proof fn jpip_snapshot_layout_success_known<'a>()
        ensures forall|layout: crate::codestream::CodestreamLayout<'a>|
            #[trigger] crate::codestream::complete_layout_outcome(Ok(layout)).is_ok(),
    {
        assert forall|layout: crate::codestream::CodestreamLayout<'a>|
            crate::codestream::complete_layout_outcome(Ok(layout)).is_ok() by {
            crate::codestream::decoder_layout_main_info_matches_raw(&layout);
        }
    }
    pub(crate) proof fn jpip_none_clone<T: Clone>(value: Option<T>)
        requires vstd::pervasive::cloned(None::<T>, value),
        ensures value.is_none(),
    {
        reveal(vstd::pervasive::cloned);
        reveal(vstd::pervasive::strictly_cloned);
    }

    pub(crate) proof fn jpip_none_row_clone_law<T: Clone>()
        ensures forall|before: Vec<Option<T>>, after: Vec<Option<T>>|
            #[trigger] vstd::pervasive::cloned(before, after)
                && (forall|index: int| 0 <= index < before@.len() ==> #[trigger] before@[index].is_none())
            ==> after@ == Seq::new(before@.len(), |_index: int| None::<T>),
    {
        reveal(vstd::pervasive::cloned);
        reveal(vstd::pervasive::strictly_cloned);
        assert forall|before: Vec<Option<T>>, after: Vec<Option<T>>|
            vstd::pervasive::cloned(before, after)
                && (forall|index: int| 0 <= index < before@.len() ==> #[trigger] before@[index].is_none())
            implies after@ == Seq::new(before@.len(), |_index: int| None::<T>) by {
            assert(after@.len() == before@.len());
            assert forall|index: int| 0 <= index < after@.len()
                implies #[trigger] after@[index].is_none() by {
                assert(before@[index].is_none());
                assert(vstd::pervasive::cloned(before@[index], after@[index]));
                jpip_none_clone(after@[index]);
            }
            let expected = Seq::new(before@.len(), |_index: int| None::<T>);
            assert forall|index: int| 0 <= index < after@.len()
                implies #[trigger] after@[index] == expected[index] by {
                assert(after@[index] == None::<T>);
            }
            assert(after@ =~= expected);
        }
    }
    pub(crate) open spec fn jpip_snapshot_root_frame(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, main: Seq<u8>,
        raw: Seq<Seq<u8>>, headers: Seq<Seq<Seq<u8>>>, layout: crate::specs::Part2DecoderLayoutInput,
        before: crate::specs::Part2JpipAutomaticTiles,
    ) -> bool {
        root.main == main && root.raw == raw && root.headers == headers
            && root.layout == layout && root.before == before
    }
    pub(crate) open spec fn jpip_snapshot_active_tile(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, count: u64, components: u16, tile: usize,
        raw: Seq<Seq<u8>>, headers: Seq<Seq<Seq<u8>>>,
    ) -> bool {
        crate::specs::part2_jpip_snapshot_tile_root(root) && root.count == count
            && root.components == components && root.tile == tile as nat
            && root.raw == raw && root.headers == headers && root.tile < headers.len()
    }
    pub(crate) open spec fn jpip_snapshot_plan_order_known(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>,
        parts: Seq<crate::specs::Part2OwnedTilePart>, plan: crate::specs::Part2ProgressionTilePlan,
        iterator: crate::specs::Part1ProgressionPacketIterator, order: crate::specs::Part2JpipSnapshotOrder,
    ) -> bool {
        root.tile <= u16::MAX as nat && root.tile < root.raw.len()
        && parts.len() != 0 && parts == root.layout.parts.filter(
            |part: crate::specs::Part2OwnedTilePart| part.tile_index == root.tile as u16)
        && crate::specs::part2_progression_tile_plan_owned(&root.layout.size, parts[0].coding_style,
            &parts[0].component_coding_styles, parts[0].component_quantizations, &parts[0].roi_shifts,
            (root.tile as u16, 0), (false, 74, false), root.input.limits) == Ok(plan)
        && crate::specs::part1_progression_iterator_initial(plan.grid, parts[0].coding_style.progression_order,
            parts[0].progression_changes, crate::limits::resource_work_limit(root.input.limits)) == Ok(iterator)
        && crate::specs::part2_jpip_snapshot_order(iterator, crate::limits::resource_work_limit(root.input.limits),
            0, Seq::new(plan.precincts.len(), |_index: int|
                Seq::new(parts[0].coding_style.layers as nat, |_layer: int| None::<u16>)), Seq::empty()) == Ok(order)
    }

    pub(crate) open spec fn jpip_snapshot_tile_acquisition_known(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>, parts: Seq<crate::specs::Part2OwnedTilePart>,
        transitions: Seq<crate::specs::Part2JpipTransition>, databins: Seq<crate::specs::Part2JpipDatabin>,
        order: crate::specs::Part2JpipSnapshotOrder, initial: crate::specs::Part2JpipSnapshotPacketState,
        capacity: crate::specs::Part2JpipSnapshotEvent,
    ) -> bool {
        forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
            #[trigger] crate::specs::part2_jpip_snapshot_tile(root.input, root.count, root.components,
                root.tile as usize, root.layout, root.raw, root.headers, seq![capacity] + tail)
            == crate::specs::part2_jpip_snapshot_bind(crate::specs::part2_jpip_snapshot_acquired_packets(
                root.input, parts, transitions, databins, order, initial, root.tile as usize,
                parts[0].component_coding_styles, tail),
                |packets, events| jpip_snapshot_tile_finish(root, parts, transitions, packets, events))
    }

    pub(crate) closed spec fn jpip_automatic_tiles_view(values: Seq<AutomaticTile>)
        -> crate::specs::Part2JpipAutomaticTiles {
        values.map_values(|tile: AutomaticTile| tile.parts@.map_values(
            |part: AutomaticTilePart| jpip_automatic_tile_part_view(&part)))
    }

    pub(crate) open spec fn jpip_snapshot_tile_finish(
        root: crate::specs::Part2JpipSnapshotTileRoot<'_>,
        parts: Seq<crate::specs::Part2OwnedTilePart>,
        transitions: Seq<crate::specs::Part2JpipTransition>,
        packets: Seq<crate::specs::Part2JpipAutomaticPacket>,
        events: Seq<crate::specs::Part2JpipSnapshotEvent>,
    ) -> crate::specs::Part2JpipSnapshotRun<crate::specs::Part2JpipSnapshotTile> {
        if root.tile >= root.headers.len() {
            crate::specs::part2_jpip_snapshot_lift(Err(crate::specs::part2_jpip_range_overflow(0)), events)
        } else {
            match crate::specs::part2_jpip_partition_automatic_tiles(
                root.headers[root.tile as int], parts, transitions, packets) {
                Err(error) => crate::specs::part2_jpip_snapshot_lift(Err(error), events),
                Ok(partitioned) => crate::specs::part2_jpip_snapshot_lift(
                    Ok((partitioned, packets, parts[0].coding_style.layers)), events),
            }
        }
    }

            pub(crate) open spec fn jpip_snapshot_initial_packets(
                plan: crate::specs::Part2ProgressionTilePlan, layers: u16,
            ) -> crate::specs::Part2JpipSnapshotPacketState {
                crate::specs::Part2JpipSnapshotPacketState {
                    precincts: plan.precincts,
                    parsed: Seq::new(plan.precincts.len(), |_index: int|
                        Seq::new(layers as nat, |_layer: int| None::<Seq<u8>>)),
                    offsets: Seq::new(plan.precincts.len(), |_index: int| 0u64),
                    blocked: Seq::new(plan.precincts.len(), |_index: int| false),
                    transition: 0, packets: 0, bytes: 0,
                }
            }

            pub(crate) proof fn jpip_snapshot_tile_acquisition_prefix(
                root: crate::specs::Part2JpipSnapshotTileRoot<'_>,
                parts: Seq<crate::specs::Part2OwnedTilePart>,
                plan: crate::specs::Part2ProgressionTilePlan,
                iterator: crate::specs::Part1ProgressionPacketIterator,
                order: crate::specs::Part2JpipSnapshotOrder,
                databins: Seq<crate::specs::Part2JpipDatabin>,
                transitions: Seq<crate::specs::Part2JpipTransition>,
                initial: crate::specs::Part2JpipSnapshotPacketState,
            )
                requires root.tile <= u16::MAX as nat, root.tile < root.raw.len(),
                    parts == root.layout.parts.filter(
                        |part: crate::specs::Part2OwnedTilePart| part.tile_index == root.tile as u16),
                    parts.len() != 0,
                    crate::specs::part2_progression_tile_plan_owned(&root.layout.size, parts[0].coding_style,
                        &parts[0].component_coding_styles, parts[0].component_quantizations, &parts[0].roi_shifts,
                        (root.tile as u16, 0), (false, 74, false), root.input.limits) == Ok(plan),
                    crate::specs::part1_progression_iterator_initial(plan.grid, parts[0].coding_style.progression_order,
                        parts[0].progression_changes, crate::limits::resource_work_limit(root.input.limits)) == Ok(iterator),
                    crate::specs::part2_jpip_snapshot_order(iterator, crate::limits::resource_work_limit(root.input.limits),
                        0, Seq::new(plan.precincts.len(), |_index: int|
                            Seq::new(parts[0].coding_style.layers as nat, |_layer: int| None::<u16>)), Seq::empty()) == Ok(order),
                    crate::specs::part2_jpip_snapshot_databins(root.input, root.count, root.components,
                        root.tile as usize, plan, 0, Seq::empty()) == Ok(databins),
                    crate::specs::part2_jpip_parse_transitions(root.raw[root.tile as int], root.tile as u16) == Ok(transitions),
                    initial == jpip_snapshot_initial_packets(plan, parts[0].coding_style.layers),
                ensures forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                    #[trigger] crate::specs::part2_jpip_snapshot_tile(root.input, root.count, root.components, root.tile as usize,
                        root.layout, root.raw, root.headers,
                        seq![crate::specs::Part2JpipSnapshotEvent::Capacity {
                            site: 3, tile: root.tile as usize, elements: plan.precincts.len() as usize, succeeded: true }] + tail)
                        == crate::specs::part2_jpip_snapshot_bind(
                            crate::specs::part2_jpip_snapshot_acquired_packets(root.input, parts, transitions, databins,
                                order, initial, root.tile as usize, parts[0].component_coding_styles, tail),
                            |packets, events| jpip_snapshot_tile_finish(root, parts, transitions, packets, events)),
            {
                assert forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                    #[trigger] crate::specs::part2_jpip_snapshot_tile(root.input, root.count, root.components, root.tile as usize,
                        root.layout, root.raw, root.headers,
                        seq![crate::specs::Part2JpipSnapshotEvent::Capacity {
                            site: 3, tile: root.tile as usize, elements: plan.precincts.len() as usize, succeeded: true }] + tail)
                        == crate::specs::part2_jpip_snapshot_bind(
                            crate::specs::part2_jpip_snapshot_acquired_packets(root.input, parts, transitions, databins,
                                order, initial, root.tile as usize, parts[0].component_coding_styles, tail),
                            |packets, events| jpip_snapshot_tile_finish(root, parts, transitions, packets, events)) by {
                    let event = crate::specs::Part2JpipSnapshotEvent::Capacity {
                        site: 3, tile: root.tile as usize, elements: plan.precincts.len() as usize, succeeded: true };
                    assert((seq![event] + tail).drop_first() =~= tail);
                }
            }

            pub(crate) proof fn jpip_snapshot_tile_root_error(
                root: crate::specs::Part2JpipSnapshotTileRoot<'_>,
                events: Seq<crate::specs::Part2JpipSnapshotEvent>, error: DecodeError,
            )
                requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
                    crate::specs::part2_jpip_snapshot_tile(root.input, root.count, root.components, root.tile as usize,
                        root.layout, root.raw, root.headers, events) == Some((Err(error), Seq::empty())),
                ensures crate::specs::part2_jpip_automatic_snapshot_result(root.input.cache, root.input.stream,
                    root.input.selected, root.input.components, root.input.limits, Err(error)),
            {
                reveal(crate::specs::part2_jpip_snapshot_tile_root);
                reveal(crate::specs::part2_jpip_snapshot_tiles);
                assert(crate::specs::part2_jpip_snapshot_run(root.input, root.events + events)
                    == crate::specs::part2_jpip_snapshot_tiles(root.input, root.count, root.components, root.main,
                        root.raw, root.headers, root.layout, root.tile, root.before, root.maximum, events));
                assert(crate::specs::part2_jpip_snapshot_tiles(root.input, root.count, root.components, root.main,
                    root.raw, root.headers, root.layout, root.tile, root.before, root.maximum, events)
                    == Some((Err(error), Seq::empty())));
                assert(crate::specs::part2_jpip_snapshot_run(root.input, root.events + events)
                    == Some((Err(error), Seq::empty())));
                jpip_snapshot_result_witness(root.input, root.events + events, Err(error));
            }

            pub(crate) proof fn jpip_snapshot_tile_root_advance(
                root: crate::specs::Part2JpipSnapshotTileRoot<'_>,
                events: Seq<crate::specs::Part2JpipSnapshotEvent>,
                parts: Seq<crate::specs::Part2JpipAutomaticTilePart>,
                packets: Seq<crate::specs::Part2JpipAutomaticPacket>, layers: u16,
            )
                requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len(),
                    forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                        crate::specs::part2_jpip_snapshot_tile(root.input, root.count, root.components, root.tile as usize,
                            root.layout, root.raw, root.headers, events + tail)
                            == Some((Ok((Some(parts), packets, layers)), tail)),
                ensures crate::specs::part2_jpip_snapshot_tile_root(crate::specs::Part2JpipSnapshotTileRoot {
                    events: root.events + events, tile: root.tile + 1, before: root.before.push(parts),
                    maximum: if layers > root.maximum { layers } else { root.maximum }, ..root }),
            {
                reveal(crate::specs::part2_jpip_snapshot_tile_root);
                reveal(crate::specs::part2_jpip_snapshot_tiles);
                assert forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                    crate::specs::part2_jpip_snapshot_run(root.input, (root.events + events) + tail)
                        == crate::specs::part2_jpip_snapshot_tiles(root.input, root.count, root.components, root.main,
                            root.raw, root.headers, root.layout, root.tile + 1, root.before.push(parts),
                            if layers > root.maximum { layers } else { root.maximum }, tail) by {
                    assert((root.events + events) + tail =~= root.events + (events + tail));
                    assert(crate::specs::part2_jpip_snapshot_run(root.input, root.events + (events + tail))
                        == crate::specs::part2_jpip_snapshot_tiles(root.input, root.count, root.components, root.main,
                            root.raw, root.headers, root.layout, root.tile, root.before, root.maximum, events + tail));
                }
            }
    pub(crate) proof fn jpip_snapshot_decode_packet_known(
        initial: crate::specs::Part1PacketPrecinctState,
        template: &crate::codestream::TilePartPayload<'_>, data: Seq<u8>,
        sequence: u16, layer: u16, limits: &ResourceLimits,
    )
        ensures crate::specs::part2_jpip_snapshot_decode_packet(initial,
            crate::codestream::tile_part_owned_view(template), data, sequence, layer, limits)
            == crate::specs::part1_jpip_precinct_packet(initial, template, data, sequence, layer, limits),
    {
    }

    pub closed spec fn jpip_automatic_packet_view(value: &AutomaticPacket)
        -> crate::specs::Part2JpipAutomaticPacket {
        (databin_id_view(value.databin), jpip_parsed_packet_value(value.bytes),
            value.next_offset, value.required, value.ordinal, value.layer)
    }

    pub open spec fn jpip_automatic_packets_view(values: &[AutomaticPacket])
        -> Seq<crate::specs::Part2JpipAutomaticPacket> {
        values@.map_values(|value: AutomaticPacket| jpip_automatic_packet_view(&value))
    }

    pub closed spec fn jpip_automatic_tile_part_view(value: &AutomaticTilePart)
        -> crate::specs::Part2JpipAutomaticTilePart {
        (value.header@, value.packets@.map_values(|packet: AutomaticPacket| jpip_automatic_packet_view(&packet)),
            value.sop, value.eph)
    }

    pub open spec fn jpip_automatic_partition_outcome(value: Result<Option<Vec<AutomaticTilePart>>, DecodeError>)
        -> Result<Option<Seq<crate::specs::Part2JpipAutomaticTilePart>>, DecodeError> {
        match value {
            Err(error) => Err(error),
            Ok(None) => Ok(None),
            Ok(Some(parts)) => Ok(Some(parts@.map_values(|part: AutomaticTilePart| jpip_automatic_tile_part_view(&part)))),
        }
    }

    pub closed spec fn jpip_automatic_headers_view(value: &AutomaticHeaders)
        -> crate::specs::Part2JpipAutomaticHeaders {
        (value.main@, value.tiles@.map_values(|tile: Vec<u8>| tile@), value.tile_count, value.components)
    }

    pub open spec fn jpip_automatic_headers_outcome(value: Result<AutomaticHeaders, DecodeError>)
        -> Result<crate::specs::Part2JpipAutomaticHeaders, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_automatic_headers_view(&value)) }
    }

    pub proof fn jpip_automatic_headers_witness(
        cache: crate::specs::Part2JpipCache, stream: u64,
        events: Seq<crate::specs::Part2JpipAutomaticHeaderEvent>,
        result: Result<crate::specs::Part2JpipAutomaticHeaders, DecodeError>,
    )
        requires crate::specs::part2_jpip_automatic_headers(cache, stream, events) == Some(result),
        ensures crate::specs::part2_jpip_automatic_headers_result(cache, stream, result),
    {
    }

    pub proof fn jpip_automatic_headers_first_error(
        cache: crate::specs::Part2JpipCache, stream: u64, error: DecodeError,
    )
        requires match crate::specs::part2_jpip_cache_view(cache,
            (6u64, DatabinClass::MainHeader, stream, 0u64)) {
            Err(first) => first == error,
            Ok(main) => crate::specs::part2_jpip_siz_cardinality(main, &cache.0) == Err(error),
        },
        ensures forall|result: Result<crate::specs::Part2JpipAutomaticHeaders, DecodeError>|
            crate::specs::part2_jpip_automatic_headers_result(cache, stream, result)
                <==> result == Err(error),
    {
        assert forall|events: Seq<crate::specs::Part2JpipAutomaticHeaderEvent>|
            #[trigger] crate::specs::part2_jpip_automatic_headers(cache, stream, events)
                == if events.len() == 0 { Some(Err(error)) } else { None } by {
            reveal(crate::specs::part2_jpip_automatic_headers);
        }
        jpip_automatic_headers_witness(cache, stream, Seq::empty(), Err(error));
        assert forall|result: Result<crate::specs::Part2JpipAutomaticHeaders, DecodeError>|
            crate::specs::part2_jpip_automatic_headers_result(cache, stream, result)
                implies result == Err(error) by {
            let events = choose|events: Seq<crate::specs::Part2JpipAutomaticHeaderEvent>|
                crate::specs::part2_jpip_automatic_headers(cache, stream, events) == Some(result);
        }
    }

    pub proof fn jpip_filter_projection<A, B>(
        values: Seq<A>, keep: Seq<bool>, project: spec_fn(A) -> B, predicate: spec_fn(B) -> bool,
    )
        requires keep.len() == values.len(),
            forall|index: int| 0 <= index < values.len() ==>
                keep[index] == predicate(project(#[trigger] values[index])),
        ensures values.filter_index(|index: int| keep[index]).map_values(project)
            == values.map_values(project).filter(predicate),
        decreases values.len(),
    {
        reveal(Seq::filter_index);
        reveal(Seq::filter);
        if values.len() != 0 {
            jpip_filter_projection(values.drop_last(), keep.drop_last(), project, predicate);
            values.drop_last().filter_index_ext(
                |index: int| keep[index], |index: int| keep.drop_last()[index]);
            assert(values.drop_last().map_values(project) =~= values.map_values(project).drop_last());
            if keep.last() {
                assert(values.filter_index(|index: int| keep[index]).map_values(project) =~=
                    values.drop_last().filter_index(|index: int| keep[index]).map_values(project)
                        .push(project(values.last())));
            }
        } else {
            assert(values.map_values(project) =~= Seq::<B>::empty());
            assert(values.filter_index(|index: int| keep[index]).map_values(project) =~= Seq::<B>::empty());
        }
    }

    pub open spec fn jpip_parsed_packet_value(value: Option<Vec<u8>>) -> Option<Seq<u8>> {
        match value { None => None, Some(bytes) => Some(bytes@) }
    }

    pub open spec fn jpip_parsed_packet_row(value: Vec<Option<Vec<u8>>>) -> Seq<Option<Seq<u8>>> {
        value@.map_values(|cell: Option<Vec<u8>>| jpip_parsed_packet_value(cell))
    }

    pub open spec fn jpip_parsed_packet_matrix(value: Seq<Vec<Option<Vec<u8>>>>)
        -> Seq<Seq<Option<Seq<u8>>>> {
        value.map_values(|row: Vec<Option<Vec<u8>>>| jpip_parsed_packet_row(row))
    }

    pub proof fn jpip_parsed_packet_matrix_update(
        value: Seq<Vec<Option<Vec<u8>>>>, index: int, row: Vec<Option<Vec<u8>>>,
    )
        requires 0 <= index < value.len(),
        ensures jpip_parsed_packet_matrix(value.update(index, row))
            == jpip_parsed_packet_matrix(value).update(index, jpip_parsed_packet_row(row)),
    {
        assert(jpip_parsed_packet_matrix(value.update(index, row))
            =~= jpip_parsed_packet_matrix(value).update(index, jpip_parsed_packet_row(row)));
    }

    pub proof fn jpip_parsed_packet_row_update(
        before: Vec<Option<Vec<u8>>>, after: Vec<Option<Vec<u8>>>, index: int, value: Option<Vec<u8>>,
    )
        requires 0 <= index < before@.len(), after@ == before@.update(index, value),
        ensures jpip_parsed_packet_row(after)
            == jpip_parsed_packet_row(before).update(index, jpip_parsed_packet_value(value)),
    {
        assert(jpip_parsed_packet_row(after)
            =~= jpip_parsed_packet_row(before).update(index, jpip_parsed_packet_value(value)));
    }

    pub closed spec fn jpip_progressive_decoder_view(value: &JpipProgressiveDecoder)
        -> crate::specs::Part2JpipProgressiveDecoder {
        (jpip_plan_view(&value.plan), value.decoded_layers)
    }

    pub closed spec fn jpip_progressive_plan_owner(value: &JpipProgressiveDecoder) -> &JpipPrecinctCodestreamPlan {
        &value.plan
    }

    pub closed spec fn jpip_progressive_update_view(value: &JpipProgressiveUpdate)
        -> crate::specs::Part2JpipProgressiveUpdate {
        (value.status, value.previous_layers, value.available_layers, jpip_missing_views(&value.missing),
            match &value.image { None => None, Some(image) => Some(crate::image::typed_image_value_view(*image)) })
    }

    pub closed spec fn jpip_progressive_image_borrow(value: &JpipProgressiveUpdate) -> Option<&crate::image::TypedImage> {
        match &value.image { None => None, Some(image) => Some(image) }
    }

    pub closed spec fn jpip_progressive_image_owner(value: &JpipProgressiveUpdate) -> &Option<crate::image::TypedImage> {
        &value.image
    }

    pub open spec fn jpip_optional_image_view(value: Option<crate::image::TypedImage>)
        -> Option<crate::specs::Part1DecodedTypedImage> {
        match value { None => None, Some(image) => Some(crate::image::typed_image_value_view(image)) }
    }

    pub open spec fn jpip_optional_image_borrow_view(value: Option<&crate::image::TypedImage>)
        -> Option<crate::specs::Part1DecodedTypedImage> {
        match value { None => None, Some(image) => Some(crate::image::typed_image_value_view(*image)) }
    }

    pub open spec fn jpip_progressive_outcome(value: Result<JpipProgressiveUpdate, DecodeError>)
        -> Result<crate::specs::Part2JpipProgressiveUpdate, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_progressive_update_view(&value)) }
    }

    pub open spec fn jpip_progressive_availability_outcome(value: Result<(u16, Vec<JpipMissingRange>), DecodeError>)
        -> Result<(u16, Seq<crate::specs::Part2JpipMissing>), DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok((value.0, jpip_missing_views(&value.1))) }
    }
}
