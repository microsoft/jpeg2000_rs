#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn jpip_snapshot_selection_view(value: Option<&crate::DecodeSelection>)
        -> Option<crate::specs::Part2DecodeSelection> {
        match value { None => None, Some(value) => Some(crate::options::decode_selection_view(value)) }
    }

        pub(crate) proof fn jpip_snapshot_template_parse_error(
            input: crate::specs::Part2JpipSnapshotInput<'_>,
            prefix: Seq<crate::specs::Part2JpipSnapshotEvent>, main: Seq<u8>, raw: Seq<Seq<u8>>,
            count: u64, components: u16, headers: Seq<Seq<Seq<u8>>>, template: Seq<u8>, error: DecodeError,
        )
            requires
                forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                    crate::specs::part2_jpip_snapshot_run(input, prefix + tail)
                        == crate::specs::part2_jpip_snapshot_after_normalized(
                            input, main, raw, count, components, headers, tail),
                crate::specs::part2_jpip_transition_template(main, headers, input.limits) == Ok(template),
                crate::codestream::complete_layout_outcome(Err(error))
                    == crate::specs::part1_parse_layout(template, input.limits),
            ensures crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
                input.stream, input.selected, input.components, input.limits, Err(error)),
        {
            crate::codestream::decoder_layout_errors_known();
            assert(crate::specs::part1_parse_layout(template, input.limits) == Err(error));
            assert(prefix + Seq::empty() =~= prefix);
            assert(crate::specs::part2_jpip_snapshot_run(input, prefix + Seq::empty())
                == crate::specs::part2_jpip_snapshot_after_normalized(
                    input, main, raw, count, components, headers, Seq::empty()));
            jpip_snapshot_result_witness(input, prefix, Err(error));
        }

    pub closed spec fn jpip_packet_selection_view(value: &JpipPacketSelection) -> Seq<u16> {
        value.components@
    }

    pub(crate) open spec fn jpip_snapshot_inputs_match(
        input: crate::specs::Part2JpipSnapshotInput<'_>, cache: &DatabinCache, stream: u64,
        selection: Option<&crate::DecodeSelection>, packets: &JpipPacketSelection, limits: &ResourceLimits,
    ) -> bool {
        input.cache == jpip_cache_view(cache) && input.stream == stream
            && input.selected == jpip_snapshot_selection_view(selection)
            && input.components == jpip_packet_selection_view(packets) && input.limits == limits
    }

    pub(crate) proof fn jpip_snapshot_result_witness(
        input: crate::specs::Part2JpipSnapshotInput<'_>,
        events: Seq<crate::specs::Part2JpipSnapshotEvent>,
        result: Result<crate::specs::Part2JpipAutomaticSnapshotResult, DecodeError>,
    )
        requires crate::specs::part2_jpip_snapshot_run(input, events) == Some((result, Seq::empty())),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(input.cache, input.stream,
            input.selected, input.components, input.limits, result),
    {
        reveal(crate::specs::part2_jpip_automatic_snapshot_result);
    }

    pub(crate) proof fn jpip_snapshot_main_waiting(input: crate::specs::Part2JpipSnapshotInput<'_>)
        requires !crate::specs::part2_jpip_cache_complete(input.cache,
            (6u64, DatabinClass::MainHeader, input.stream, 0u64)),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
            input.stream, input.selected, input.components, input.limits,
            Ok((None, crate::specs::part2_jpip_complete_missing(input.cache,
                (6u64, DatabinClass::MainHeader, input.stream, 0u64))))),
    {
        jpip_snapshot_result_witness(input, Seq::empty(),
            Ok((None, crate::specs::part2_jpip_complete_missing(input.cache,
                (6u64, DatabinClass::MainHeader, input.stream, 0u64)))));
    }

    pub(crate) proof fn jpip_snapshot_admission_error(
        input: crate::specs::Part2JpipSnapshotInput<'_>, error: DecodeError,
    )
        requires crate::specs::part2_jpip_cache_complete(input.cache,
            (6u64, DatabinClass::MainHeader, input.stream, 0u64)),
            crate::specs::part2_jpip_snapshot_admit(input) == Err(error),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
            input.stream, input.selected, input.components, input.limits, Err(error)),
    {
        jpip_snapshot_result_witness(input, Seq::empty(), Err(error));
    }

    pub(crate) proof fn jpip_snapshot_header_capacity_error(
        input: crate::specs::Part2JpipSnapshotInput<'_>, main: Seq<u8>, count: u64, components: u16,
    )
        requires crate::specs::part2_jpip_cache_complete(input.cache,
            (6u64, DatabinClass::MainHeader, input.stream, 0u64)),
            crate::specs::part2_jpip_snapshot_admit(input) == Ok((main, count, components)),
            count <= usize::MAX as u64,
        ensures crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
            input.stream, input.selected, input.components, input.limits, Err(DecodeError::AllocationFailed)),
    {
        let events = seq![crate::specs::Part2JpipSnapshotEvent::Capacity {
            site: 0, tile: 0, elements: count as usize, succeeded: false }];
        assert(events.drop_first() =~= Seq::<crate::specs::Part2JpipSnapshotEvent>::empty());
        jpip_snapshot_result_witness(input, events, Err(DecodeError::AllocationFailed));
    }

    pub(crate) proof fn jpip_snapshot_gather_continuation(
        input: crate::specs::Part2JpipSnapshotInput<'_>, main: Seq<u8>, count: u64, components: u16,
    )
        requires crate::specs::part2_jpip_cache_complete(input.cache,
            (6u64, DatabinClass::MainHeader, input.stream, 0u64)),
            crate::specs::part2_jpip_snapshot_admit(input) == Ok((main, count, components)),
            count <= usize::MAX as u64,
        ensures forall|error: DecodeError|
            crate::specs::part2_jpip_snapshot_gather(input, count, 0, Seq::empty(), Seq::empty()) == Err(error)
                ==> crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
                    input.stream, input.selected, input.components, input.limits, Err(error)),
    {
        assert forall|error: DecodeError|
            crate::specs::part2_jpip_snapshot_gather(input, count, 0, Seq::empty(), Seq::empty()) == Err(error)
                implies crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
                    input.stream, input.selected, input.components, input.limits, Err(error)) by {
            let events = seq![crate::specs::Part2JpipSnapshotEvent::Capacity {
                site: 0, tile: 0, elements: count as usize, succeeded: true }];
            assert(events.drop_first() =~= Seq::<crate::specs::Part2JpipSnapshotEvent>::empty());
            jpip_snapshot_result_witness(input, events, Err(error));
        }
    }

    pub(crate) proof fn jpip_snapshot_headers_waiting(
        input: crate::specs::Part2JpipSnapshotInput<'_>, main: Seq<u8>, count: u64, components: u16,
        raw: Seq<Seq<u8>>, missing: Seq<crate::specs::Part2JpipMissing>,
    )
        requires crate::specs::part2_jpip_cache_complete(input.cache,
            (6u64, DatabinClass::MainHeader, input.stream, 0u64)),
            crate::specs::part2_jpip_snapshot_admit(input) == Ok((main, count, components)),
            count <= usize::MAX as u64, missing.len() != 0,
            crate::specs::part2_jpip_snapshot_gather(input, count, 0, Seq::empty(), Seq::empty())
                == Ok((raw, missing)),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
            input.stream, input.selected, input.components, input.limits, Ok((None, missing))),
    {
        let events = seq![crate::specs::Part2JpipSnapshotEvent::Capacity {
            site: 0, tile: 0, elements: count as usize, succeeded: true }];
        assert(events.drop_first() =~= Seq::<crate::specs::Part2JpipSnapshotEvent>::empty());
        jpip_snapshot_result_witness(input, events, Ok((None, missing)));
    }

    pub(crate) proof fn jpip_snapshot_headers_continuation(
        input: crate::specs::Part2JpipSnapshotInput<'_>, main: Seq<u8>, count: u64, components: u16,
        raw: Seq<Seq<u8>>,
    )
        requires crate::specs::part2_jpip_cache_complete(input.cache,
            (6u64, DatabinClass::MainHeader, input.stream, 0u64)),
            crate::specs::part2_jpip_snapshot_admit(input) == Ok((main, count, components)),
            count <= usize::MAX as u64,
            crate::specs::part2_jpip_snapshot_gather(input, count, 0, Seq::empty(), Seq::empty())
                == Ok((raw, Seq::empty())),
        ensures forall|events: Seq<crate::specs::Part2JpipSnapshotEvent>|
            crate::specs::part2_jpip_snapshot_run(input,
                seq![crate::specs::Part2JpipSnapshotEvent::Capacity {
                    site: 0, tile: 0, elements: count as usize, succeeded: true }] + events)
                == crate::specs::part2_jpip_snapshot_after_gather(input, main, raw, count, components, events),
    {
        let capacity = crate::specs::Part2JpipSnapshotEvent::Capacity {
            site: 0, tile: 0, elements: count as usize, succeeded: true };
        assert forall|events: Seq<crate::specs::Part2JpipSnapshotEvent>|
            crate::specs::part2_jpip_snapshot_run(input, seq![capacity] + events)
                == crate::specs::part2_jpip_snapshot_after_gather(input, main, raw, count, components, events) by {
            assert((seq![capacity] + events).drop_first() =~= events);
        }
    }

    pub(crate) proof fn jpip_snapshot_main_normalization_error(
        input: crate::specs::Part2JpipSnapshotInput<'_>, main: Seq<u8>, count: u64, components: u16,
        raw: Seq<Seq<u8>>, error: DecodeError,
    )
        requires crate::specs::part2_jpip_cache_complete(input.cache,
            (6u64, DatabinClass::MainHeader, input.stream, 0u64)),
            crate::specs::part2_jpip_snapshot_admit(input) == Ok((main, count, components)),
            count <= usize::MAX as u64,
            crate::specs::part2_jpip_snapshot_gather(input, count, 0, Seq::empty(), Seq::empty())
                == Ok((raw, Seq::empty())),
            crate::specs::part2_jpip_main_header_result(main, Err(error)),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
            input.stream, input.selected, input.components, input.limits, Err(error)),
    {
        jpip_snapshot_headers_continuation(input, main, count, components, raw);
        let calls = choose|calls: Seq<crate::specs::Part2JpipStorageEvent>|
            crate::specs::part2_jpip_normalize_main_header(main, calls) == Some(Err(error));
        let capacity = crate::specs::Part2JpipSnapshotEvent::Capacity {
            site: 0, tile: 0, elements: count as usize, succeeded: true };
        let event = crate::specs::Part2JpipSnapshotEvent::Main { calls };
        assert(seq![event].drop_first() =~= Seq::<crate::specs::Part2JpipSnapshotEvent>::empty());
        assert((seq![capacity] + seq![event]).drop_first() =~= seq![event]);
        assert(crate::specs::part2_jpip_snapshot_after_gather(input, main, raw, count, components, seq![event])
            == Some((Err(error), Seq::empty())));
        jpip_snapshot_result_witness(input, seq![capacity] + seq![event], Err(error));
    }

    pub(crate) proof fn jpip_snapshot_normalization_continuation(
        input: crate::specs::Part2JpipSnapshotInput<'_>, main: Seq<u8>, count: u64, components: u16,
        raw: Seq<Seq<u8>>, normalized: Seq<u8>, calls: Seq<crate::specs::Part2JpipStorageEvent>,
    )
        requires crate::specs::part2_jpip_cache_complete(input.cache,
            (6u64, DatabinClass::MainHeader, input.stream, 0u64)),
            crate::specs::part2_jpip_snapshot_admit(input) == Ok((main, count, components)),
            count <= usize::MAX as u64,
            crate::specs::part2_jpip_snapshot_gather(input, count, 0, Seq::empty(), Seq::empty())
                == Ok((raw, Seq::empty())),
            crate::specs::part2_jpip_normalize_main_header(main, calls) == Some(Ok(normalized)),
        ensures crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
                input.stream, input.selected, input.components, input.limits, Err(DecodeError::AllocationFailed)),
            forall|error: DecodeError|
                crate::specs::part2_jpip_snapshot_normalize_tiles(raw, 0, Seq::empty()) == Err(error)
                    ==> crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
                        input.stream, input.selected, input.components, input.limits, Err(error)),
    {
        jpip_snapshot_headers_continuation(input, main, count, components, raw);
        let capacity = crate::specs::Part2JpipSnapshotEvent::Capacity {
            site: 0, tile: 0, elements: count as usize, succeeded: true };
        let event = crate::specs::Part2JpipSnapshotEvent::Main { calls };
        let refused = crate::specs::Part2JpipSnapshotEvent::Capacity {
            site: 1, tile: 0, elements: raw.len() as usize, succeeded: false };
        assert(seq![event, refused].drop_first() =~= seq![refused]);
        assert(seq![refused].drop_first() =~= Seq::<crate::specs::Part2JpipSnapshotEvent>::empty());
        assert((seq![capacity] + seq![event, refused]).drop_first() =~= seq![event, refused]);
        jpip_snapshot_result_witness(input, seq![capacity] + seq![event, refused], Err(DecodeError::AllocationFailed));
        assert forall|error: DecodeError|
            crate::specs::part2_jpip_snapshot_normalize_tiles(raw, 0, Seq::empty()) == Err(error)
                implies crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
                    input.stream, input.selected, input.components, input.limits, Err(error)) by {
            let accepted = crate::specs::Part2JpipSnapshotEvent::Capacity {
                site: 1, tile: 0, elements: raw.len() as usize, succeeded: true };
            assert(seq![event, accepted].drop_first() =~= seq![accepted]);
            assert(seq![accepted].drop_first() =~= Seq::<crate::specs::Part2JpipSnapshotEvent>::empty());
            assert((seq![capacity] + seq![event, accepted]).drop_first() =~= seq![event, accepted]);
            jpip_snapshot_result_witness(input, seq![capacity] + seq![event, accepted], Err(error));
        }
    }

        pub(crate) proof fn jpip_snapshot_normalized_continuation(
            input: crate::specs::Part2JpipSnapshotInput<'_>, main: Seq<u8>, count: u64, components: u16,
            raw: Seq<Seq<u8>>, normalized: Seq<u8>, calls: Seq<crate::specs::Part2JpipStorageEvent>,
        )
            requires crate::specs::part2_jpip_cache_complete(input.cache,
                (6u64, DatabinClass::MainHeader, input.stream, 0u64)),
                crate::specs::part2_jpip_snapshot_admit(input) == Ok((main, count, components)),
                count <= usize::MAX as u64,
                crate::specs::part2_jpip_snapshot_gather(input, count, 0, Seq::empty(), Seq::empty())
                    == Ok((raw, Seq::empty())),
                crate::specs::part2_jpip_normalize_main_header(main, calls) == Some(Ok(normalized)),
            ensures forall|headers: Seq<Seq<Seq<u8>>>, tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                crate::specs::part2_jpip_snapshot_normalize_tiles(raw, 0, Seq::empty()) == Ok(headers) ==>
                    crate::specs::part2_jpip_snapshot_run(input,
                        crate::specs::part2_jpip_snapshot_normalized_events(count, raw.len() as usize, calls) + tail)
                    == crate::specs::part2_jpip_snapshot_after_normalized(
                        input, normalized, raw, count, components, headers, tail),
        {
            jpip_snapshot_headers_continuation(input, main, count, components, raw);
            let prefix = crate::specs::part2_jpip_snapshot_normalized_events(count, raw.len() as usize, calls);
            assert forall|headers: Seq<Seq<Seq<u8>>>, tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                crate::specs::part2_jpip_snapshot_normalize_tiles(raw, 0, Seq::empty()) == Ok(headers) implies
                    crate::specs::part2_jpip_snapshot_run(input, prefix + tail)
                        == crate::specs::part2_jpip_snapshot_after_normalized(
                            input, normalized, raw, count, components, headers, tail) by {
                assert((prefix + tail).drop_first() =~= seq![prefix[1], prefix[2]] + tail);
                assert((seq![prefix[1], prefix[2]] + tail).drop_first() =~= seq![prefix[2]] + tail);
                assert((seq![prefix[2]] + tail).drop_first() =~= tail);
            }
        }

}
