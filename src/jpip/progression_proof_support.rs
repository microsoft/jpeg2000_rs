#[cfg(verus_keep_ghost)]
verus! {
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
