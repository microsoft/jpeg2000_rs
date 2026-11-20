#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn packet_bit_reader_view(reader: &PacketBitReader<'_>) -> crate::specs::Part1PacketReaderState {
        crate::specs::Part1PacketReaderState {
            input: reader.input@, byte_index: reader.byte_index, current_byte: reader.current_byte,
            bits_remaining: reader.bits_remaining, previous_byte_was_ff: reader.previous_byte_was_ff,
            bits_read: reader.bits_read, maximum_work_units: reader.maximum_work_units,
            maximum_header_bytes: reader.maximum_header_bytes,
        }
    }

    pub open spec fn packet_reader_outcome(result: Result<PacketBitReader<'_>, DecodeError>)
        -> Result<crate::specs::Part1PacketReaderState, DecodeError>
    {
        match result { Ok(reader) => Ok(packet_bit_reader_view(&reader)), Err(error) => Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn packet_grid_view(grid: &PacketGrid) -> crate::specs::Part1PacketGrid {
        crate::specs::Part1PacketGrid {
            layers:grid.layers, components:grid.components, resolutions:grid.resolutions,
            component_resolutions:grid.component_resolutions@,
            maximum_precincts_per_resolution:grid.maximum_precincts_per_resolution,
            precinct_counts:grid.precinct_counts@, precinct_offsets:grid.precinct_offsets@,
            candidate_count:grid.candidate_count, packet_count:grid.packet_count,
            maximum_work_units:grid.maximum_work_units,
            spatial:match &grid.spatial { Some(spatial)=>Some(packet_spatial_grid_view(spatial)),None=>None },
        }
    }
    pub open spec fn packet_grid_outcome(value:Result<PacketGrid,DecodeError>) -> Result<crate::specs::Part1PacketGrid,DecodeError> {
        match value {Ok(grid)=>Ok(packet_grid_view(&grid)),Err(error)=>Err(error)}
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn packet_spatial_grid_view(grid: &PacketSpatialGrid) -> crate::specs::Part1PacketSpatialGrid {
        crate::specs::Part1PacketSpatialGrid {
            rows:packet_spatial_rows_view(grid.rows@),
            x0:grid.x0,y0:grid.y0,step_x:grid.step_x,step_y:grid.step_y,
            across:grid.across,positions:grid.positions,
        }
    }
    pub closed spec fn packet_spatial_resolution_view(row: PacketSpatialResolution) -> crate::specs::Part1PacketSpatialResolution {
        crate::specs::Part1PacketSpatialResolution {
            first_x:row.first_x,first_y:row.first_y,origin_x:row.origin_x,origin_y:row.origin_y,
            step_x:row.step_x,step_y:row.step_y,across:row.across,down:row.down,
        }
    }
    pub open spec fn packet_spatial_rows_view(rows:Seq<PacketSpatialResolution>) -> Seq<crate::specs::Part1PacketSpatialResolution> {
        rows.map(|i:int,row:PacketSpatialResolution|packet_spatial_resolution_view(row))
    }
    pub(crate) proof fn packet_spatial_resolution_known_fields(row:PacketSpatialResolution)
        ensures packet_spatial_resolution_view(row)==(crate::specs::Part1PacketSpatialResolution {
            first_x:row.first_x,first_y:row.first_y,origin_x:row.origin_x,origin_y:row.origin_y,
            step_x:row.step_x,step_y:row.step_y,across:row.across,down:row.down,
        }),
    {}
    pub(crate) proof fn packet_spatial_grid_known_fields(grid:&PacketSpatialGrid)
        ensures packet_spatial_grid_view(grid)==(crate::specs::Part1PacketSpatialGrid {
            rows:packet_spatial_rows_view(grid.rows@),
            x0:grid.x0,y0:grid.y0,step_x:grid.step_x,step_y:grid.step_y,across:grid.across,positions:grid.positions,
        }),
    {}
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn packet_grid_count_view(value: &PacketGridCountState) -> crate::specs::Part1GridCountState {
        crate::specs::Part1GridCountState {
            index:value.index,component:value.component,resolution:value.resolution,total:value.total,
            maximum:value.maximum,offsets:value.offsets@,
        }
    }
    pub open spec fn packet_grid_count_outcome(value:Result<PacketGridCountState,DecodeError>)
        -> Result<crate::specs::Part1GridCountState,DecodeError> {
        match value { Ok(state) => Ok(packet_grid_count_view(&state)),Err(error)=>Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn packet_selection_view(value:Option<&[u8]>) -> Option<Seq<u8>> {
        match value {Some(counts)=>Some(counts@),None=>None}
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn packet_iterator_view(value: &PacketIterator<'_>) -> crate::specs::Part1PacketIterator {
        crate::specs::Part1PacketIterator {
            grid:packet_grid_view(value.grid), order:value.order,
            candidate_index:value.candidate_index, emitted:value.emitted,
        }
    }

    pub open spec fn packet_unravel_outcome(value: Result<[u64;4], DecodeError>)
        -> Result<Seq<u64>, DecodeError> {
        match value { Ok(values) => Ok(values@), Err(error) => Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn progression_packet_iterator_view(value: &ProgressionPacketIterator<'_>)
        -> crate::specs::Part1ProgressionPacketIterator {
        crate::specs::Part1ProgressionPacketIterator {
            grid:packet_grid_view(value.grid), changes:crate::codestream::progression_changes_view(value.changes),
            default:match value.default { Some(default) => Some(packet_iterator_view(&default)), None => None },
            window_index:value.window_index, window_candidate:value.window_candidate,
            window_candidates:value.window_candidates, emitted:value.emitted,
        }
    }

    pub open spec fn progression_packet_iterator_outcome(value: Result<ProgressionPacketIterator<'_>,DecodeError>)
        -> Result<crate::specs::Part1ProgressionPacketIterator,DecodeError> {
        match value { Ok(iterator) => Ok(progression_packet_iterator_view(&iterator)), Err(error) => Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn code_block_packet_state_view(state: &CodeBlockPacketState) -> crate::specs::Part1CodeBlockPacketState {
        crate::specs::Part1CodeBlockPacketState {
            included: state.included, zero_bitplanes: state.zero_bitplanes, lblock: state.lblock,
            total_passes: state.total_passes, high_throughput: state.high_throughput,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn code_block_contribution_view(contribution: &CodeBlockContribution) -> crate::specs::Part1CodeBlockContribution {
        crate::specs::Part1CodeBlockContribution {
            first_inclusion: contribution.first_inclusion,
            zero_bitplanes: contribution.zero_bitplanes,
            new_passes: contribution.new_passes,
            data_length: contribution.data_length,
            high_throughput: contribution.high_throughput,
            segment_count: contribution.segment_count,
            segment_passes: contribution.segment_passes@,
            segment_lengths: contribution.segment_lengths@,
        }
    }

    pub open spec fn code_block_contribution_option_view(contribution: Option<CodeBlockContribution>)
        -> Option<crate::specs::Part1CodeBlockContribution>
    {
        match contribution { None => None, Some(value) => Some(code_block_contribution_view(&value)) }
    }

    pub open spec fn code_block_header_outcome(result: Result<Option<CodeBlockContribution>, DecodeError>)
        -> Result<Option<crate::specs::Part1CodeBlockContribution>, DecodeError>
    {
        match result {
            Err(error) => Err(error),
            Ok(contribution) => Ok(code_block_contribution_option_view(contribution)),
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn ht_body_progress_view(progress: &HtBodyProgress) -> crate::specs::HtPacketBodyProgress {
        crate::specs::HtPacketBodyProgress {
            segment_index: progress.segment_index,
            offset: progress.offset,
            decoded_passes: progress.decoded_passes,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn packet_precinct_decoders(value: &PacketPrecinctDecoder) -> Seq<Tier1CodeBlockDecoder> {
        value.decoders@
    }

    pub proof fn packet_precinct_decoder_states(value: &PacketPrecinctDecoder)
        ensures packet_precinct_view(value).decoders
            == packet_precinct_decoders(value).map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder)),
    {
        reveal(packet_precinct_view);
        reveal(packet_precinct_decoders);
    }

    pub open spec fn packet_decoder_outcome(result: Result<&Tier1CodeBlockDecoder, DecodeError>)
        -> Result<Tier1CodeBlockDecoder, DecodeError>
    {
        match result { Ok(value) => Ok(*value), Err(error) => Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn precinct_payload_header_view(value: PrecinctPayloadHeader<'_>)
        -> (crate::specs::Part1PrecinctPayloadReader, Seq<Option<crate::specs::Part1CodeBlockContribution>>, u32) {
        (precinct_payload_reader_view(value.prefix),
            value.contributions@.map_values(|value: Option<CodeBlockContribution>| code_block_contribution_option_view(value)),
            value.contribution_count)
    }

    pub closed spec fn precinct_payload_reader_view(value: PrecinctPayloadReader<'_>) -> crate::specs::Part1PrecinctPayloadReader {
        crate::specs::Part1PrecinctPayloadReader {
            reader: packet_bit_reader_view(&value.reader), packet_data: value.packet_data@,
            present: value.present, sop_bytes: value.sop_bytes,
        }
    }

    pub open spec fn precinct_payload_reader_outcome(value: Result<PrecinctPayloadReader<'_>, DecodeError>)
        -> Result<crate::specs::Part1PrecinctPayloadReader, DecodeError> {
        match value { Ok(reader) => Ok(precinct_payload_reader_view(reader)), Err(error) => Err(error) }
    }

    pub closed spec fn packet_subband_view(value: &PacketSubbandState) -> crate::specs::Part1PacketSubbandState {
        crate::specs::Part1PacketSubbandState {
            orientation: value.orientation, first_decoder: value.first_decoder, decoder_count: value.decoder_count,
            code_blocks_across: value.code_blocks_across, code_blocks_down: value.code_blocks_down,
            inclusion_tree: tag_tree_view(&value.inclusion_tree), zero_bitplane_tree: tag_tree_view(&value.zero_bitplane_tree),
        }
    }

    pub closed spec fn packet_precinct_view(value: &PacketPrecinctDecoder) -> crate::specs::Part1PacketPrecinctState {
        crate::specs::Part1PacketPrecinctState {
            component: value.component, resolution: value.resolution, precinct: value.precinct,
            states: value.states@.map_values(|state: CodeBlockPacketState| code_block_packet_state_view(&state)),
            contexts: value.contexts@,
            decoders: value.decoders@.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder)),
            subbands: value.subbands@.map_values(|subband: PacketSubbandState| packet_subband_view(&subband)),
        }
    }

    pub closed spec fn packet_execution_view(value: &PacketSubbandExecution) -> crate::specs::Part2PacketSubbandExecution {
        crate::specs::Part2PacketSubbandExecution {
            orientation: value.orientation, across: value.code_blocks_across, down: value.code_blocks_down,
            maximum_zero: value.maximum_zero_bitplanes,
            decoders: value.decoders@.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder)),
        }
    }

    pub proof fn packet_execution_known_fields(value: &PacketSubbandExecution)
        ensures packet_execution_view(value) == (crate::specs::Part2PacketSubbandExecution {
            orientation: value.orientation, across: value.code_blocks_across, down: value.code_blocks_down,
            maximum_zero: value.maximum_zero_bitplanes,
            decoders: value.decoders@.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder)),
        }),
    {
        reveal(packet_execution_view);
    }

    pub open spec fn packet_executions_view(values: Seq<PacketSubbandExecution>) -> Seq<crate::specs::Part2PacketSubbandExecution> {
        Seq::new(values.len(), |index: int| packet_execution_view(&values[index]))
    }

    pub open spec fn packet_executions_outcome(result: Result<Vec<PacketSubbandExecution>, DecodeError>)
        -> Result<Seq<crate::specs::Part2PacketSubbandExecution>, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(values) => Ok(packet_executions_view(values@)) }
    }

    pub open spec fn packet_decoder_states(values: Seq<Tier1CodeBlockDecoder>) -> Seq<crate::specs::Tier1DecoderState> {
        values.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder))
    }

    pub closed spec fn precinct_initialization_view(
        coordinate: (u16, u8, u32), states: Seq<CodeBlockPacketState>, contexts: Seq<CodeBlockPacketContext>,
        decoders: Seq<Tier1CodeBlockDecoder>, subbands: Seq<PacketSubbandState>,
    ) -> crate::specs::Part1PacketPrecinctState {
        crate::specs::Part1PacketPrecinctState {
            component: coordinate.0, resolution: coordinate.1, precinct: coordinate.2,
            states: states.map_values(|state: CodeBlockPacketState| code_block_packet_state_view(&state)),
            contexts, decoders: decoders.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder)),
            subbands: subbands.map_values(|subband: PacketSubbandState| packet_subband_view(&subband)),
        }
    }

    pub open spec fn packet_precinct_outcome(result: Result<PacketPrecinctDecoder, DecodeError>)
        -> Result<crate::specs::Part1PacketPrecinctState, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(packet_precinct_view(&value)) }
    }

    pub open spec fn precinct_contexts_outcome(
        result: Result<(Vec<CodeBlockPacketState>, Vec<CodeBlockPacketContext>), DecodeError>,
    ) -> Result<(Seq<crate::specs::Part1CodeBlockPacketState>, Seq<CodeBlockPacketContext>), DecodeError> {
        match result {
            Err(error) => Err(error),
            Ok(value) => Ok((value.0@.map_values(|state: CodeBlockPacketState| code_block_packet_state_view(&state)), value.1@)),
        }
    }

    pub open spec fn packet_states_view(values: Seq<CodeBlockPacketState>) -> Seq<crate::specs::Part1CodeBlockPacketState> {
        values.map_values(|state: CodeBlockPacketState| code_block_packet_state_view(&state))
    }

    pub closed spec fn precinct_payload_parameters_view(value: PrecinctPayloadParameters)
        -> crate::specs::Part1PrecinctPayloadParameters {
        crate::specs::Part1PrecinctPayloadParameters {
            error_offset: value.error_offset, packed_offset: value.packed_offset,
            expected_packet_length: value.expected_packet_length, expected_sop_sequence: value.expected_sop_sequence,
            style: value.style, sop: value.sop, eph: value.eph, packed: value.packed, decode_tier1: value.decode_tier1,
        }
    }

    pub closed spec fn precinct_header_view(
        states: &[CodeBlockPacketState], subbands: &[PacketSubbandState],
        contributions: &[Option<CodeBlockContribution>], reader: &PacketBitReader<'_>,
        progress: &PrecinctHeaderProgress,
    ) -> crate::specs::Part1PrecinctHeaderState {
        crate::specs::Part1PrecinctHeaderState {
            states: states@.map_values(|state: CodeBlockPacketState| code_block_packet_state_view(&state)),
            subbands: subbands@.map_values(|subband: PacketSubbandState| packet_subband_view(&subband)),
            contributions: packet_body_contributions_view(contributions),
            reader: packet_bit_reader_view(reader),
            subband_index: progress.subband_index, local_index: progress.local_index,
            contribution_count: progress.contribution_count,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn progression_tile_preparation_view(input:&ProgressionTilePreparation)->crate::specs::Part1TilePacketPreparation {
        crate::specs::Part1TilePacketPreparation {
            tile_index:input.tile_index,index:input.index,payload_bytes:input.payload_bytes,
            packed_payload_bytes:input.packed_payload_bytes,declared_packets:input.declared_packets,
            all_lengths:input.all_lengths,packed:input.packed@.map_values(|bytes:Vec<u8>|bytes@),
        }
    }
    pub open spec fn progression_tile_preparation_outcome(value:Result<ProgressionTilePreparation,DecodeError>)
        ->Result<crate::specs::Part1TilePacketPreparation,DecodeError> {
        match value {Ok(input)=>Ok(progression_tile_preparation_view(&input)),Err(error)=>Err(error)}
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn packet_precinct_vector_view(values:&[PacketPrecinctDecoder])
        -> Seq<crate::specs::Part1PacketPrecinctState> {
        values@.map_values(|value:PacketPrecinctDecoder|packet_precinct_view(&value))
    }

    pub proof fn packet_precinct_vector_known_fields(values: &[PacketPrecinctDecoder])
        ensures packet_precinct_vector_view(values)
            == values@.map_values(|value: PacketPrecinctDecoder| packet_precinct_view(&value)),
    {
        reveal(packet_precinct_vector_view);
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn progression_tile_parameters_view<'a,'data>(value:&ProgressionTileParameters<'a,'data>)
        ->crate::specs::Part1TilePacketParameters {
        crate::specs::Part1TilePacketParameters {
            parts:crate::codestream::tile_parts_owned_view(value.tile_parts@),grid:packet_grid_view(value.grid),input:progression_tile_preparation_view(value.input),
            selection:packet_selection_view(value.selection),
            caps:crate::specs::Part1TilePacketCaps {
                work:crate::limits::resource_work_limit(value.limits),
                header:crate::limits::resource_packet_header_byte_limit(value.limits),
                blocks:crate::limits::resource_code_block_limit(value.limits),
                passes:crate::limits::resource_code_block_pass_limit(value.limits),
                bytes:crate::limits::resource_code_block_byte_limit(value.limits),
                input:crate::limits::resource_input_byte_limit(value.limits),
            },
        }
    }
    pub closed spec fn progression_tile_progress_view(value:&ProgressionTileProgress<'_>)->crate::specs::Part1TilePacketProgress {
        crate::specs::Part1TilePacketProgress {
            iterator:progression_packet_iterator_view(&value.iterator),
            length_iterator:crate::codestream::packet_length_iter_view(&value.length_iterator),
            current_tile_part:value.current_tile_part,length_tile_part:value.length_tile_part,
            offset:value.offset,packed_offset:value.packed_offset,packets:value.packets,present_packets:value.present_packets,
            contributions:value.contributions,segments:value.segments,passes:value.passes,
            packet_header_bytes:value.packet_header_bytes,packet_body_bytes:value.packet_body_bytes,
            seen:value.seen@,remaining_packets:value.remaining_packets,
        }
    }
    pub open spec fn progression_tile_progress_outcome(value:Result<ProgressionTileProgress<'_>,DecodeError>)
        ->Result<crate::specs::Part1TilePacketProgress,DecodeError> {
        match value {Ok(progress)=>Ok(progression_tile_progress_view(&progress)),Err(error)=>Err(error)}
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn progression_tile_execution_view(precincts:&[PacketPrecinctDecoder],p:&ProgressionTileProgress<'_>)
        ->crate::specs::Part1TilePacketExecution {
        crate::specs::Part1TilePacketExecution {progress:progression_tile_progress_view(p),precincts:packet_precinct_vector_view(precincts)}
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn packet_body_contributions_view(values: &[Option<CodeBlockContribution>])
        -> Seq<Option<crate::specs::Part1CodeBlockContribution>>
    {
        values@.map_values(|value: Option<CodeBlockContribution>| code_block_contribution_option_view(value))
    }

    pub closed spec fn packet_body_preflight_view(value: &PacketBodyPreflight)
        -> crate::specs::Part1PacketBodyPreflight
    {
        crate::specs::Part1PacketBodyPreflight { index: value.index, end: value.end }
    }

    pub closed spec fn packet_body_execution_view(
        decoders: &[Tier1CodeBlockDecoder], progress: &PacketBodyExecutionProgress,
    ) -> crate::specs::Part1PacketBodyExecution {
        crate::specs::Part1PacketBodyExecution {
            decoders: decoders@.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder)),
            index: progress.index, offset: progress.offset, segments: progress.segments, passes: progress.passes,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn multi_packet_state_view(
        states:&[CodeBlockPacketState],inclusion:&TagTree,zero:&TagTree,contexts:&[CodeBlockPacketContext],
        decoders:&[Tier1CodeBlockDecoder],
    )->crate::specs::Part1MultiPacketState {
        crate::specs::Part1MultiPacketState {
            states:states@.map_values(|state:CodeBlockPacketState|code_block_packet_state_view(&state)),
            inclusion:tag_tree_view(inclusion),zero:tag_tree_view(zero),contexts:contexts@,
            decoders:decoders@.map_values(|decoder:Tier1CodeBlockDecoder|crate::tier1::tier1_decoder_state(&decoder)),
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn multi_admission_outcome(value:Result<&[u8],DecodeError>)
        ->Result<Seq<u8>,DecodeError> {
        match value {Ok(value)=>Ok(value@),Err(error)=>Err(error)}
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn multi_header_view(
        states:&[CodeBlockPacketState],inclusion:&TagTree,zero:&TagTree,contexts:&[CodeBlockPacketContext],
        contributions:&[Option<CodeBlockContribution>],reader:&PacketBitReader<'_>,progress:&MultiHeaderProgress,
    )->crate::specs::Part1MultiPacketHeader {
        crate::specs::Part1MultiPacketHeader {
            states:states@.map_values(|state:CodeBlockPacketState|code_block_packet_state_view(&state)),
            inclusion:tag_tree_view(inclusion),zero:tag_tree_view(zero),contexts:contexts@,
            contributions:packet_body_contributions_view(contributions),reader:packet_bit_reader_view(reader),
            index:progress.index,count:progress.count,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn single_packet_state_view(
        state:&CodeBlockPacketState,inclusion:&TagTree,zero:&TagTree,decoder:&Tier1CodeBlockDecoder,
    )->crate::specs::Part1SinglePacketState {
        crate::specs::Part1SinglePacketState {
            state:code_block_packet_state_view(state),inclusion:tag_tree_view(inclusion),zero:tag_tree_view(zero),
            decoder:crate::tier1::tier1_decoder_state(decoder),
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn legacy_packet_progress_view(
        decoder: &Tier1CodeBlockDecoder, segment_index: u8, offset: usize, decoded_passes: u32,
    ) -> crate::specs::Part1LegacyPacketProgress {
        crate::specs::Part1LegacyPacketProgress {
            decoder: crate::tier1::tier1_decoder_state(decoder), segment_index, offset, decoded_passes,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn header_segments_view(segments: &CodeBlockHeaderSegments) -> crate::specs::Part1HeaderSegments {
        crate::specs::Part1HeaderSegments {
            segment_passes: segments.segment_passes@, segment_lengths: segments.segment_lengths@,
            segment_count: segments.segment_count, accounted_passes: segments.accounted_passes,
            data_length: segments.data_length, routing: segments.routing,
        }
    }

    #[verifier::inline]
    spec fn header_segments_outcome(result: Result<CodeBlockHeaderSegments, DecodeError>) -> Result<crate::specs::Part1HeaderSegments, DecodeError> {
        match result { Err(error) => Err(error), Ok(segments) => Ok(header_segments_view(&segments)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn tag_node_view(node: TagTreeNode) -> crate::specs::Part1TagNode {
        crate::specs::Part1TagNode { low: node.low, value: node.value }
    }

    closed spec fn tag_level_view(level: TagTreeLevel) -> crate::specs::Part1TagLevel {
        crate::specs::Part1TagLevel { offset: level.offset, width: level.width, height: level.height }
    }

    pub closed spec fn tag_tree_view(tree: &TagTree) -> crate::specs::Part1TagTree {
        crate::specs::Part1TagTree {
            levels: tree.levels@.map_values(|level: TagTreeLevel| tag_level_view(level)),
            nodes: tree.nodes@.map_values(|node: TagTreeNode| tag_node_view(node)),
        }
    }

    pub open spec fn tag_tree_outcome(result: Result<TagTree, DecodeError>) -> Result<crate::specs::Part1TagTree, DecodeError> {
        match result { Err(error) => Err(error), Ok(tree) => Ok(tag_tree_view(&tree)) }
    }

    closed spec fn tag_path_view(path: TagTreePath) -> crate::specs::Part1TagPath {
        crate::specs::Part1TagPath { nodes: path.nodes@, length: path.length }
    }

    #[verifier::inline]
    spec fn tag_path_outcome(result: Result<TagTreePath, DecodeError>) -> Result<crate::specs::Part1TagPath, DecodeError> {
        match result { Err(error) => Err(error), Ok(path) => Ok(tag_path_view(path)) }
    }
}
