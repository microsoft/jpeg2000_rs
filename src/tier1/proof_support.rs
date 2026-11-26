#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn raw_bit_reader_view(reader: &RawBitReader<'_>) -> crate::specs::Part1RawReaderState {
        crate::specs::Part1RawReaderState {
            input: reader.input@,
            next_index: reader.next_index,
            current_byte: reader.current_byte,
            bits_remaining: reader.bits_remaining,
            marker_padding_count: reader.marker_padding_count,
            work_units: reader.work_units,
            maximum_work_units: reader.maximum_work_units,
        }
    }

    #[verifier::inline]
    spec fn raw_reader_outcome(result: Result<RawBitReader<'_>, DecodeError>)
        -> Result<crate::specs::Part1RawReaderState, DecodeError>
    {
        match result {
            Ok(reader) => Ok(raw_bit_reader_view(&reader)),
            Err(error) => Err(error),
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn ht_magsgn_view(reader: &HtForwardMagSgnReader<'_>) -> crate::specs::HtMagSgnState {
        crate::specs::HtMagSgnState {
            input: reader.input@, next_byte: reader.next_byte, value: reader.value,
            next_bit: reader.next_bit, last_bit: reader.last_bit, has_byte: reader.has_byte,
            current_is_physical: reader.current_is_physical, previous_was_ff: reader.previous_was_ff,
            physical_bits_read: reader.physical_bits_read, fill_bits_read: reader.fill_bits_read,
            work_units: reader.work_units, maximum_work_units: reader.maximum_work_units,
        }
    }

    #[verifier::inline]
    spec fn ht_magsgn_outcome(result: Result<HtForwardMagSgnReader<'_>, DecodeError>)
        -> Result<crate::specs::HtMagSgnState, DecodeError>
    {
        match result { Ok(reader) => Ok(ht_magsgn_view(&reader)), Err(error) => Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn ht_mel_view(reader: &HtMelBitReader<'_>) -> crate::specs::HtMelState {
        crate::specs::HtMelState {
            input: reader.input@, next_byte: reader.next_byte, current_byte: reader.current_byte,
            value: reader.value, next_bit: reader.next_bit, previous_was_ff: reader.previous_was_ff,
            bits_read: reader.bits_read, maximum_work_units: reader.maximum_work_units,
        }
    }

    #[verifier::inline]
    spec fn ht_mel_outcome(result: Result<HtMelBitReader<'_>, DecodeError>)
        -> Result<crate::specs::HtMelState, DecodeError>
    {
        match result { Ok(reader) => Ok(ht_mel_view(&reader)), Err(error) => Err(error) }
    }

    pub closed spec fn ht_position_view(position: Option<HtBitPosition>) -> Option<(u16, u8)> {
        match position { Some(position) => Some((position.byte, position.bit)), None => None }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn ht_reverse_vlc_view(reader: &HtReverseVlcReader<'_>) -> crate::specs::HtReverseVlcState {
        crate::specs::HtReverseVlcState {
            input: reader.input@, current_byte: reader.current_byte, value: reader.value,
            next_bit: reader.next_bit, last_bit: reader.last_bit, has_byte: reader.has_byte,
            later_byte_requires_unstuffing: reader.later_byte_requires_unstuffing,
            bits_read: reader.bits_read, maximum_work_units: reader.maximum_work_units,
        }
    }

    #[verifier::inline]
    spec fn ht_reverse_vlc_outcome(result: Result<HtReverseVlcReader<'_>, DecodeError>)
        -> Result<crate::specs::HtReverseVlcState, DecodeError>
    {
        match result { Ok(reader) => Ok(ht_reverse_vlc_view(&reader)), Err(error) => Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn ht_forward_refinement_view(reader: &HtForwardRefinementReader<'_>) -> crate::specs::HtForwardRefinementState {
        crate::specs::HtForwardRefinementState {
            input: reader.input@, next_byte: reader.next_byte, current_byte: reader.current_byte,
            value: reader.value, next_bit: reader.next_bit, last_bit: reader.last_bit,
            has_byte: reader.has_byte, previous_was_ff: reader.previous_was_ff,
            physical_bits_read: reader.physical_bits_read, fill_bits_read: reader.fill_bits_read,
            maximum_work_units: reader.maximum_work_units,
        }
    }

    #[verifier::inline]
    spec fn ht_forward_refinement_outcome(result: Result<HtForwardRefinementReader<'_>, DecodeError>)
        -> Result<crate::specs::HtForwardRefinementState, DecodeError>
    {
        match result { Ok(reader) => Ok(ht_forward_refinement_view(&reader)), Err(error) => Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn ht_reverse_refinement_view(reader: &HtReverseRefinementReader<'_>) -> crate::specs::HtReverseRefinementState {
        crate::specs::HtReverseRefinementState {
            input: reader.input@, current_byte: reader.current_byte, value: reader.value,
            next_bit: reader.next_bit, last_bit: reader.last_bit, has_byte: reader.has_byte,
            later_requires_unstuffing: reader.later_requires_unstuffing,
            physical_bits_read: reader.physical_bits_read, fill_bits_read: reader.fill_bits_read,
            maximum_work_units: reader.maximum_work_units,
        }
    }

    #[verifier::inline]
    spec fn ht_reverse_refinement_outcome(result: Result<HtReverseRefinementReader<'_>, DecodeError>)
        -> Result<crate::specs::HtReverseRefinementState, DecodeError>
    {
        match result { Ok(reader) => Ok(ht_reverse_refinement_view(&reader)), Err(error) => Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn ht_refinement_readers_view(readers: &HtRefinementReaders<'_>) -> crate::specs::HtRefinementReadersState {
        crate::specs::HtRefinementReadersState {
            forward: ht_forward_refinement_view(&readers.forward),
            reverse: match readers.reverse {
                None => None, Some(reverse) => Some(ht_reverse_refinement_view(&reverse)),
            },
            claimed: readers.claimed@, stuffed: readers.stuffed@,
        }
    }

    #[verifier::inline]
    spec fn ht_refinement_readers_outcome(result: Result<HtRefinementReaders<'_>, DecodeError>)
        -> Result<crate::specs::HtRefinementReadersState, DecodeError>
    {
        match result { Ok(readers) => Ok(ht_refinement_readers_view(&readers)), Err(error) => Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn ht_substream_view(stream: &HtSubstreamView<'_>) -> crate::specs::HtSubstreamState {
        crate::specs::HtSubstreamState {
            bytes: stream.bytes@, offset: stream.offset, forward: ht_direction_forward(stream.direction),
        }
    }

    pub closed spec fn ht_cleanup_segment_view(segment: &HtCleanupSegment<'_>) -> crate::specs::HtCleanupSegmentState {
        crate::specs::HtCleanupSegmentState {
            encoded: segment.encoded@, scup: segment.scup,
            mag_sgn: ht_substream_view(&segment.mag_sgn), mel_vlc: ht_substream_view(&segment.mel_vlc),
            mel: ht_substream_view(&segment.mel), vlc: ht_substream_view(&segment.vlc),
        }
    }

    pub closed spec fn ht_refinement_segment_view(segment: &HtRefinementSegment<'_>) -> crate::specs::HtRefinementSegmentState {
        crate::specs::HtRefinementSegmentState {
            encoded: segment.encoded@,
            significance_propagation: ht_substream_view(&segment.significance_propagation),
            magnitude_refinement: ht_substream_view(&segment.magnitude_refinement),
        }
    }

    pub closed spec fn ht_refinement_option_view(segment: Option<HtRefinementSegment<'_>>)
        -> Option<crate::specs::HtRefinementSegmentState>
    {
        match segment { None => None, Some(segment) => Some(ht_refinement_segment_view(&segment)) }
    }

    pub closed spec fn ht_block_segments_view(segments: &HtBlockSegments<'_>) -> crate::specs::HtBlockSegmentsState {
        crate::specs::HtBlockSegmentsState {
            cleanup: ht_cleanup_segment_view(&segments.cleanup),
            refinement: ht_refinement_option_view(segments.refinement), bytes: segments.bytes,
        }
    }

    pub open spec fn ht_optional_bytes_view(bytes: Option<&[u8]>) -> Option<Seq<u8>> {
        match bytes { None => None, Some(bytes) => Some(bytes@) }
    }

    pub closed spec fn ht_block_segments_outcome(result: Result<HtBlockSegments<'_>, DecodeError>)
        -> Result<crate::specs::HtBlockSegmentsState, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(segments) => Ok(ht_block_segments_view(&segments)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn ht_cleanup_readers_view(readers: &HtCleanupReaders<'_>) -> crate::specs::HtCleanupReaderState {
        crate::specs::HtCleanupReaderState {
            mel: ht_mel_view(&readers.mel), vlc: ht_reverse_vlc_view(&readers.vlc),
            mel_last_byte: readers.mel_last_byte, vlc_last_byte: readers.vlc_last_byte,
            terminal_byte: readers.terminal_byte, mel_state: readers.mel_state,
            mel_zero_events: readers.mel_zero_events, mel_terminating_one: readers.mel_terminating_one,
            mel_events: readers.mel_events, work_units: readers.work_units,
            maximum_work_units: readers.maximum_work_units,
        }
    }

    pub closed spec fn ht_direction_forward(direction: HtStreamDirection) -> bool {
        matches!(direction, HtStreamDirection::Forward)
    }

    pub closed spec fn ht_vlc_table_view(initial: bool) -> Seq<u16> {
        if initial { HT_VLC_INITIAL@ } else { HT_VLC_NON_INITIAL@ }
    }

    #[verifier::inline]
    spec fn ht_cleanup_readers_outcome(result: Result<HtCleanupReaders<'_>, DecodeError>)
        -> Result<crate::specs::HtCleanupReaderState, DecodeError>
    {
        match result { Ok(readers) => Ok(ht_cleanup_readers_view(&readers)), Err(error) => Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    #[verifier::inline]
    spec fn ht_metadata_words_outcome(result: Result<([u16; 2], [u8; 2]), DecodeError>)
        -> Result<(Seq<u16>, Seq<u8>), DecodeError>
    {
        match result { Err(error) => Err(error), Ok((words, contexts)) => Ok((words@, contexts@)) }
    }

    #[verifier::inline]
    spec fn ht_metadata_quad_input(
        index: usize, row: usize, width: u16, height: u16, maximum_u: u8,
        word: u16, context: u8, significance: u8, u_value: u8, initial: bool,
    ) -> crate::specs::HtMetadataQuadInput {
        crate::specs::HtMetadataQuadInput {
            index, row, width, height, maximum_u, word, context, significance, u_value, initial,
        }
    }

    #[verifier::inline]
    spec fn ht_metadata_pair_view(
        readers: &HtCleanupReaders<'_>, quads: &Vec<HtQuadMetadata>,                 current: Seq<u8>, significant: u16, left: u8,
    ) -> crate::specs::HtMetadataPairState {
        crate::specs::HtMetadataPairState {
            readers: ht_cleanup_readers_view(readers), quads: quads@, current, significant, left,
        }
    }

    #[verifier::inline]
    spec fn ht_metadata_row_view(
        readers: &HtCleanupReaders<'_>, quads: &Vec<HtQuadMetadata>, previous: &Vec<u8>, significant: u16,
    ) -> crate::specs::HtMetadataRowState {
        crate::specs::HtMetadataRowState {
            readers: ht_cleanup_readers_view(readers), quads: quads@, previous: previous@, significant,
        }
    }

    pub closed spec fn ht_cleanup_metadata_view(metadata: &HtCleanupMetadata) -> crate::specs::HtMetadataOutput {
        crate::specs::HtMetadataOutput {
            width: metadata.width, height: metadata.height, quads: metadata.quads@,
            significant_samples: metadata.significant_samples, mel_bits: metadata.mel_bits,
            vlc_bits: metadata.vlc_bits, mel_events: metadata.mel_events,
        }
    }

    pub closed spec fn ht_cleanup_metadata_outcome(result: Result<HtCleanupMetadata, DecodeError>)
        -> Result<crate::specs::HtMetadataOutput, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(metadata) => Ok(ht_cleanup_metadata_view(&metadata)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    #[verifier::inline]
    spec fn ht_numeric_magnitude_outcome(result: Result<(Magnitude, bool, u8), DecodeError>)
        -> Result<(nat, bool, u8), DecodeError>
    {
        match result {
            Err(error) => Err(error),
            Ok((magnitude, negative, exponent)) => Ok((crate::magnitude::magnitude_value(magnitude), negative, exponent)),
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn ht_plane_view(state: &HtCleanupPlaneReconstruction<'_>) -> crate::specs::HtPlaneState {
        crate::specs::HtPlaneState {
            output: code_block_plane_view(&state.output), reader: ht_magsgn_view(&state.reader),
            previous: state.previous_exponents@, current: state.current_exponents@, statistics: state.statistics,
        }
    }

    closed spec fn ht_plane_outcome(result: Result<(CodeBlockPlane, Tier1PassStatistics), DecodeError>)
        -> Result<(crate::specs::Tier1RawPlane, Tier1PassStatistics), DecodeError> {
        match result { Err(error) => Err(error), Ok((plane, statistics)) => Ok((code_block_plane_view(&plane), statistics)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    spec fn ht_boolean_vector_view(value: Vec<bool>) -> Seq<bool> { value@ }
    spec fn ht_cleanup_flags_outcome(value: Result<Vec<bool>, DecodeError>) -> Result<Seq<bool>, DecodeError> {
        match value { Ok(flags) => Ok(flags@), Err(error) => Err(error) }
    }

    spec fn ht_refinement_magnitude_outcome(result: Result<Magnitude, DecodeError>) -> Result<(Seq<u64>, nat), DecodeError> {
        match result { Err(error) => Err(error), Ok(value) => Ok((
            crate::magnitude::magnitude_limbs(value), crate::magnitude::magnitude_value(value))) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    spec fn ht_byte_vector_outcome(result: Result<Vec<u8>, DecodeError>) -> Result<Seq<u8>, DecodeError> {
        match result { Err(error) => Err(error), Ok(value) => Ok(value@) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    spec fn ht_cleanup_prepare_outcome(result: Result<(CodeBlockPlane, ht_checkpoint::HtCleanupCheckpoint, Tier1PassStatistics, u16), DecodeError>)
        -> Result<(crate::specs::Tier1RawPlane, crate::specs::Tier1RawPlane, Tier1PassStatistics, u16), DecodeError> {
        match result {
            Err(error) => Err(error),
            Ok((plane, cleanup, statistics, bitplanes)) =>
                Ok((code_block_plane_view(&plane), cleanup.view(), statistics, bitplanes)),
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn ht_refinement_core_view(state: &HtRefinementPlaneState<'_>) -> crate::specs::HtRefinementCoreState {
        crate::specs::HtRefinementCoreState {
            output: code_block_plane_view(&state.output), readers: ht_refinement_readers_view(&state.readers),
            cleanup_significant: state.cleanup_significant@, statistics: state.statistics,
        }
    }

    closed spec fn ht_sigprop_patch_view(state: &HtSignificancePatchState<'_>) -> crate::specs::HtSignificancePatchState {
        crate::specs::HtSignificancePatchState {
            core: ht_refinement_core_view(&state.core), discovery: code_block_plane_view(&state.discovery), pending: state.pending@,
        }
    }

    spec fn ht_refinement_magnitude_view(value: Magnitude) -> (Seq<u64>, nat) {
        (crate::magnitude::magnitude_limbs(value), crate::magnitude::magnitude_value(value))
    }

    closed spec fn ht_sigprop_plane_view(state: &HtSigpropPlaneState<'_>) -> crate::specs::HtSigpropPlaneState {
        crate::specs::HtSigpropPlaneState { core: ht_refinement_core_view(&state.core), discovery: code_block_plane_view(&state.discovery) }
    }

    spec fn ht_sigprop_plane_outcome(result: (Result<(), DecodeError>, HtSigpropPlaneState<'_>))
        -> crate::specs::HtSigpropPlaneResult {
        (result.0, ht_sigprop_plane_view(&result.1))
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn coefficient_raw_view(value: CoefficientState) -> crate::specs::Tier1RawCoefficient {
        crate::specs::Tier1RawCoefficient {
            limbs: Seq::empty().push(value.magnitude) + value.magnitude_high@,
            legacy_bitplane: value.legacy_bitplane, negative: value.negative,
            significant: value.significant, refined: value.refined,
        }
    }

    pub open spec fn coefficient_raw_views(values: Seq<CoefficientState>) -> Seq<crate::specs::Tier1RawCoefficient> {
        Seq::new(values.len(), |i: int| coefficient_raw_view(values[i]))
    }

    pub open spec fn coefficient_state_view(value: &CoefficientState) -> crate::specs::Tier1RawCoefficient {
        coefficient_raw_view(*value)
    }

    pub open spec fn coefficient_slice_view(values: &[CoefficientState]) -> Seq<crate::specs::Tier1RawCoefficient> {
        coefficient_raw_views(values@)
    }

    pub(crate) open spec fn coefficient_signed_outcome(result: Result<SignedMagnitude, DecodeError>)
        -> Result<(Seq<u64>, nat, bool), DecodeError>
    {
        match result {
            Err(error) => Err(error),
            Ok(value) => Ok((crate::magnitude::magnitude_limbs(value.magnitude),
                crate::magnitude::magnitude_value(value.magnitude), value.negative)),
        }
    }

    pub open spec fn coefficient_raw_outcome(result: Result<CoefficientState, DecodeError>)
        -> Result<crate::specs::Tier1RawCoefficient, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(coefficient_raw_view(value)) }
    }

    pub proof fn coefficient_raw_shape(value: CoefficientState)
        ensures coefficient_raw_view(value).limbs.len() == 6,
    {}
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn legacy_bitplane_view(state: &Tier1BitplaneState) -> crate::specs::Part1LegacyBitplane {
        crate::specs::Part1LegacyBitplane {
            width: state.width, height: state.height, bitplane: state.bitplane,
            significant_before: state.significant_before@, significance_visited: state.significance_visited@,
            significance_propagation_complete: state.significance_propagation_complete,
            magnitude_refinement_complete: state.magnitude_refinement_complete,
            cleanup_complete: state.cleanup_complete,
        }
    }

    pub open spec fn legacy_bitplane_outcome(result: Result<Tier1BitplaneState, DecodeError>)
        -> Result<crate::specs::Part1LegacyBitplane, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(state) => Ok(legacy_bitplane_view(&state)) }
    }

    pub closed spec fn legacy_bitplane_option_view(source:&Option<Tier1BitplaneState>)->Option<crate::specs::Part1LegacyBitplane> {
        match source{None=>None,Some(value)=>Some(legacy_bitplane_view(value))}
    }
    pub open spec fn legacy_bitplane_option_outcome(result:Result<Option<Tier1BitplaneState>,DecodeError>)->Result<Option<crate::specs::Part1LegacyBitplane>,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok(legacy_bitplane_option_view(&value))}
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) open spec fn legacy_storage_limits(limits:&ResourceLimits)->crate::specs::Part2LegacyCaps {
        crate::specs::part2_legacy_caps(crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits))
    }
    pub(crate) open spec fn compact_legacy_storage_limits(limits:&ResourceLimits)->crate::specs::Part2CompactLegacyCaps {
        crate::specs::Part2CompactLegacyCaps {
            legacy:legacy_storage_limits(limits),
            decoded:crate::limits::resource_decoded_bytes_limit(limits),
            wide_bytes:core::mem::size_of::<CoefficientState>(),
        }
    }
    pub closed spec fn legacy_segment_view(legacy: &LegacySegmentState) -> crate::specs::Tier1LegacyFrame {
        crate::specs::Tier1LegacyFrame {
            plane: code_block_plane_view(&legacy.plane), next_pass: legacy.next_pass, bitplane: legacy.bitplane,
            bitplane_state: match legacy.bitplane_state {
                None => None, Some(state) => Some(legacy_bitplane_view(&state)),
            },
            mq_context_state: match legacy.mq_context_state {
                None => None, Some(state) => Some(crate::mq::mq_context_state_view(state)),
            },
            reset_contexts_before_mq: legacy.reset_contexts_before_mq,
            decoded_segments: legacy.decoded_segments, decoded_bytes: legacy.decoded_bytes,
            input: legacy.input@, passes: legacy.passes,
        }
    }

    pub open spec fn legacy_segment_outcome(result:Result<LegacySegmentState,DecodeError>)->Result<crate::specs::Tier1LegacyFrame,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok(legacy_segment_view(&value))}
    }
    pub closed spec fn legacy_segment_option_view(source:&Option<LegacySegmentState>)->Option<crate::specs::Tier1LegacyFrame> {
        match source{None=>None,Some(value)=>Some(legacy_segment_view(value))}
    }
    pub open spec fn legacy_segment_option_outcome(result:Result<Option<LegacySegmentState>,DecodeError>)->Result<Option<crate::specs::Tier1LegacyFrame>,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok(legacy_segment_option_view(&value))}
    }

    pub closed spec fn tier1_decoder_state(decoder: &Tier1CodeBlockDecoder) -> crate::specs::Tier1DecoderState {
        crate::specs::Tier1DecoderState {
            plane: code_block_plane_view(&decoder.plane), orientation: decoder.orientation,
            private_plan: decoder.private_plan,
            style: decoder.style, maximum_passes: decoder.maximum_passes, next_pass: decoder.next_pass,
            bitplane: decoder.bitplane, zero_bitplanes: decoder.zero_bitplanes,
            bitplane_state: match decoder.bitplane_state {
                None => None, Some(state) => Some(legacy_bitplane_view(&state)),
            },
            mq_context_state: match decoder.mq_context_state {
                None => None, Some(state) => Some(crate::mq::mq_context_state_view(state)),
            },
            reset_contexts_before_mq: decoder.reset_contexts_before_mq,
            decoded_segments: decoder.decoded_segments, decoded_bytes: decoder.decoded_bytes,
            legacy_segment: match decoder.legacy_segment {
                None => None,
                Some(legacy) => Some(legacy_segment_view(&legacy)),
            },
            legacy_decode_work: decoder.legacy_decode_work,
            ht_cleanup_plane: match decoder.ht_cleanup_plane { None => None, Some(plane) => Some(plane.view()) },
            ht_refinement_data: decoder.ht_refinement_data@, ht_refinement_passes: decoder.ht_refinement_passes,
            ht_decoded_bitplanes: decoder.ht_decoded_bitplanes,
            ht_current_set_has_cleanup: decoder.ht_current_set_has_cleanup, ht_sets_seen: decoder.ht_sets_seen,
            allow_multiple_ht_sets: decoder.allow_multiple_ht_sets, ht_magnitude_bound: decoder.ht_magnitude_bound,
        }
    }

    pub closed spec fn tier1_max_ht_magnitude_bits() -> u8 { MAX_HT_MAGNITUDE_BITS }

    pub open spec fn tier1_initial_decoder_outcome(result: Result<Tier1CodeBlockDecoder, DecodeError>)
        -> Result<crate::specs::Tier1DecoderState, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(decoder) => Ok(tier1_decoder_state(&decoder)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn legacy_symbols_view<D: Tier1SymbolDecoder>(decoder: &D) -> crate::specs::Part1LegacySymbols {
        decoder.symbols_view()
    }

    closed spec fn legacy_frame_view<D: Tier1SymbolDecoder>(plane: &CodeBlockPlane, state: &Tier1BitplaneState,
        decoder: &D, statistics: Tier1PassStatistics) -> crate::specs::Part1LegacyFrame {
        crate::specs::Part1LegacyFrame {
            plane: code_block_plane_view(plane), state: legacy_bitplane_view(state),
            symbols: legacy_symbols_view(decoder), statistics,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    spec fn neighbor_kind_tag(kind: NeighborKind) -> u8 {
        match kind { NeighborKind::Horizontal => 0, NeighborKind::Vertical => 1, NeighborKind::Diagonal => 2 }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn code_block_plane_view(plane: &CodeBlockPlane) -> crate::specs::Tier1RawPlane {
        crate::specs::Tier1RawPlane {
            width: plane.width, height: plane.height, coefficients: coefficient_raw_views(plane.coefficients@),
        }
    }

    pub closed spec fn tier1_decoder_plane_view(decoder: &Tier1CodeBlockDecoder) -> crate::specs::Tier1RawPlane {
        code_block_plane_view(&decoder.plane)
    }

    pub proof fn tier1_decoder_plane_matches_state(decoder: &Tier1CodeBlockDecoder)
        ensures tier1_decoder_plane_view(decoder) == tier1_decoder_state(decoder).plane,
    {
        reveal(tier1_decoder_plane_view);
        reveal(tier1_decoder_state);
    }

    pub closed spec fn code_block_plane_outcome(result: Result<CodeBlockPlane, DecodeError>)
        -> Result<crate::specs::Tier1RawPlane, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(plane) => Ok(code_block_plane_view(&plane)) }
    }
}
