//! Codestream entry points and main-header/layout orchestration.

use super::mct_resolution::{
    validate_unique_mct_array_indexes, validate_unique_mct_record_indexes,
};
use super::persistent_tile_configuration::inherited_tile_owner;
use super::profile::classify_codestream_profile;
use super::reader::new_parser;
use super::{
    ADS, ATK, CAP, CBD, COC, COD, CPF, CRG, CodestreamInfo, CodestreamLayout,
    ComponentQuantizations, DFS, DecodeError, EOC, ImageSize, MAX_COMPONENTS, MCC, MCO, MCT,
    MalformedKind, MctParameters, NLT, PLM, POC, PPM, PRF, PackedPacketHeaderSource,
    PackedPacketHeaders, PacketLengths, Parser, Part2Extensions, ProgressionChanges, QCC, QCD, RGN,
    Resource, ResourceLimits, RoiShifts, SIZ, SOC, SOT, TLM, TilePartPayload,
};
#[cfg(verus_keep_ghost)]
use super::{
    layout_prologue_outcome, mct_parameter_copy_view, optional_roi_shifts_view,
    owned_extensions_view, parser_view, persistent_tile_configuration_view,
    persistent_tile_state_view, progression_changes_view, quantization_owner_view,
    tile_part_payload_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub fn parse(input: &[u8], limits: &ResourceLimits) -> Result<CodestreamInfo, DecodeError> {
    Ok(parse_layout(input, limits)?.info)
}
pub fn parse_layout<'a>(
    input: &'a [u8],
    limits: &'a ResourceLimits,
) -> Result<CodestreamLayout<'a>, DecodeError> {
    new_parser(input, limits)?.parse_layout()
}
impl<'a> Parser<'a> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (layout_prologue_outcome(result), parser_view(final(self)))
            == crate::specs::part1_parse_layout_prologue(parser_view(old(self))),
    ))]
    pub(super) fn parse_layout_prologue(&mut self) -> Result<(ImageSize, u16, usize), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_parse_layout_prologue);
            reveal(parser_view);
            reveal(layout_prologue_outcome);
        }
        self.expect_standalone(SOC)?;
        let siz = self.read_segment()?;
        if siz.marker != SIZ {
            return Err(DecodeError::malformed(
                self.offset(siz.offset),
                MalformedKind::InvalidMarkerOrder,
            ));
        }
        let (image_size, r_siz) = self.parse_siz(siz)?;
        let main_header_start = self.position;
        Ok((image_size, r_siz, main_header_start))
    }

    fn parse_layout(self) -> Result<CodestreamLayout<'a>, DecodeError> {
        let mut parser = self;
        let (mut image_size, r_siz, main_header_start) = parser.parse_layout_prologue()?;
        let mut main_header_segments = 1_u64;
        let mut coding_style = None;
        let mut qcd_segment = None;
        let mut coc_segments = [None; MAX_COMPONENTS];
        let mut qcc_segments = [None; MAX_COMPONENTS];
        let mut roi_shifts = RoiShifts::none();
        let mut roi_seen = [false; MAX_COMPONENTS];
        let mut plm_groups = Vec::new();
        let mut next_plm_index = 0_u16;
        let mut plm_seen = false;
        let mut ppm_bytes = Vec::new();
        let mut next_ppm_index = 0_u16;
        let mut ppm_fragments = 0_u16;
        let mut progression_changes = ProgressionChanges::none();
        let mut poc_seen = false;
        let mut mct_arrays = Vec::new();
        let mut mct_records = Vec::new();
        let mut mct_order = None;
        let mut pending_mct = Vec::new();
        let mut completed_mct = Vec::new();
        let mut pending_mcc = Vec::new();
        let mut completed_mcc = Vec::new();
        let mut extended_capabilities = None;
        let mut profile = None;
        let mut corresponding_profile = None;
        let mut part2_extensions = Part2Extensions::default();
        let mut next_tlm_index = 0_u16;
        let input_length = parser.input.len();

        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(decreases input_length as int - parser.position as int,)
        )]
        loop {
            let previous_position = parser.position;
            let Some(segment) = parser.read_main_header_segment(&mut main_header_segments)? else {
                break;
            };
            match segment.marker {
                CAP if extended_capabilities.is_some() => {
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                CAP => extended_capabilities = Some(parser.parse_cap(segment)?),
                PRF if profile.is_some() => {
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                PRF => profile = Some(parser.parse_profile_number(segment)?),
                CPF if corresponding_profile.is_some() => {
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                CPF => corresponding_profile = Some(parser.parse_profile_number(segment)?),
                COD if coding_style.is_some() => {
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                COD => coding_style = Some(parser.parse_cod(segment)?),
                COC => {
                    parser.record_component_segment(
                        segment,
                        image_size.components,
                        MalformedKind::InvalidCodingStyle,
                        &mut coc_segments,
                    )?;
                }
                QCD if qcd_segment.is_some() => {
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                QCD => qcd_segment = Some(segment),
                QCC => {
                    parser.record_component_segment(
                        segment,
                        image_size.components,
                        MalformedKind::InvalidQuantization,
                        &mut qcc_segments,
                    )?;
                }
                RGN => {
                    let (component, shift) = parser.parse_rgn(segment, image_size.components)?;
                    let index = usize::from(component);
                    if index >= roi_seen.len() || roi_seen[index] {
                        return Err(DecodeError::malformed(
                            parser.offset(segment.offset),
                            MalformedKind::InvalidMarkerOrder,
                        ));
                    }
                    roi_seen[index] = true;
                    roi_shifts.set(component, shift)?;
                }
                PLM => {
                    plm_seen = true;
                    parser.parse_plm(segment, &mut next_plm_index, &mut plm_groups)?;
                }
                PPM => {
                    parser.parse_packed_fragment(
                        segment,
                        PPM,
                        &mut next_ppm_index,
                        &mut ppm_fragments,
                        &mut ppm_bytes,
                    )?;
                }
                POC => {
                    if poc_seen {
                        return Err(DecodeError::malformed(
                            parser.offset(segment.offset),
                            MalformedKind::InvalidMarkerOrder,
                        ));
                    }
                    poc_seen = true;
                    progression_changes = parser.parse_poc(segment, image_size.components)?;
                }
                TLM => parser.parse_tlm(
                    segment,
                    &mut next_tlm_index,
                    image_size.tile_count()?,
                    &mut part2_extensions,
                )?,
                CRG => parser.parse_crg(segment, image_size.components, &mut part2_extensions)?,
                DFS => parser.parse_dfs(segment, &mut part2_extensions)?,
                ADS => parser.parse_ads(segment, &mut part2_extensions)?,
                NLT => parser.parse_nlt(segment, image_size.components, &mut part2_extensions)?,
                CBD => parser.parse_cbd(segment, image_size.components, &mut part2_extensions)?,
                ATK => parser.parse_atk(segment, &mut part2_extensions)?,
                MCT => {
                    if let Some(array) = parser.consume_mct_fragment(
                        segment,
                        &mut pending_mct,
                        &mut completed_mct,
                    )? {
                        mct_arrays.push(array);
                        validate_unique_mct_array_indexes(&mct_arrays, segment.offset)?;
                    }
                }
                MCC => {
                    if let Some(record) = parser.consume_mcc_fragment(
                        segment,
                        image_size.components,
                        &mut pending_mcc,
                        &mut completed_mcc,
                    )? {
                        mct_records.push(record);
                        validate_unique_mct_record_indexes(&mct_records, segment.offset)?;
                    }
                }
                MCO => {
                    if mct_order.is_some() {
                        return Err(DecodeError::malformed(
                            parser.offset(segment.offset),
                            MalformedKind::InvalidMarkerOrder,
                        ));
                    }
                    mct_order = Some(parser.parse_mco(segment)?);
                }
                0xff64 => {}
                marker => {
                    let _ = marker;
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarker,
                    ));
                }
            }
            if !crate::refinement::parser_progress(previous_position, parser.position, input_length)
            {
                return Err(parser.malformed_here(MalformedKind::InvalidMarkerLength));
            }
        }
        if !pending_mct.is_empty() || !pending_mcc.is_empty() {
            return Err(parser.malformed_here(MalformedKind::MissingRequiredStructure));
        }
        parser
            .apply_component_bit_depths(&mut image_size, &part2_extensions.component_bit_depths)?;
        let main_header_end = parser.position;
        let ppm_frames = parser.parse_ppm_frames(&ppm_bytes, ppm_fragments)?;
        let main_header = parser
            .input
            .get(main_header_start..main_header_end)
            .ok_or_else(|| parser.malformed_here(MalformedKind::InvalidPackedPacketHeader))?;

        let coding_style = coding_style
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::MissingRequiredStructure))?;
        let qcd_segment = qcd_segment
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::MissingRequiredStructure))?;
        let quantization = parser.parse_qcd(qcd_segment, coding_style)?;
        let component_coding_styles = parser.finish_main_component_styles(
            image_size.components,
            coding_style,
            &coc_segments,
            &part2_extensions,
        )?;
        let component_quantizations = parser.finish_main_component_quantizations(
            image_size.components,
            quantization,
            &component_coding_styles,
            &qcc_segments,
        )?;
        parser.validate_progression_changes(
            &progression_changes,
            coding_style.layers,
            &component_coding_styles,
            0,
        )?;
        if (!mct_arrays.is_empty() || !mct_records.is_empty()) && mct_order.is_none() {
            return Err(DecodeError::malformed(
                0,
                MalformedKind::MissingRequiredStructure,
            ));
        }
        parser.apply_component_registrations(
            &mut image_size,
            &part2_extensions.component_registrations,
        )?;
        let main_mct_parameters = MctParameters {
            arrays: mct_arrays,
            records: mct_records,
            order: mct_order.unwrap_or_default(),
        };
        let multiple_component_transform =
            parser.resolve_multiple_component_transform(&main_mct_parameters)?;
        let tile_count = image_size.tile_count()?;
        let mut tile_parts = 0_u32;
        let mut tile_part_payloads: Vec<TilePartPayload<'a>> = Vec::new();
        let tile_state_count = usize::try_from(tile_count)
            .map_err(|_| parser.malformed_here(MalformedKind::ArithmeticOverflow))?;
        let mut tile_roi_shifts = vec![None; tile_state_count];
        let mut tile_coding_styles = vec![None; tile_state_count];
        let mut tile_quantizations = vec![None; tile_state_count];
        let mut tile_component_style_parts: Vec<Option<usize>> = vec![None; tile_state_count];
        let mut tile_component_quantizations: Vec<Option<ComponentQuantizations>> =
            vec![None; tile_state_count];
        let mut tile_progression_changes: Vec<Option<ProgressionChanges>> =
            vec![None; tile_state_count];
        let mut tile_mct_parameters: Vec<Option<MctParameters>> = vec![None; tile_state_count];
        let mut tile_part2_extensions: Vec<Option<Part2Extensions>> = vec![None; tile_state_count];

        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial_persistent_state = persistent_tile_state_view(
                tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                tile_component_style_parts@, tile_component_quantizations@,
                tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                tile_part_payloads@);
            let ghost mut persistent_commits: Seq<crate::specs::Part1PersistentTileCommit> = Seq::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(persistent_tile_state_view);
            reveal(persistent_tile_configuration_view);
            reveal(super::persistent_tile_configuration_sequences_view);
            assert(initial_persistent_state == crate::specs::part1_empty_persistent_tile_state(tile_state_count));
            reveal(crate::specs::part1_persistent_tile_state_fold);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    crate::specs::part1_persistent_tile_state_fold(
                        initial_persistent_state, persistent_commits)
                        == (Ok(()), persistent_tile_state_view(
                            tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                            tile_component_style_parts@, tile_component_quantizations@,
                            tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                            tile_part_payloads@)),
                    tile_component_style_parts.len() == tile_state_count,
                    forall|tile: int| 0 <= tile < tile_component_style_parts.len() ==>
                        match #[trigger] tile_component_style_parts@[tile] {
                            Some(part) => part < tile_part_payloads.len()
                                && tile_part_payloads@[part as int].tile_index as int == tile
                                && forall|later: int| part < later < tile_part_payloads.len() ==>
                                    (#[trigger] tile_part_payloads@[later]).tile_index as int != tile,
                            None => forall|prior: int| 0 <= prior < tile_part_payloads.len() ==>
                                (#[trigger] tile_part_payloads@[prior]).tile_index as int != tile,
                        },
                decreases input_length as int - parser.position as int,
            )
        )]
        loop {
            let previous_position = parser.position;
            match parser.peek_marker()? {
                SOT => {
                    tile_parts = tile_parts
                        .checked_add(1)
                        .ok_or_else(|| parser.malformed_here(MalformedKind::ArithmeticOverflow))?;
                    if tile_parts > parser.limits.maximum_tile_parts() {
                        return Err(DecodeError::limit(
                            Resource::TileParts,
                            u64::from(parser.limits.maximum_tile_parts()),
                            u64::from(tile_parts),
                        ));
                    }
                    let tile_part = parser.read_sot(tile_count)?;
                    if !part2_extensions.tile_part_lengths.is_empty() {
                        let entry_index = usize::try_from(tile_parts - 1).map_err(|_| {
                            parser.malformed_here(MalformedKind::ArithmeticOverflow)
                        })?;
                        let entry = part2_extensions
                            .tile_part_lengths
                            .get(entry_index)
                            .ok_or_else(|| {
                                DecodeError::malformed(
                                    parser.offset(tile_part.start),
                                    MalformedKind::InvalidTilePart,
                                )
                            })?;
                        if entry.length != tile_part.length
                            || matches!(entry.tile_index, Some(index) if index != tile_part.tile_index)
                        {
                            return Err(DecodeError::malformed(
                                parser.offset(tile_part.start),
                                MalformedKind::InvalidTilePart,
                            ));
                        }
                    }
                    let main_packet_lengths = if plm_seen {
                        *plm_groups
                            .get(usize::try_from(tile_parts - 1).map_err(|_| {
                                parser.malformed_here(MalformedKind::ArithmeticOverflow)
                            })?)
                            .ok_or_else(|| {
                                DecodeError::malformed(
                                    parser.offset(tile_part.start),
                                    MalformedKind::InvalidPacketLength,
                                )
                            })?
                    } else {
                        PacketLengths::none()
                    };
                    let packed_packet_headers = if ppm_fragments != 0 {
                        let frame = *ppm_frames
                            .get(usize::try_from(tile_parts - 1).map_err(|_| {
                                parser.malformed_here(MalformedKind::ArithmeticOverflow)
                            })?)
                            .ok_or_else(|| {
                                DecodeError::malformed(
                                    parser.offset(tile_part.start),
                                    MalformedKind::InvalidPackedPacketHeader,
                                )
                            })?;
                        PackedPacketHeaders {
                            source: PackedPacketHeaderSource::MarkerSegments {
                                header: main_header,
                                marker: PPM,
                                logical_start: frame.start,
                            },
                            length: frame.length,
                            fragments: ppm_fragments,
                        }
                    } else {
                        PackedPacketHeaders::none()
                    };
                    let tile_index = usize::from(tile_part.tile_index);
                    let (
                        previous_roi_shifts,
                        inherited_roi_shifts,
                        inherited_default_style,
                        inherited_default_quantization,
                        inherited_component_styles,
                    ) = parser.select_inherited_tile_configuration(
                        tile_index,
                        &roi_shifts,
                        &coding_style,
                        &quantization,
                        &component_coding_styles,
                        &tile_roi_shifts,
                        &tile_coding_styles,
                        &tile_quantizations,
                        &tile_component_style_parts,
                        &tile_part_payloads,
                    )?;
                    let inherited_component_quantizations = inherited_tile_owner(
                        tile_index,
                        &component_quantizations,
                        &tile_component_quantizations,
                    )
                    .clone();
                    let inherited_progression_changes = inherited_tile_owner(
                        tile_index,
                        &progression_changes,
                        &tile_progression_changes,
                    )
                    .clone();
                    let inherited_mct_parameters = inherited_tile_owner(
                        tile_index,
                        &main_mct_parameters,
                        &tile_mct_parameters,
                    )
                    .clone();
                    let inherited_part2_extensions =
                        inherited_tile_owner(tile_index, &part2_extensions, &tile_part2_extensions)
                            .clone();
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(crate::specs::part1_inherited_tile_owner);
                        assert(quantization_owner_view(&inherited_component_quantizations)
                            == quantization_owner_view(&crate::specs::part1_inherited_tile_owner(
                                tile_index, component_quantizations, tile_component_quantizations@)));
                        assert(progression_changes_view(&inherited_progression_changes)
                            == progression_changes_view(&crate::specs::part1_inherited_tile_owner(
                                tile_index, progression_changes, tile_progression_changes@)));
                        assert(mct_parameter_copy_view(&inherited_mct_parameters)
                            == mct_parameter_copy_view(&crate::specs::part1_inherited_tile_owner(
                                tile_index, main_mct_parameters, tile_mct_parameters@)));
                        assert(owned_extensions_view(&inherited_part2_extensions)
                            == owned_extensions_view(&crate::specs::part1_inherited_tile_owner(
                                tile_index, part2_extensions, tile_part2_extensions@)));
                    }
                    let (payload, tile_parameters, tile_extensions) = parser.read_tile_part(
                        tile_part,
                        (inherited_default_style, inherited_default_quantization),
                        inherited_component_styles,
                        inherited_component_quantizations,
                        inherited_roi_shifts,
                        inherited_progression_changes,
                        inherited_mct_parameters,
                        inherited_part2_extensions,
                        image_size.components,
                        main_packet_lengths,
                        packed_packet_headers,
                    )?;
                    #[cfg(verus_keep_ghost)]
                    proof_decl! {
                        let ghost previous_style_parts = tile_component_style_parts@;
                        let ghost previous_payloads = tile_part_payloads@;
                        let ghost previous_persistent_commits = persistent_commits;
                        let ghost previous_persistent_state = persistent_tile_state_view(
                            tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                            tile_component_style_parts@, tile_component_quantizations@,
                            tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                            tile_part_payloads@);
                        let ghost persistent_commit = crate::specs::Part1PersistentTileCommit {
                            position: parser.position, start: tile_part.start, index: tile_index,
                            previous_roi: optional_roi_shifts_view(previous_roi_shifts),
                            payload: tile_part_payload_view(&payload),
                            parameters: mct_parameter_copy_view(&tile_parameters),
                            extensions: owned_extensions_view(&tile_extensions),
                        };
                    }
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(crate::specs::part1_persistent_tile_state_fold(
                            initial_persistent_state, previous_persistent_commits)
                            == (Ok(()), previous_persistent_state));
                    }
                    parser.commit_persistent_tile_configuration(
                        tile_part.start,
                        tile_index,
                        tile_part_payloads.len(),
                        previous_roi_shifts,
                        &payload,
                        &mut tile_roi_shifts,
                        &mut tile_coding_styles,
                        &mut tile_quantizations,
                        &mut tile_component_style_parts,
                        &mut tile_component_quantizations,
                        &mut tile_progression_changes,
                    )?;
                    *tile_mct_parameters
                        .get_mut(tile_index)
                        .ok_or_else(|| parser.malformed_here(MalformedKind::InvalidTilePart))? =
                        Some(tile_parameters);
                    *tile_part2_extensions
                        .get_mut(tile_index)
                        .ok_or_else(|| parser.malformed_here(MalformedKind::InvalidTilePart))? =
                        Some(tile_extensions);
                    tile_part_payloads.push(payload);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(persistent_tile_state_view);
                        reveal(persistent_tile_configuration_view);
                        reveal(super::persistent_tile_configuration_sequences_view);
                        reveal(crate::specs::part1_commit_persistent_tile_state);
                        assert(crate::specs::part1_commit_persistent_tile_state(
                            previous_persistent_state, persistent_commit)
                            == (Ok(()), persistent_tile_state_view(
                                tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                                tile_component_style_parts@, tile_component_quantizations@,
                                tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                                tile_part_payloads@)));
                        persistent_commits = persistent_commits.push(persistent_commit);
                        assert(persistent_commits.drop_last() == previous_persistent_commits);
                        assert(persistent_commits.last() == persistent_commit);
                        reveal(crate::specs::part1_persistent_tile_state_fold);
                        assert(crate::specs::part1_persistent_tile_state_fold(
                            initial_persistent_state, persistent_commits)
                            == (Ok(()), persistent_tile_state_view(
                                tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                                tile_component_style_parts@, tile_component_quantizations@,
                                tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                                tile_part_payloads@)));
                        assert forall|tile: int| 0 <= tile < tile_component_style_parts.len() implies
                            match #[trigger] tile_component_style_parts@[tile] {
                                Some(part) => part < tile_part_payloads.len()
                                    && tile_part_payloads@[part as int].tile_index as int == tile
                                    && forall|later: int| part < later < tile_part_payloads.len() ==>
                                        (#[trigger] tile_part_payloads@[later]).tile_index as int != tile,
                                None => forall|prior: int| 0 <= prior < tile_part_payloads.len() ==>
                                    (#[trigger] tile_part_payloads@[prior]).tile_index as int != tile,
                            } by {
                                if tile != tile_index {
                                    assert(tile_component_style_parts@[tile] == previous_style_parts[tile]);
                                    match previous_style_parts[tile] {
                                        Some(part) => {
                                            assert(part < previous_payloads.len());
                                            assert(tile_part_payloads@[part as int] == previous_payloads[part as int]);
                                            assert forall|later: int| part < later < tile_part_payloads.len() implies
                                                (#[trigger] tile_part_payloads@[later]).tile_index as int != tile by {
                                                    if later < previous_payloads.len() {
                                                        assert(tile_part_payloads@[later] == previous_payloads[later]);
                                                        assert(previous_payloads[later].tile_index as int != tile);
                                                    } else {
                                                        assert(later == previous_payloads.len());
                                                        assert(tile_part_payloads@[later].tile_index as int == tile_index);
                                                    }
                                                }
                                        }
                                        None => {
                                            assert forall|prior: int| 0 <= prior < tile_part_payloads.len() implies
                                                (#[trigger] tile_part_payloads@[prior]).tile_index as int != tile by {
                                                    if prior < previous_payloads.len() {
                                                        assert(tile_part_payloads@[prior] == previous_payloads[prior]);
                                                        assert(previous_payloads[prior].tile_index as int != tile);
                                                    } else {
                                                        assert(prior == previous_payloads.len());
                                                        assert(tile_part_payloads@[prior].tile_index as int == tile_index);
                                                    }
                                                }
                                        }
                                    }
                                } else {
                                    assert(tile_component_style_parts@[tile] == Some(previous_payloads.len() as usize));
                                    assert(tile_part_payloads.len() == previous_payloads.len() + 1);
                                    assert(tile_part_payloads@[previous_payloads.len() as int].tile_index as int == tile);
                                }
                            }
                    }
                }
                EOC => {
                    if tile_parts == 0 {
                        return Err(parser.malformed_here(MalformedKind::InvalidMarkerOrder));
                    }
                    parser.expect_standalone(EOC)?;
                    if plm_seen && plm_groups.len() != tile_parts as usize {
                        return Err(parser.malformed_here(MalformedKind::InvalidPacketLength));
                    }
                    if ppm_fragments != 0 && ppm_frames.len() != tile_parts as usize {
                        return Err(parser.malformed_here(MalformedKind::InvalidPackedPacketHeader));
                    }
                    if !part2_extensions.tile_part_lengths.is_empty()
                        && part2_extensions.tile_part_lengths.len() != tile_parts as usize
                    {
                        return Err(parser.malformed_here(MalformedKind::InvalidTilePart));
                    }
                    if parser.position != parser.input.len() {
                        return Err(parser.malformed_here(MalformedKind::TrailingData));
                    }
                    break;
                }
                _ => return Err(parser.malformed_here(MalformedKind::InvalidMarkerOrder)),
            }
            if !crate::refinement::parser_progress(previous_position, parser.position, input_length)
            {
                return Err(parser.malformed_here(MalformedKind::InvalidTilePart));
            }
        }

        let codestream_profile = classify_codestream_profile(
            r_siz,
            extended_capabilities,
            profile,
            corresponding_profile,
            &component_coding_styles,
            &roi_shifts,
            &tile_part_payloads,
            image_size.components,
            roi_seen.iter().any(|seen| *seen),
        )?;
        Ok(CodestreamLayout {
            info: CodestreamInfo {
                image_size,
                coding_style,
                quantization,
                component_coding_styles,
                component_quantizations,
                roi_shifts,
                progression_changes,
                multiple_component_transform,
                part2_extensions,
                profile: codestream_profile,
                main_header_segments,
                tile_parts,
                consumed_bytes: parser.offset(parser.position),
            },
            tile_parts: tile_part_payloads,
        })
    }
}
