//! Coding, quantization, ROI and progression marker parsing.

use super::reader::read_u16;
use super::{
    CodingStyle, ComponentCodingStylePayload, ComponentCodingStyles, DecodeError,
    DecompositionDirection, MAX_COMPONENTS, MAX_QUANTIZATION_STEPS, MalformedKind, Parser,
    ProgressionChange, ProgressionChanges, ProgressionOrder, Quantization, QuantizationStep,
    QuantizationStyle, Resource, Segment, WaveletTransform,
};
#[cfg(verus_keep_ghost)]
use super::{
    component_coding_style_count, component_coding_style_payload_is_bounded,
    parsed_coding_style_outcome, parsed_coding_style_view, parsed_component_coding_style_outcome,
    parsed_component_coding_style_payload_outcome, parsed_component_quantization_outcome,
    parsed_progression_outcome, parsed_quantization_outcome, parser_view,
    progression_change_contains, progression_changes_view, segment_slots_view, segment_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl<'a> Parser<'a> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, segment_slots_view(final(segments)@), parser_view(self))
            == crate::specs::part1_record_component_segment(
                parser_view(self), segment_view(segment), components, invalid_kind,
                segment_slots_view(old(segments)@)),
    ))]
    pub(super) fn record_component_segment(
        &self,
        segment: Segment<'a>,
        components: u16,
        invalid_kind: MalformedKind,
        segments: &mut [Option<Segment<'a>>; MAX_COMPONENTS],
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_record_component_segment); }
        let (component, _) = self.parse_component_index(segment, components, invalid_kind)?;
        let index = usize::from(component);
        if index >= segments.len() {
            return Err(self.malformed_at(segment.offset, invalid_kind));
        }
        if segments[index].is_some() {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerOrder));
        }
        segments[index] = Some(segment);
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures parsed_coding_style_outcome(result) == crate::specs::part1_parse_cod(segment.offset, segment.payload@, self.limits),
    ))]
    pub(super) fn parse_cod(&self, segment: Segment<'a>) -> Result<CodingStyle, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_parse_cod); }
        let style = self.parse_cod_payload(segment.offset, segment.payload)?;
        self.validate_ordinary_precincts(segment.offset, style)?;
        Ok(style)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_validate_ordinary_precincts(
            segment_offset, style.decomposition_structure, style.precincts_defined,
            style.decomposition_levels, style.precinct_exponents@),
    ))]
    fn validate_ordinary_precincts(
        &self,
        segment_offset: usize,
        style: CodingStyle,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost goal = crate::specs::part1_validate_ordinary_precincts(
                segment_offset, style.decomposition_structure, style.precincts_defined,
                style.decomposition_levels, style.precinct_exponents@);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_validate_ordinary_precincts);
        }
        if style.decomposition_structure.is_some() || !style.precincts_defined {
            return Ok(());
        }
        let mut resolution = 1_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant 1 <= resolution,
                resolution <= style.decomposition_levels as nat + 1,
                goal == crate::specs::part1_validate_ordinary_precincts(
                    segment_offset, style.decomposition_structure, style.precincts_defined,
                    style.decomposition_levels, style.precinct_exponents@),
                goal == crate::specs::part1_ordinary_precincts_from(
                    segment_offset, style.decomposition_levels, style.precinct_exponents@, resolution),
            decreases style.decomposition_levels as int + 1 - resolution as int,
        ))]
        while resolution <= usize::from(style.decomposition_levels) {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_ordinary_precincts_from, 1);
            }
            if resolution >= style.precinct_exponents.len() {
                return Err(self.malformed_at(segment_offset, MalformedKind::InvalidCodingStyle));
            }
            let pair = style.precinct_exponents[resolution];
            if pair.0 == 0 || pair.1 == 0 {
                return Err(self.malformed_at(segment_offset, MalformedKind::InvalidCodingStyle));
            }
            resolution += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_ordinary_precincts_from, 1); }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures parsed_coding_style_outcome(result) == crate::specs::part1_parse_cod_payload(segment_offset, payload@, self.limits),
    ))]
    pub(super) fn parse_cod_payload(
        &self,
        segment_offset: usize,
        payload: &[u8],
    ) -> Result<CodingStyle, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_parse_cod_payload);
            reveal(crate::specs::part1_cod_header);
        }
        if payload.len() < 10 {
            return Err(self.malformed_at(segment_offset, MalformedKind::InvalidMarkerLength));
        }
        let flags = payload[0];
        if flags & 0xf8 != 0 {
            return Err(self.malformed_at(segment_offset, MalformedKind::InvalidCodingStyle));
        }
        let progression_order = match payload[1] {
            0 => ProgressionOrder::Lrcp,
            1 => ProgressionOrder::Rlcp,
            2 => ProgressionOrder::Rpcl,
            3 => ProgressionOrder::Pcrl,
            4 => ProgressionOrder::Cprl,
            _ => {
                return Err(self.malformed_at(segment_offset, MalformedKind::InvalidCodingStyle));
            }
        };
        let layers = read_u16([payload[2], payload[3]]);
        if layers == 0 || layers > self.limits.maximum_layers() {
            return Err(if layers > self.limits.maximum_layers() {
                DecodeError::LimitExceeded {
                    resource: Resource::Layers,
                    limit: u64::from(self.limits.maximum_layers()),
                    actual: u64::from(layers),
                }
            } else {
                self.malformed_at(segment_offset, MalformedKind::InvalidCodingStyle)
            });
        }
        let multiple_component_transform = match payload[4] {
            0 => false,
            1 => true,
            _ => {
                return Err(self.malformed_at(segment_offset, MalformedKind::InvalidCodingStyle));
            }
        };
        let decomposition_levels = payload[5];
        let resolution_levels = match decomposition_levels.checked_add(1) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment_offset, MalformedKind::ArithmeticOverflow));
            }
        };
        if resolution_levels > self.limits.maximum_resolutions_per_component() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::Resolutions,
                limit: u64::from(self.limits.maximum_resolutions_per_component()),
                actual: u64::from(resolution_levels),
            });
        }
        let width_exponent = payload[6];
        let height_exponent = payload[7];
        if width_exponent > 8 || height_exponent > 8 {
            return Err(self.malformed_at(segment_offset, MalformedKind::InvalidCodingStyle));
        }
        let code_block_width = 1_u16 << (u32::from(width_exponent) + 2);
        let code_block_height = 1_u16 << (u32::from(height_exponent) + 2);
        let code_block_samples = match u32::from(code_block_width)
            .checked_mul(u32::from(code_block_height))
        {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment_offset, MalformedKind::ArithmeticOverflow));
            }
        };
        if code_block_samples > 4096
            || crate::tier1::tier1_block_coding_from_code_block_style(payload[8]).is_err()
        {
            return Err(self.malformed_at(segment_offset, MalformedKind::InvalidCodingStyle));
        }
        let transform = match payload[9] {
            0 => WaveletTransform::Irreversible9x7,
            1 => WaveletTransform::Reversible5x3,
            index => WaveletTransform::Arbitrary(index),
        };
        let precincts_defined = flags & 1 != 0;
        let precinct_count = usize::from(resolution_levels);
        let expected_length = if precincts_defined {
            match 10_usize.checked_add(precinct_count) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment_offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            }
        } else {
            10
        };
        if payload.len() != expected_length {
            return Err(self.malformed_at(segment_offset, MalformedKind::InvalidMarkerLength));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost h = crate::specs::Part1CodHeader {
                flags, progression_order, layers, multiple_component_transform, decomposition_levels,
                code_block_width, code_block_height, code_block_style: payload@[8], transform, precinct_count,
            };
            let ghost initial_precincts = Seq::new(33, |i: int| (15u8, 15u8));
            let ghost precinct_goal = if precincts_defined {
                crate::specs::part1_cod_precincts(segment_offset, payload@, precinct_count, 0, initial_precincts)
            } else { Ok(initial_precincts) };
            let ghost goal = crate::specs::part1_parse_cod_payload(segment_offset, payload@, self.limits);
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(crate::specs::part1_cod_header(segment_offset, payload@, self.limits) == Ok(h)); }
        let mut precinct_exponents = [(15_u8, 15_u8); 33];
        #[cfg(verus_keep_ghost)]
        proof! { assert(precinct_exponents@ =~= initial_precincts); }
        if precincts_defined {
            let mut resolution = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant resolution <= precinct_count,
                    payload.len() as int == 10 + precinct_count as int,
                    precincts_defined,
                    flags & 1 != 0,
                    h == (crate::specs::Part1CodHeader {
                        flags, progression_order, layers, multiple_component_transform, decomposition_levels,
                        code_block_width, code_block_height, code_block_style: payload@[8], transform, precinct_count,
                    }),
                    goal == crate::specs::part1_parse_cod_payload(segment_offset, payload@, self.limits),
                    goal == match precinct_goal { Err(error) => Err(error), Ok(values) => Ok(crate::specs::part1_cod_from_header(h, values)) },
                    precinct_goal == crate::specs::part1_cod_precincts(
                        segment_offset, payload@, precinct_count, resolution, precinct_exponents@,
                    ),
                    decreases precinct_count - resolution,
                )
            )]
            while resolution < precinct_count {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part1_parse_cod_payload);
                    reveal_with_fuel(crate::specs::part1_cod_precincts, 1);
                }
                let index = match 10_usize.checked_add(resolution) {
                    Some(value) => value,
                    None => {
                        return Err(
                            self.malformed_at(segment_offset, MalformedKind::ArithmeticOverflow)
                        );
                    }
                };
                if index >= payload.len() || resolution >= precinct_exponents.len() {
                    return Err(
                        self.malformed_at(segment_offset, MalformedKind::InvalidCodingStyle)
                    );
                }
                precinct_exponents[resolution] = (payload[index] & 0x0f, payload[index] >> 4);
                resolution = match resolution.checked_add(1) {
                    Some(value) => value,
                    None => {
                        return Err(
                            self.malformed_at(segment_offset, MalformedKind::ArithmeticOverflow)
                        );
                    }
                };
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_cod_precincts, 1); }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_parse_cod_payload);
            assert(precinct_goal == Ok(precinct_exponents@));
            assert(goal == Ok(crate::specs::part1_cod_from_header(h, precinct_exponents@)));
        }
        let style = CodingStyle {
            progression_order,
            layers,
            multiple_component_transform,
            decomposition_levels,
            decomposition_structure: None,
            decomposition_directions: [DecompositionDirection::TwoDimensional; 32],
            code_block_width,
            code_block_height,
            code_block_style: payload[8],
            transform,
            precincts_defined,
            sop_markers: flags & 2 != 0,
            eph_markers: flags & 4 != 0,
            precinct_exponents,
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(style.decomposition_directions@ =~= Seq::new(32, |i: int| DecompositionDirection::TwoDimensional));
            assert(goal == Ok(parsed_coding_style_view(style)));
        }
        Ok(style)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_parse_component_index(segment.offset, segment.payload@, components, invalid_kind),
    ))]
    pub(super) fn parse_component_index(
        &self,
        segment: Segment<'a>,
        components: u16,
        invalid_kind: MalformedKind,
    ) -> Result<(u16, usize), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_parse_component_index); }
        let component_bytes = if components < 257 { 1_usize } else { 2_usize };
        if segment.payload.len() < component_bytes {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let component = if component_bytes == 1 {
            u16::from(segment.payload[0])
        } else {
            read_u16([segment.payload[0], segment.payload[1]])
        };
        if component >= components {
            return Err(self.malformed_at(segment.offset, invalid_kind));
        }
        Ok((component, component_bytes))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures parsed_progression_outcome(result) == crate::specs::part1_parse_poc(segment_view(segment), components),
    ))]
    pub(super) fn parse_poc(
        &self,
        segment: Segment<'a>,
        components: u16,
    ) -> Result<ProgressionChanges, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_parse_poc); }
        let component_bytes = if components < 257 { 1_usize } else { 2_usize };
        let doubled = match component_bytes.checked_mul(2) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        let record_bytes = match doubled.checked_add(5) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        let remainder = segment.payload.len() % record_bytes;
        if segment.payload.is_empty() || remainder != 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let mut records = Vec::with_capacity(segment.payload.len() / record_bytes);
        let mut position = 0_usize;
        let mut remaining_records = segment.payload.len() / record_bytes;
        #[cfg(verus_keep_ghost)]
        proof! {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(segment.payload.len() as int, record_bytes as int);
            assert((record_bytes as int) * (remaining_records as int) ==
                (remaining_records as int) * (record_bytes as int)) by (nonlinear_arith);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant position <= segment.payload.len(),
                    component_bytes == if components < 257 { 1usize } else { 2usize },
                    record_bytes == 2 * component_bytes + 5,
                    record_bytes == 7 || record_bytes == 9,
                    position + remaining_records as int * record_bytes as int == segment.payload.len(),
                    crate::specs::part1_parse_poc(segment_view(segment), components)
                        == crate::specs::part1_poc_records(segment_view(segment), components, position as nat, records@),
                decreases remaining_records,
            )
        )]
        while position < segment.payload.len() {
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost record_start = position; }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_records, 1);
                reveal(crate::specs::part1_poc_byte); reveal(crate::specs::part1_poc_component);
                assert(record_bytes > 0 && position + remaining_records as int * record_bytes as int == segment.payload.len()
                    && position < segment.payload.len() ==> remaining_records > 0
                        && position + record_bytes <= segment.payload.len()) by (nonlinear_arith);
                assert(remaining_records > 0);
                assert(position + record_bytes <= segment.payload.len());
            }
            if remaining_records == 0 {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
            }
            remaining_records -= 1;
            let resolution_start = self.read_poc_byte(segment, position)?;
            position = match position.checked_add(1) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
            let component_start = self.read_poc_component(segment, position, component_bytes)?;
            position = match position.checked_add(component_bytes) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
            let layer_end_position = match position.checked_add(2) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
            let layer_bytes = match segment.payload.get(position..layer_end_position) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength)
                    );
                }
            };
            let layer_end = read_u16([layer_bytes[0], layer_bytes[1]]);
            position = match position.checked_add(2) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
            let resolution_end = self.read_poc_byte(segment, position)?;
            position = match position.checked_add(1) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
            let encoded_component_end =
                self.read_poc_component(segment, position, component_bytes)?;
            let component_end =
                if component_bytes == 1 && encoded_component_end == 0 && components == 256 {
                    256
                } else {
                    encoded_component_end
                };
            position = match position.checked_add(component_bytes) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
            let progression_order = match self.read_poc_byte(segment, position)? {
                0 => ProgressionOrder::Lrcp,
                1 => ProgressionOrder::Rlcp,
                2 => ProgressionOrder::Rpcl,
                3 => ProgressionOrder::Pcrl,
                4 => ProgressionOrder::Cprl,
                _ => {
                    return Err(self.malformed_at(
                        segment.offset,
                        MalformedKind::InvalidProgressionOrderChange,
                    ));
                }
            };
            position = match position.checked_add(1) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
            records.push(ProgressionChange {
                resolution_start,
                component_start,
                layer_end,
                resolution_end,
                component_end,
                progression_order,
            });
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(position == record_start + record_bytes);
                assert((remaining_records as int + 1) * (record_bytes as int) ==
                    (remaining_records as int) * (record_bytes as int) + record_bytes as int) by (nonlinear_arith);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_poc_records, 1); reveal(progression_changes_view); }
        Ok(ProgressionChanges { records })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_poc_component(segment_view(segment), position, width),
    ))]
    pub(super) fn read_poc_component(
        &self,
        segment: Segment<'a>,
        position: usize,
        width: usize,
    ) -> Result<u16, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_poc_component); }
        if width == 1 {
            let value = match segment.payload.get(position) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength)
                    );
                }
            };
            return Ok(*value as u16);
        }
        let end = match position.checked_add(2) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        let bytes = match segment.payload.get(position..end) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
            }
        };
        Ok(read_u16([bytes[0], bytes[1]]))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_poc_byte(segment_view(segment), position),
    ))]
    pub(super) fn read_poc_byte(
        &self,
        segment: Segment<'a>,
        position: usize,
    ) -> Result<u8, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_poc_byte); }
        let value = match segment.payload.get(position) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
            }
        };
        Ok(*value)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_validate_progression_changes(
            offset, progression_changes_view(changes), layers, component_styles, self.limits),
    ))]
    pub(super) fn validate_progression_changes(
        &self,
        changes: &ProgressionChanges,
        layers: u16,
        component_styles: &ComponentCodingStyles,
        offset: usize,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_validate_progression_changes); }
        if changes.is_empty() {
            return Ok(());
        }
        let components = component_styles.components;
        let (active_coordinates, maximum_resolutions) =
            self.progression_validation_shape(layers, component_styles, offset)?;
        let validation_work =
            match (changes.records.len() as u64).checked_mul(active_coordinates as u64) {
                Some(value) => value,
                None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
            };
        if validation_work > self.limits.maximum_work_units() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: self.limits.maximum_work_units(),
                actual: validation_work,
            });
        }
        let mut owners = vec![false; active_coordinates];
        #[cfg(verus_keep_ghost)]
        proof! { assert(owners@ =~= Seq::new(active_coordinates as nat, |index: int| false)); }
        let mut record_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant record_index <= changes.records.len(),
                    components == component_coding_style_count(component_styles),
                    crate::specs::part1_validate_progression_changes(
                        offset, progression_changes_view(changes), layers, component_styles, self.limits)
                        == crate::specs::part1_poc_admit_records(offset, progression_changes_view(changes),
                            layers, component_styles, maximum_resolutions, record_index as nat, owners@),
                decreases changes.records.len() - record_index,
            )
        )]
        while record_index < changes.records.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_poc_admit_records, 1); }
            let record = changes.records[record_index];
            if record.layer_end == 0
                || record.layer_end > layers
                || record.component_start >= record.component_end
                || record.component_end > components
                || record.resolution_start >= record.resolution_end
                || record.resolution_end > maximum_resolutions
            {
                return Err(self.malformed_at(offset, MalformedKind::InvalidProgressionOrderChange));
            }
            let contributed = self.mark_progression_record(
                record,
                layers,
                component_styles,
                &mut owners,
                offset,
            )?;
            if !contributed {
                return Err(self.malformed_at(offset, MalformedKind::InvalidProgressionOrderChange));
            }
            record_index = match record_index.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_poc_admit_records, 1); }
        if !progression_owners_complete(&owners) {
            return Err(self.malformed_at(offset, MalformedKind::InvalidProgressionOrderChange));
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_poc_validation_shape(offset, layers, component_styles, 0, 0, 0),
    ))]
    pub(super) fn progression_validation_shape(
        &self,
        layers: u16,
        component_styles: &ComponentCodingStyles,
        offset: usize,
    ) -> Result<(usize, u8), DecodeError> {
        let components = component_styles.components;
        let mut active_coordinates = 0_usize;
        let mut maximum_resolutions = 0_u8;
        let mut component = 0_u16;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant component <= components,
                components == component_coding_style_count(component_styles),
                crate::specs::part1_poc_validation_shape(offset, layers, component_styles, 0, 0, 0)
                    == crate::specs::part1_poc_validation_shape(offset, layers, component_styles,
                        component, active_coordinates, maximum_resolutions),
            decreases components - component,
        ))]
        while component < components {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_poc_validation_shape, 1); }
            let depth = component_styles.style(component)?.decomposition_levels;
            let resolutions = match depth.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
            };
            if resolutions > maximum_resolutions {
                maximum_resolutions = resolutions;
            }
            let amount = match usize::from(layers).checked_mul(usize::from(resolutions)) {
                Some(value) => value,
                None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
            };
            active_coordinates = match active_coordinates.checked_add(amount) {
                Some(value) => value,
                None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
            };
            component = match component.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_poc_validation_shape, 1); }
        Ok((active_coordinates, maximum_resolutions))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, final(owners)@) == crate::specs::part1_poc_mark_resolutions(
            offset, record, coordinate, 0, old(owners)@, progress),
    ))]
    pub(super) fn mark_progression_resolutions(
        &self,
        record: ProgressionChange,
        coordinate: (u16, u16, u8),
        owners: &mut [bool],
        progress: (usize, bool),
        offset: usize,
    ) -> Result<(usize, bool), DecodeError> {
        let mut linear = progress.0;
        let mut contributed = progress.1;
        let mut resolution = 0_u8;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input = owners@;
            let ghost goal = crate::specs::part1_poc_mark_resolutions(offset, record, coordinate, 0, input, progress);
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant resolution <= coordinate.2, input == old(owners)@,
                goal == crate::specs::part1_poc_mark_resolutions(offset, record, coordinate, 0, input, progress),
                goal == crate::specs::part1_poc_mark_resolutions(offset, record, coordinate, resolution, owners@, (linear, contributed)),
            decreases coordinate.2 - resolution,
        ))]
        while resolution < coordinate.2 {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_poc_mark_resolutions, 1); }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before = owners@; }
            if record.contains(coordinate.1, resolution, coordinate.0) {
                let owner = match owners.get_mut(linear) {
                    Some(value) => value,
                    None => {
                        return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow));
                    }
                };
                if !*owner {
                    *owner = true;
                    contributed = true;
                }
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                let fresh = progression_change_contains(record, coordinate.1, resolution, coordinate.0)
                    && !before[linear as int];
                assert(owners@ =~= if fresh { before.update(linear as int, true) } else { before });
            }
            linear = match linear.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
            };
            resolution = match resolution.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_poc_mark_resolutions, 1); }
        Ok((linear, contributed))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, final(owners)@) == crate::specs::part1_poc_mark_layers(
            offset, record, coordinate, layers, 0, old(owners)@, progress),
    ))]
    pub(super) fn mark_progression_layers(
        &self,
        record: ProgressionChange,
        coordinate: (u16, u8),
        owners: &mut [bool],
        progress: (usize, bool),
        layers: u16,
        offset: usize,
    ) -> Result<(usize, bool), DecodeError> {
        let mut linear = progress.0;
        let mut contributed = progress.1;
        let mut layer = 0_u16;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input = owners@;
            let ghost goal = crate::specs::part1_poc_mark_layers(offset, record, coordinate, layers, 0, input, progress);
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant layer <= layers, input == old(owners)@,
                goal == crate::specs::part1_poc_mark_layers(offset, record, coordinate, layers, 0, input, progress),
                goal == crate::specs::part1_poc_mark_layers(offset, record, coordinate, layers, layer, owners@, (linear, contributed)),
            decreases layers - layer,
        ))]
        while layer < layers {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_poc_mark_layers, 1); }
            let next = self.mark_progression_resolutions(
                record,
                (coordinate.0, layer, coordinate.1),
                owners,
                (linear, contributed),
                offset,
            )?;
            linear = next.0;
            contributed = next.1;
            layer = match layer.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_poc_mark_layers, 1); }
        Ok((linear, contributed))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, final(owners)@) == crate::specs::part1_poc_mark_record(
            offset, record, layers, component_styles, old(owners)@),
    ))]
    pub(super) fn mark_progression_record(
        &self,
        record: ProgressionChange,
        layers: u16,
        component_styles: &ComponentCodingStyles,
        owners: &mut [bool],
        offset: usize,
    ) -> Result<bool, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_poc_mark_record); }
        let components = component_styles.components;
        let mut linear = 0_usize;
        let mut contributed = false;
        let mut component = 0_u16;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input = owners@;
            let ghost goal = crate::specs::part1_poc_mark_components(offset, record, layers, component_styles, 0, input, (0, false));
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant component <= components, components == component_coding_style_count(component_styles),
                input == old(owners)@,
                goal == crate::specs::part1_poc_mark_components(offset, record, layers, component_styles, 0, input, (0, false)),
                goal == crate::specs::part1_poc_mark_components(offset, record, layers, component_styles, component, owners@, (linear, contributed)),
            decreases components - component,
        ))]
        while component < components {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_poc_mark_components, 1); }
            let depth = component_styles.style(component)?.decomposition_levels;
            let resolutions = match depth.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
            };
            let next = self.mark_progression_layers(
                record,
                (component, resolutions),
                owners,
                (linear, contributed),
                layers,
                offset,
            )?;
            linear = next.0;
            contributed = next.1;
            component = match component.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_poc_mark_components, 1); }
        Ok(contributed)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures parsed_component_coding_style_outcome(result) == crate::specs::part1_parse_coc(
            segment.offset, segment.payload@, components, parsed_coding_style_view(default), self.limits),
    ))]
    pub(super) fn parse_coc(
        &self,
        segment: Segment<'a>,
        components: u16,
        default: CodingStyle,
    ) -> Result<(u16, CodingStyle), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_parse_coc); }
        let prepared = self.prepare_coc_payload(segment, components, default)?;
        let mut style =
            self.parse_cod_payload(segment.offset, &prepared.payload[..prepared.length])?;
        style.decomposition_structure = prepared.decomposition_structure;
        self.validate_ordinary_precincts(segment.offset, style)?;
        Ok((prepared.component, style))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures parsed_component_coding_style_payload_outcome(result) == crate::specs::part1_coc_prepare(
            segment.offset, segment.payload@, components, parsed_coding_style_view(default)),
        component_coding_style_payload_is_bounded(result),
    ))]
    fn prepare_coc_payload(
        &self,
        segment: Segment<'a>,
        components: u16,
        default: CodingStyle,
    ) -> Result<ComponentCodingStylePayload, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_coc_prepare);
            reveal(crate::specs::part1_parse_component_index);
        }
        let (component, component_bytes) =
            self.parse_component_index(segment, components, MalformedKind::InvalidCodingStyle)?;
        let minimum = component_bytes
            .checked_add(6)
            .ok_or_else(|| self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow))?;
        if segment.payload.len() < minimum {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let scoc = segment.payload[component_bytes];
        if scoc & 0xfe != 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidCodingStyle));
        }
        let parameters = segment
            .payload
            .get(component_bytes + 1..)
            .ok_or_else(|| self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength))?;
        let decomposition_structure = if parameters[0] & 0x80 != 0 {
            let index = parameters[0] & 0x7f;
            if index == 0 {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidCodingStyle));
            }
            Some(index)
        } else {
            None
        };
        let mut cod_payload = [0_u8; 43];
        cod_payload[0] = (scoc & 1)
            | if default.sop_markers { 2 } else { 0 }
            | if default.eph_markers { 4 } else { 0 };
        cod_payload[1] = match default.progression_order {
            ProgressionOrder::Lrcp => 0,
            ProgressionOrder::Rlcp => 1,
            ProgressionOrder::Rpcl => 2,
            ProgressionOrder::Pcrl => 3,
            ProgressionOrder::Cprl => 4,
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let layers = default.layers;
            assert(layers >> 8 <= 255) by (bit_vector);
            assert(layers & 0xff <= 255) by (bit_vector);
        }
        cod_payload[2] = u8::try_from(default.layers >> 8)
            .map_err(|_| self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow))?;
        cod_payload[3] = u8::try_from(default.layers & 0xff)
            .map_err(|_| self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow))?;
        cod_payload[4] = if default.multiple_component_transform {
            1
        } else {
            0
        };
        let end = match 5_usize.checked_add(parameters.len()) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        if end > cod_payload.len() {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before_parameters = cod_payload@; }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(cod_payload@[0] == (scoc & 1) | (if default.sop_markers { 2u8 } else { 0u8 }) | (if default.eph_markers { 4u8 } else { 0u8 }));
            assert(cod_payload@[1] == crate::specs::part1_cod_progression_byte(default.progression_order));
            assert(cod_payload@[2] == (default.layers >> 8) as u8);
            assert(cod_payload@[3] == (default.layers & 255) as u8);
            assert(cod_payload@[4] == if default.multiple_component_transform { 1u8 } else { 0u8 });
        }
        cod_payload[5..end].copy_from_slice(parameters);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(cod_payload@.subrange(0, 5) =~= before_parameters.subrange(0, 5));
            assert(cod_payload@.subrange(5, end as int) =~= parameters@);
        }
        if decomposition_structure.is_some() {
            cod_payload[5] = default.decomposition_levels;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(cod_payload@.subrange(0, end as int) =~= crate::specs::part1_coc_cod_payload(
                parameters@, scoc, parsed_coding_style_view(default), decomposition_structure));
        }
        Ok(ComponentCodingStylePayload {
            component,
            payload: cod_payload,
            length: end,
            decomposition_structure,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures parsed_quantization_outcome(result) == crate::specs::part1_parse_qcd_payload(
            segment.offset, segment.payload@, parsed_coding_style_view(coding_style)),
    ))]
    pub(super) fn parse_qcd(
        &self,
        segment: Segment<'a>,
        coding_style: CodingStyle,
    ) -> Result<Quantization, DecodeError> {
        self.parse_qcd_payload(segment.offset, segment.payload, coding_style)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures parsed_quantization_outcome(result) == crate::specs::part1_parse_qcd_payload(
            segment_offset, payload@, parsed_coding_style_view(coding_style)),
    ))]
    pub(super) fn parse_qcd_payload(
        &self,
        segment_offset: usize,
        payload: &[u8],
        coding_style: CodingStyle,
    ) -> Result<Quantization, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_parse_qcd_payload);
            reveal(crate::specs::part1_qcd_header);
        }
        if payload.is_empty() {
            return Err(self.malformed_at(segment_offset, MalformedKind::InvalidMarkerLength));
        }

        let guard_bits = payload[0] >> 5;
        let style = match payload[0] & 0x1f {
            0 => QuantizationStyle::None,
            1 => QuantizationStyle::ScalarDerived,
            2 => QuantizationStyle::ScalarExpounded,
            _ => {
                return Err(self.malformed_at(segment_offset, MalformedKind::InvalidQuantization));
            }
        };
        let subband_count = coding_style.subband_count();
        let step_bytes = payload.len() - 1;
        let expected_step_bytes = match style {
            QuantizationStyle::None => usize::from(subband_count),
            QuantizationStyle::ScalarDerived => 2,
            QuantizationStyle::ScalarExpounded => match usize::from(subband_count).checked_mul(2) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment_offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            },
        };
        if step_bytes != expected_step_bytes {
            return Err(self.malformed_at(segment_offset, MalformedKind::InvalidMarkerLength));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost h = crate::specs::Part1QcdHeader { style, guard_bits, subband_count };
            let ghost goal = crate::specs::part1_parse_qcd_payload(
                segment_offset, payload@, parsed_coding_style_view(coding_style));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_qcd_header(segment_offset, payload@, parsed_coding_style_view(coding_style)) == Ok(h));
        }
        if matches!(style, QuantizationStyle::None) {
            let mut index = 1_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant
                        1 <= index <= payload.len(),
                        style == QuantizationStyle::None,
                        h == (crate::specs::Part1QcdHeader { style, guard_bits, subband_count }),
                        goal == crate::specs::part1_parse_qcd_payload(
                            segment_offset, payload@, parsed_coding_style_view(coding_style)),
                        goal == match crate::specs::part1_qcd_validate_unscaled(segment_offset, payload@, index) {
                            Err(error) => Err(error),
                            Ok(()) => crate::specs::part1_qcd_after_validation(segment_offset, payload@, h),
                        },
                    decreases payload.len() - index,
                )
            )]
            while index < payload.len() {
                #[cfg(verus_keep_ghost)]
                proof! { reveal_with_fuel(crate::specs::part1_qcd_validate_unscaled, 1); }
                if payload[index] & 0x07 != 0 {
                    return Err(
                        self.malformed_at(segment_offset, MalformedKind::InvalidQuantization)
                    );
                }
                index = match index.checked_add(1) {
                    Some(value) => value,
                    None => {
                        return Err(
                            self.malformed_at(segment_offset, MalformedKind::ArithmeticOverflow)
                        );
                    }
                };
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_qcd_validate_unscaled, 1); }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(goal == crate::specs::part1_qcd_after_validation(segment_offset, payload@, h));
            reveal(crate::specs::part1_qcd_after_validation);
        }
        let step_count = match style {
            QuantizationStyle::None | QuantizationStyle::ScalarExpounded => subband_count,
            QuantizationStyle::ScalarDerived => 1,
        };
        if usize::from(step_count) > MAX_QUANTIZATION_STEPS {
            return Err(self.malformed_at(segment_offset, MalformedKind::InvalidQuantization));
        }
        let mut steps = [QuantizationStep {
            exponent: 0,
            mantissa: 0,
        }; MAX_QUANTIZATION_STEPS];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(steps@ =~= Seq::new(97, |i: int| QuantizationStep { exponent: 0, mantissa: 0 }));
        }
        let step_total = usize::from(step_count);
        let mut step_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    step_index <= step_total <= MAX_QUANTIZATION_STEPS,
                    step_total == step_count as usize,
                    goal == crate::specs::part1_parse_qcd_payload(
                        segment_offset, payload@, parsed_coding_style_view(coding_style)),
                    goal == match crate::specs::part1_qcd_steps(
                        segment_offset, payload@, style, step_total, step_index, steps@) {
                        Err(error) => Err(error),
                        Ok(values) => Ok((style, guard_bits, step_count, values)),
                    },
                decreases step_total - step_index,
            )
        )]
        while step_index < step_total {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_qcd_steps, 1);
                reveal(crate::specs::part1_qcd_step);
            }
            let payload_index =
                if matches!(style, QuantizationStyle::None) {
                    match step_index.checked_add(1) {
                        Some(value) => value,
                        None => {
                            return Err(self
                                .malformed_at(segment_offset, MalformedKind::ArithmeticOverflow));
                        }
                    }
                } else {
                    let doubled = match step_index.checked_mul(2) {
                        Some(value) => value,
                        None => {
                            return Err(self
                                .malformed_at(segment_offset, MalformedKind::ArithmeticOverflow));
                        }
                    };
                    match doubled.checked_add(1) {
                        Some(value) => value,
                        None => {
                            return Err(self
                                .malformed_at(segment_offset, MalformedKind::ArithmeticOverflow));
                        }
                    }
                };
            let step = if matches!(style, QuantizationStyle::None) {
                if payload_index >= payload.len() {
                    return Err(
                        self.malformed_at(segment_offset, MalformedKind::InvalidQuantization)
                    );
                }
                QuantizationStep {
                    exponent: payload[payload_index] >> 3,
                    mantissa: 0,
                }
            } else {
                let next_index = match payload_index.checked_add(1) {
                    Some(value) => value,
                    None => {
                        return Err(
                            self.malformed_at(segment_offset, MalformedKind::ArithmeticOverflow)
                        );
                    }
                };
                if next_index >= payload.len() {
                    return Err(
                        self.malformed_at(segment_offset, MalformedKind::InvalidQuantization)
                    );
                }
                let encoded = read_u16([payload[payload_index], payload[next_index]]);
                #[cfg(verus_keep_ghost)]
                proof! { assert(encoded >> 11 <= 255) by (bit_vector); }
                QuantizationStep {
                    exponent: u8::try_from(encoded >> 11).map_err(|_| {
                        self.malformed_at(segment_offset, MalformedKind::ArithmeticOverflow)
                    })?,
                    mantissa: encoded & 0x07ff,
                }
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::part1_qcd_step(segment_offset, payload@, style, step_index) == Ok(step));
            }
            if step_index >= steps.len() {
                return Err(self.malformed_at(segment_offset, MalformedKind::InvalidQuantization));
            }
            steps[step_index] = step;
            step_index = match step_index.checked_add(1) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment_offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_qcd_steps, 1); }
        Ok(Quantization {
            style,
            guard_bits,
            step_count,
            steps,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures parsed_component_quantization_outcome(result) == crate::specs::part1_parse_qcc(
            segment.offset, segment.payload@, components, parsed_coding_style_view(coding_style)),
    ))]
    pub(super) fn parse_qcc(
        &self,
        segment: Segment<'a>,
        components: u16,
        coding_style: CodingStyle,
    ) -> Result<(u16, Quantization), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_parse_qcc);
            reveal(crate::specs::part1_parse_component_index);
        }
        let (component, component_bytes) =
            self.parse_component_index(segment, components, MalformedKind::InvalidQuantization)?;
        let payload = segment
            .payload
            .get(component_bytes..)
            .ok_or_else(|| self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength))?;
        let quantization = self.parse_qcd_payload(segment.offset, payload, coding_style)?;
        Ok((component, quantization))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_parse_rgn(segment.offset, segment.payload@, components),
    ))]
    pub(super) fn parse_rgn(
        &self,
        segment: Segment<'a>,
        components: u16,
    ) -> Result<(u16, u8), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_parse_rgn); }
        let component_bytes = if components < 257 { 1_usize } else { 2_usize };
        let expected_length = match component_bytes.checked_add(2) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        if segment.payload.len() != expected_length {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let component = if component_bytes == 1 {
            u16::from(segment.payload[0])
        } else {
            read_u16([segment.payload[0], segment.payload[1]])
        };
        let style_index = component_bytes;
        let shift_index = match component_bytes.checked_add(1) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        if component >= components
            || style_index >= segment.payload.len()
            || shift_index >= segment.payload.len()
            || segment.payload[style_index] != 0
        {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidRegionOfInterest));
        }
        Ok((component, segment.payload[shift_index]))
    }
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_progression_owners_complete(owners@),
))]
pub(super) fn progression_owners_complete(owners: &[bool]) -> bool {
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= owners.len(),
            forall|index: int| 0 <= index < position ==> owners@[index],
        decreases owners.len() - position,
    ))]
    while position < owners.len() {
        if !owners[position] {
            return false;
        }
        position += 1;
    }
    true
}
