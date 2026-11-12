//! MCT registry validation and executable transform resolution.

use super::mct::mct_array_kinds_equal;
use super::{
    DecodeError, MalformedKind, MctArray, MctArrayKind, MctCollection, MctCollectionKind,
    MctCollectionReference, MctCollectionReferenceTransform, MctParameters, MctRecord, MctStage,
    MctWaveletType, MultipleComponentTransform, Parser,
};
#[cfg(verus_keep_ghost)]
use super::{
    mcc_collection_reference_view, mcc_collection_references_view, mcc_reference_transform_view,
    mct_array_reference_outcome, mct_array_view, mct_arrays_view, mct_collection_outcome,
    mct_collection_view, mct_collections_view, mct_graph_outcome, mct_parameters_view,
    mct_record_view, mct_records_view, mct_stage_outcome, mct_stage_view, mct_stages_view,
    mct_wavelet_view, multiple_component_transform_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_reversible_mct_scale(value, signed),
))]
pub(crate) fn reversible_mct_scale(value: i64, signed: bool) -> Result<i128, DecodeError> {
    if value == 0 || (value < 0 && !signed) {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidTransform));
    }
    let magnitude = if value < 0 {
        -i128::from(value)
    } else {
        i128::from(value)
    };
    let mut remaining = magnitude;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant remaining > 0,
            magnitude > 0,
            value != 0,
            signed || value > 0,
            magnitude == if value < 0 { -(value as int) } else { value as int },
            crate::specs::part2_mct_power_of_two(magnitude as int)
                == crate::specs::part2_mct_power_of_two(remaining as int),
        decreases remaining,
    ))]
    while remaining > 1 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_mct_power_of_two, 2); }
        if remaining % 2 != 0 {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidTransform));
        }
        remaining /= 2;
    }
    Ok(magnitude)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_validate_reversible_mct_coefficients(values@, count),
))]
pub(crate) fn validate_reversible_mct_coefficients(
    values: &[i64],
    count: usize,
) -> Result<(), DecodeError> {
    if count == 0 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidTransform));
    }
    let stages = match count.checked_add(1) {
        Some(value) => value,
        None => return Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)),
    };
    let expected = match count.checked_mul(stages) {
        Some(value) => value,
        None => return Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)),
    };
    if values.len() != expected {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidTransform));
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_mct_scale_empty(values@, count); }
    let mut stage = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant stage <= stages,
            count > 0,
            stages as int == count as int + 1,
            expected as int == count as int * stages as int,
            values@.len() == expected,
            crate::specs::part2_mct_scale_prefix(values@, count, stage as nat) == Ok(()),
        decreases stages - stage,
    ))]
    while stage < stages {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_scale_step(values@, count, stage as nat);
            crate::proofs::production_impl::production_mct_scale_error(values@, count, stage as nat + 1, stages as nat);
        }
        let target = if stage == count {
            count - 1
        } else {
            count - 1 - stage
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(target < count);
            assert((stage as int) * (count as int) + (target as int) < (expected as int)) by (nonlinear_arith)
                requires stage < stages, target < count, count > 0,
                    expected as int == count as int * stages as int;
        }
        let start = stage
            .checked_mul(count)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let index = start
            .checked_add(target)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        reversible_mct_scale(
            *values
                .get(index)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidTransform))?,
            stage == count,
        )?;
        stage += 1;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_byte_list_contains(values@, value),
))]
pub(super) fn u8_list_contains(values: &[u8], value: u8) -> bool {
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= values.len(),
            forall|index: int| 0 <= index < position ==> values@[index] != value,
        decreases values.len() - position,
    ))]
    while position < values.len() {
        if values[position] == value {
            return true;
        }
        position += 1;
    }
    false
}
impl<'a> Parser<'a> {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures mct_graph_outcome(result) == crate::specs::part1_mct_graph(mct_parameters_view(parameters)),
    ))]
    pub(super) fn resolve_multiple_component_transform(
        &self,
        parameters: &MctParameters,
    ) -> Result<Option<MultipleComponentTransform>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost goal = crate::specs::part1_mct_graph(mct_parameters_view(parameters)); }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_mct_graph); reveal(mct_parameters_view); }
        if parameters.order.is_empty() {
            return Ok(None);
        }
        let mut stages = Vec::with_capacity(parameters.order.len());
        #[cfg(verus_keep_ghost)]
        proof! { assert(mct_stages_view(stages@) =~= Seq::empty()); }
        let mut order_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant order_index <= parameters.order.len(),
                    goal == crate::specs::part1_mct_graph(mct_parameters_view(parameters)),
                    goal == crate::specs::part1_mct_graph_from(
                        mct_parameters_view(parameters), order_index as nat, mct_stages_view(stages@)),
                decreases parameters.order.len() - order_index,
            )
        )]
        while order_index < parameters.order.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_mct_graph_from, 1); reveal(mct_parameters_view); }
            let record_index = parameters.order[order_index];
            let position = match find_mct_record_index(&parameters.records, record_index) {
                Some(position) => position,
                None => return Err(self.malformed_at(0, MalformedKind::InvalidTransform)),
            };
            let stage =
                self.resolve_mct_stage(&parameters.records[position], &parameters.arrays)?;
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before = mct_stages_view(stages@); let ghost value = mct_stage_view(&stage); }
            stages.push(stage);
            #[cfg(verus_keep_ghost)]
            proof! { assert(mct_stages_view(stages@) =~= before.push(value)); }
            order_index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_mct_graph_from, 1); }
        let graph = MultipleComponentTransform { stages };
        #[cfg(verus_keep_ghost)]
        proof! { assert(multiple_component_transform_view(&graph) =~= mct_stages_view(graph.stages@)); }
        Ok(Some(graph))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures mct_stage_outcome(result) == crate::specs::part1_mct_graph_stage(
            mct_record_view(record), mct_arrays_view(arrays@)),
    ))]
    pub(super) fn resolve_mct_stage(
        &self,
        record: &MctRecord,
        arrays: &[MctArray],
    ) -> Result<MctStage, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost goal = crate::specs::part1_mct_graph_stage(mct_record_view(record), mct_arrays_view(arrays@)); }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_mct_graph_stage); reveal(mct_record_view); }
        let mut collections = Vec::with_capacity(record.collections.len());
        #[cfg(verus_keep_ghost)]
        proof! { assert(mct_collections_view(collections@) =~= Seq::empty()); }
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= record.collections.len(),
                goal == crate::specs::part1_mct_graph_stage(mct_record_view(record), mct_arrays_view(arrays@)),
                goal == crate::specs::part1_mct_graph_stage_from(
                    mct_record_view(record), mct_arrays_view(arrays@), position as nat, mct_collections_view(collections@)),
            decreases record.collections.len() - position,
        ))]
        while position < record.collections.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_mct_graph_stage_from, 1); reveal(mct_record_view); }
            let collection = self.resolve_mct_collection(&record.collections[position], arrays)?;
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before = mct_collections_view(collections@); let ghost value = mct_collection_view(&collection); }
            collections.push(collection);
            #[cfg(verus_keep_ghost)]
            proof! { assert(mct_collections_view(collections@) =~= before.push(value)); }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_mct_graph_stage_from, 1); }
        let stage = MctStage {
            index: record.index,
            collections,
        };
        #[cfg(verus_keep_ghost)]
        proof! { assert(mct_stage_view(&stage).1 =~= mct_collections_view(stage.collections@)); }
        Ok(stage)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures mct_collection_outcome(result) == crate::specs::part1_mct_graph_collection(
            mcc_collection_reference_view(reference), mct_arrays_view(arrays@)),
    ))]
    pub(super) fn resolve_mct_collection(
        &self,
        reference: &MctCollectionReference,
        arrays: &[MctArray],
    ) -> Result<MctCollection, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_mct_graph_collection);
            reveal(mcc_collection_reference_view); reveal(mcc_reference_transform_view);
            reveal(mct_array_view); reveal(mct_wavelet_view);
        }
        let rows = reference.input_components.len();
        let columns = reference.output_components.len();
        if rows == 0 || rows != columns {
            return Err(self.malformed_at(0, MalformedKind::InvalidTransform));
        }
        let collection = match reference.transform {
            MctCollectionReferenceTransform::Array {
                kind,
                reversible,
                transform_index,
                offset_index,
            } => {
                let offsets = if offset_index == 0 {
                    None
                } else {
                    Some(referenced_mct_array(arrays, offset_index, MctArrayKind::Offset)?.clone())
                };
                let invalid_offset_dimensions = match &offsets {
                    Some(array) => array.values.len() != rows,
                    None => false,
                };
                let floating_offsets = match &offsets {
                    Some(array) => array.fraction_bits != 0,
                    None => false,
                };
                let matrix = if transform_index == 0 {
                    None
                } else {
                    Some(referenced_mct_array(arrays, transform_index, kind)?.clone())
                };
                let expected_elements =
                    self.expected_mct_elements(rows, columns, kind, reversible)?;
                let invalid_matrix_dimensions = match &matrix {
                    Some(array) => array.values.len() != expected_elements,
                    None => false,
                };
                let floating_matrix = match &matrix {
                    Some(array) => array.fraction_bits != 0,
                    None => false,
                };
                if invalid_offset_dimensions
                    || invalid_matrix_dimensions
                    || (reversible && (floating_matrix || floating_offsets))
                {
                    return Err(self.malformed_at(0, MalformedKind::InvalidTransform));
                }
                if let (true, Some(matrix)) = (
                    reversible && mct_array_kinds_equal(kind, MctArrayKind::Decorrelation),
                    &matrix,
                ) {
                    validate_reversible_mct_coefficients(&matrix.values, rows)?;
                }
                MctCollection {
                    reversible,
                    input_components: reference.input_components.clone(),
                    output_components: reference.output_components.clone(),
                    kind: if mct_array_kinds_equal(kind, MctArrayKind::Dependency) {
                        MctCollectionKind::Dependency
                    } else {
                        MctCollectionKind::Decorrelation
                    },
                    matrix,
                    offsets,
                    wavelet: None,
                }
            }
            MctCollectionReferenceTransform::Wavelet(wavelet) => MctCollection {
                reversible: matches!(wavelet.transform, MctWaveletType::Reversible5x3),
                input_components: reference.input_components.clone(),
                output_components: reference.output_components.clone(),
                kind: MctCollectionKind::Wavelet,
                matrix: None,
                offsets: None,
                wavelet: Some(wavelet),
            },
        };
        Ok(collection)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_mct_graph_element_count(rows, columns, kind, reversible),
    ))]
    pub(super) fn expected_mct_elements(
        &self,
        rows: usize,
        columns: usize,
        kind: MctArrayKind,
        reversible: bool,
    ) -> Result<usize, DecodeError> {
        if mct_array_kinds_equal(kind, MctArrayKind::Decorrelation) {
            let stages = if reversible {
                match columns.checked_add(1) {
                    Some(value) => value,
                    None => return Err(self.malformed_at(0, MalformedKind::ArithmeticOverflow)),
                }
            } else {
                columns
            };
            match rows.checked_mul(stages) {
                Some(value) => Ok(value),
                None => Err(self.malformed_at(0, MalformedKind::ArithmeticOverflow)),
            }
        } else if reversible {
            let partner = match rows.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_at(0, MalformedKind::ArithmeticOverflow)),
            };
            let product = match rows.checked_mul(partner) {
                Some(value) => value,
                None => return Err(self.malformed_at(0, MalformedKind::ArithmeticOverflow)),
            };
            match (product / 2).checked_sub(1) {
                Some(value) => Ok(value),
                None => Err(self.malformed_at(0, MalformedKind::ArithmeticOverflow)),
            }
        } else {
            let partner = rows.saturating_sub(1);
            let product = match rows.checked_mul(partner) {
                Some(value) => value,
                None => return Err(self.malformed_at(0, MalformedKind::ArithmeticOverflow)),
            };
            Ok(product / 2)
        }
    }

    #[cfg(any())]
    fn resolve_multiple_component_transform_legacy(
        &self,
        components: u16,
        coding_style: CodingStyle,
        arrays: &[MctArray],
        mcc: Option<Segment<'a>>,
        mco: Option<Segment<'a>>,
    ) -> Result<Option<MultipleComponentTransform>, DecodeError> {
        if arrays.is_empty() && mcc.is_none() && mco.is_none() {
            return Ok(None);
        }
        let mcc =
            mcc.ok_or_else(|| DecodeError::malformed(0, MalformedKind::MissingRequiredStructure))?;
        let mco =
            mco.ok_or_else(|| DecodeError::malformed(0, MalformedKind::MissingRequiredStructure))?;
        if coding_style.multiple_component_transform {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidTransform));
        }
        if mcc.payload.len() < 12
            || read_u16([mcc.payload[0], mcc.payload[1]]) != 0
            || read_u16([mcc.payload[3], mcc.payload[4]]) != 0
        {
            return Err(DecodeError::malformed(
                self.offset(mcc.offset),
                MalformedKind::InvalidTransform,
            ));
        }
        let collection_index = mcc.payload[2];
        let collection_count = read_u16([mcc.payload[5], mcc.payload[6]]);
        if collection_count != 1 || mcc.payload[7] != 1 {
            return Err(DecodeError::malformed(
                self.offset(mcc.offset),
                MalformedKind::InvalidTransform,
            ));
        }
        let mut position = 8_usize;
        let input_components =
            parse_mcc_component_list(mcc.payload, &mut position, components, mcc.offset)?;
        let output_components =
            parse_mcc_component_list(mcc.payload, &mut position, components, mcc.offset)?;
        if mcc.payload.len().saturating_sub(position) != 3 {
            return Err(DecodeError::malformed(
                self.offset(mcc.offset),
                MalformedKind::InvalidTransform,
            ));
        }
        let transform = (u32::from(mcc.payload[position]) << 16)
            | (u32::from(mcc.payload[position + 1]) << 8)
            | u32::from(mcc.payload[position + 2]);
        if transform & 0xfe0000 != 0 {
            return Err(DecodeError::malformed(
                self.offset(mcc.offset),
                MalformedKind::InvalidTransform,
            ));
        }
        let reversible = transform & 0x010000 != 0;
        let matrix_index = (transform & 0xff) as u8;
        let offset_index = ((transform >> 8) & 0xff) as u8;
        if matrix_index == 0 {
            return Err(DecodeError::malformed(
                self.offset(mcc.offset),
                MalformedKind::InvalidTransform,
            ));
        }
        if mco.payload.is_empty() {
            return Err(DecodeError::malformed(
                self.offset(mco.offset),
                MalformedKind::InvalidTransform,
            ));
        }
        let stages = usize::from(mco.payload[0]);
        if stages != 1 {
            return Err(DecodeError::malformed(
                self.offset(mco.offset),
                MalformedKind::InvalidTransform,
            ));
        }
        if mco.payload.len() != 2 || mco.payload[1] != collection_index {
            return Err(DecodeError::malformed(
                self.offset(mco.offset),
                MalformedKind::InvalidTransform,
            ));
        }

        let mut matrix = None;
        let mut offsets = None;
        let mut array_index = 0_usize;
        while array_index < arrays.len() {
            let array = arrays.get(array_index).ok_or_else(|| {
                DecodeError::malformed(self.offset(mcc.offset), MalformedKind::InvalidTransform)
            })?;
            if array.index == matrix_index {
                if matrix.is_some() || !matches!(array.kind, MctArrayKind::Decorrelation) {
                    return Err(DecodeError::malformed(
                        self.offset(mcc.offset),
                        MalformedKind::InvalidTransform,
                    ));
                }
                matrix = Some(array.clone());
            } else if offset_index != 0 && array.index == offset_index {
                if offsets.is_some() || !matches!(array.kind, MctArrayKind::Offset) {
                    return Err(DecodeError::malformed(
                        self.offset(mcc.offset),
                        MalformedKind::InvalidTransform,
                    ));
                }
                offsets = Some(array.clone());
            } else {
                return Err(DecodeError::malformed(
                    self.offset(mcc.offset),
                    MalformedKind::InvalidTransform,
                ));
            }
            array_index = array_index.checked_add(1).ok_or_else(|| {
                DecodeError::malformed(self.offset(mcc.offset), MalformedKind::ArithmeticOverflow)
            })?;
        }
        let matrix = matrix.ok_or_else(|| {
            DecodeError::malformed(self.offset(mcc.offset), MalformedKind::InvalidTransform)
        })?;
        if offset_index != 0 && offsets.is_none() {
            return Err(DecodeError::malformed(
                self.offset(mcc.offset),
                MalformedKind::InvalidTransform,
            ));
        }
        let count = usize::from(components);
        let matrix_elements = count.checked_mul(count).ok_or_else(|| {
            DecodeError::malformed(self.offset(mcc.offset), MalformedKind::ArithmeticOverflow)
        })?;
        let invalid_offset_dimensions = match &offsets {
            Some(array) => array.values.len() != count,
            None => false,
        };
        if matrix.values.len() != matrix_elements || invalid_offset_dimensions {
            return Err(DecodeError::malformed(
                self.offset(mcc.offset),
                MalformedKind::InvalidTransform,
            ));
        }
        let floating_offsets = match &offsets {
            Some(array) => array.fraction_bits != 0,
            None => false,
        };
        if reversible && (matrix.fraction_bits != 0 || floating_offsets) {
            return Err(DecodeError::malformed(
                self.offset(mcc.offset),
                MalformedKind::InvalidTransform,
            ));
        }
        Ok(Some(MultipleComponentTransform {
            collection_index,
            reversible,
            input_components,
            output_components,
            matrix,
            offsets,
        }))
    }
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_mct_registry_array_find(mct_arrays_view(arrays@), index, 0),
        match result { Some(position) => position < arrays.len(), None => true },
))]
pub(super) fn find_mct_array_index(arrays: &[MctArray], index: u8) -> Option<usize> {
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= arrays.len(),
            crate::specs::part1_mct_registry_array_find(mct_arrays_view(arrays@), index, 0)
                == crate::specs::part1_mct_registry_array_find(mct_arrays_view(arrays@), index, position as nat),
        decreases arrays.len() - position,
    ))]
    while position < arrays.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_mct_registry_array_find, 1); reveal(mct_array_view); }
        if arrays[position].index == index {
            return Some(position);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_mct_registry_array_find, 1); }
    None
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_mct_registry_record_find(mct_records_view(records@), index, 0),
        match result { Some(position) => position < records.len(), None => true },
))]
pub(super) fn find_mct_record_index(records: &[MctRecord], index: u8) -> Option<usize> {
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= records.len(),
            crate::specs::part1_mct_registry_record_find(mct_records_view(records@), index, 0)
                == crate::specs::part1_mct_registry_record_find(mct_records_view(records@), index, position as nat),
        decreases records.len() - position,
    ))]
    while position < records.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_mct_registry_record_find, 1); reveal(mct_record_view); }
        if records[position].index == index {
            return Some(position);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_mct_registry_record_find, 1); }
    None
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_mct_registry_unique_array(mct_arrays_view(arrays@), marker_offset),
))]
pub(super) fn validate_unique_mct_array_indexes(
    arrays: &[MctArray],
    marker_offset: usize,
) -> Result<(), DecodeError> {
    if arrays.is_empty() {
        return Ok(());
    }
    let last = arrays.len() - 1;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(mct_array_view);
        assert(mct_arrays_view(arrays@.subrange(0, last as int)) =~= mct_arrays_view(arrays@).drop_last());
    }
    if find_mct_array_index(&arrays[..last], arrays[last].index).is_some() {
        return Err(DecodeError::MalformedInput {
            offset: marker_offset as u64,
            kind: MalformedKind::InvalidTransform,
        });
    }
    Ok(())
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_mct_registry_unique_record(mct_records_view(records@), marker_offset),
))]
pub(super) fn validate_unique_mct_record_indexes(
    records: &[MctRecord],
    marker_offset: usize,
) -> Result<(), DecodeError> {
    if records.is_empty() {
        return Ok(());
    }
    let last = records.len() - 1;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(mct_record_view);
        assert(mct_records_view(records@.subrange(0, last as int)) =~= mct_records_view(records@).drop_last());
    }
    if find_mct_record_index(&records[..last], records[last].index).is_some() {
        return Err(DecodeError::MalformedInput {
            offset: marker_offset as u64,
            kind: MalformedKind::InvalidTransform,
        });
    }
    Ok(())
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(_result =>
    ensures ((), mct_arrays_view(final(arrays)@)) == crate::specs::part1_mct_registry_replace_array(
        mct_arrays_view(old(arrays)@), mct_array_view(&replacement)),
))]
pub(super) fn replace_mct_array(arrays: &mut Vec<MctArray>, replacement: MctArray) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost input = mct_arrays_view(arrays@); let ghost value = mct_array_view(&replacement); }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(mct_array_view); }
    match find_mct_array_index(arrays, replacement.index) {
        Some(index) => {
            arrays[index] = replacement;
            #[cfg(verus_keep_ghost)]
            proof! { assert(mct_arrays_view(arrays@) =~= input.update(index as int, value)); }
        }
        None => {
            arrays.push(replacement);
            #[cfg(verus_keep_ghost)]
            proof! { assert(mct_arrays_view(arrays@) =~= input.push(value)); }
        }
    }
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(_result =>
    ensures ((), mct_records_view(final(records)@)) == crate::specs::part1_mct_registry_replace_record(
        mct_records_view(old(records)@), mct_record_view(&replacement)),
))]
pub(super) fn replace_mct_record(records: &mut Vec<MctRecord>, replacement: MctRecord) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost input = mct_records_view(records@); let ghost value = mct_record_view(&replacement); }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(mct_record_view); }
    match find_mct_record_index(records, replacement.index) {
        Some(index) => {
            records[index] = replacement;
            #[cfg(verus_keep_ghost)]
            proof! { assert(mct_records_view(records@) =~= input.update(index as int, value)); }
        }
        None => {
            records.push(replacement);
            #[cfg(verus_keep_ghost)]
            proof! { assert(mct_records_view(records@) =~= input.push(value)); }
        }
    }
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures mct_array_reference_outcome(result) == crate::specs::part1_mct_registry_reference(
        mct_arrays_view(arrays@), index, kind),
))]
pub(super) fn referenced_mct_array(
    arrays: &[MctArray],
    index: u8,
    kind: MctArrayKind,
) -> Result<&MctArray, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost goal = crate::specs::part1_mct_registry_reference(mct_arrays_view(arrays@), index, kind); }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_mct_registry_reference); }
    let mut position = 0_usize;
    let mut found: Option<usize> = None;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= arrays.len(),
            match found { Some(candidate) => candidate < position, None => true },
            goal == crate::specs::part1_mct_registry_reference(mct_arrays_view(arrays@), index, kind),
            goal == crate::specs::part1_mct_registry_reference_from(
                mct_arrays_view(arrays@), index, kind, position as nat, found),
        decreases arrays.len() - position,
    ))]
    while position < arrays.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_mct_registry_reference_from, 1); reveal(mct_array_view); }
        let array = &arrays[position];
        if array.index == index && mct_array_kinds_equal(array.kind, kind) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(mct_arrays_view(arrays@)[position as int] == mct_array_view(array));
                assert(mct_arrays_view(arrays@)[position as int].0 == index);
                assert(mct_arrays_view(arrays@)[position as int].1 == kind);
            }
            if found.is_some() {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(goal == Err(crate::specs::part1_codestream_malformed(
                        0, MalformedKind::InvalidTransform)));
                }
                return Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::InvalidTransform,
                });
            }
            found = Some(position);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_mct_registry_reference_from, 1); }
    match found {
        Some(candidate) => Ok(&arrays[candidate]),
        None => Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidTransform,
        }),
    }
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_mcc_parallel_collections(mcc_collection_references_view(collections@), marker_offset),
))]
pub(super) fn validate_parallel_collections(
    collections: &[MctCollectionReference],
    marker_offset: usize,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(mcc_collection_reference_view); }
    let mut collection_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant collection_index <= collections.len(),
                forall|index: int, previous: int| 0 <= previous < index < collection_index ==>
                    !crate::specs::part1_mcc_parallel_conflict(
                        mcc_collection_references_view(collections@)[index],
                        mcc_collection_references_view(collections@)[previous]),
            decreases collections.len() - collection_index,
        )
    )]
    while collection_index < collections.len() {
        let collection = &collections[collection_index];
        let mut previous_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant previous_index <= collection_index, collection_index < collections.len(),
                    mcc_collection_reference_view(collection) == mcc_collection_references_view(collections@)[collection_index as int],
                    forall|previous: int| 0 <= previous < previous_index ==>
                        !crate::specs::part1_mcc_parallel_conflict(
                            mcc_collection_references_view(collections@)[collection_index as int],
                            mcc_collection_references_view(collections@)[previous]),
                    forall|index: int, previous: int| 0 <= previous < index < collection_index ==>
                        !crate::specs::part1_mcc_parallel_conflict(
                            mcc_collection_references_view(collections@)[index],
                            mcc_collection_references_view(collections@)[previous]),
                decreases collection_index - previous_index,
            )
        )]
        while previous_index < collection_index {
            let previous = &collections[previous_index];
            #[cfg(verus_keep_ghost)]
            proof! { reveal(mcc_collection_reference_view); }
            if component_lists_overlap(&collection.input_components, &previous.input_components)
                || component_lists_overlap(
                    &collection.input_components,
                    &previous.output_components,
                )
                || component_lists_overlap(
                    &previous.input_components,
                    &collection.output_components,
                )
                || component_lists_overlap(
                    &previous.output_components,
                    &collection.output_components,
                )
            {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(crate::specs::part1_mcc_parallel_conflict(
                        mcc_collection_references_view(collections@)[collection_index as int],
                        mcc_collection_references_view(collections@)[previous_index as int]));
                    assert(!(forall|index: int, earlier: int| 0 <= earlier < index < collections.len() ==>
                        !crate::specs::part1_mcc_parallel_conflict(
                            mcc_collection_references_view(collections@)[index],
                            mcc_collection_references_view(collections@)[earlier])));
                }
                return Err(DecodeError::MalformedInput {
                    offset: marker_offset as u64,
                    kind: MalformedKind::InvalidTransform,
                });
            }
            previous_index = match previous_index.checked_add(1) {
                Some(value) => value,
                None => {
                    return Err(DecodeError::MalformedInput {
                        offset: marker_offset as u64,
                        kind: MalformedKind::ArithmeticOverflow,
                    });
                }
            };
        }
        collection_index = match collection_index.checked_add(1) {
            Some(value) => value,
            None => {
                return Err(DecodeError::MalformedInput {
                    offset: marker_offset as u64,
                    kind: MalformedKind::ArithmeticOverflow,
                });
            }
        };
    }
    Ok(())
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_mcc_lists_overlap(left@, right@),
))]
pub(super) fn component_lists_overlap(left: &[u16], right: &[u16]) -> bool {
    let mut left_index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant left_index <= left.len(),
            forall|i: int, j: int| 0 <= i < left_index && 0 <= j < right.len() ==> left@[i] != right@[j],
        decreases left.len() - left_index,
    ))]
    while left_index < left.len() {
        let mut right_index = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant left_index < left.len(), right_index <= right.len(),
                forall|j: int| 0 <= j < right_index ==> left@[left_index as int] != right@[j],
                forall|i: int, j: int| 0 <= i < left_index && 0 <= j < right.len() ==> left@[i] != right@[j],
            decreases right.len() - right_index,
        ))]
        while right_index < right.len() {
            if left[left_index] == right[right_index] {
                return true;
            }
            right_index += 1;
        }
        left_index += 1;
    }
    false
}
