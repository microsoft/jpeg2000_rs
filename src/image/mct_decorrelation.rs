use super::arithmetic::{arithmetic_overflow, invalid_transform};
use super::mct::{
    admit_mct_decorrelation, admit_reversible_mct_decorrelation, apply_mct_destination_precisions,
    find_transform_component, fixed_mct_row_scaled, inverse_reversible_mct, offset_value,
    offset_value_scaled, read_transform_sample, rescale_i128, reversible_mct_output,
    reversible_mct_row, store_transform_sample, validate_mct_components_layout,
};
use super::{MctDecorrelationPreparation, TransformComponentMut};
#[cfg(verus_keep_ghost)]
use super::{
    mct_decorrelation_preparation_outcome, mct_decorrelation_preparation_view,
    transform_components_borrow_frame, transform_components_view,
};
use crate::codestream::{MCT_FIXED_BITS, MctCollection};
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (mct_decorrelation_preparation_outcome(result), *final(work)) == crate::specs::part2_mct_prepare_decorrelation(
        transform_components_view(components), crate::codestream::mct_collection_view(collection), *old(work),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(super) fn prepare_mct_decorrelation(
    components: &[TransformComponentMut<'_>],
    collection: &MctCollection,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<MctDecorrelationPreparation, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = transform_components_view(components);
        let ghost style = crate::codestream::mct_collection_view(collection);
        let ghost initial_work = *work;
    }
    let rows = collection.input_components().len();
    let columns = collection.output_components().len();
    let matrix = collection.matrix();
    let invalid_offset_dimensions = match collection.offsets() {
        Some(offsets) => offsets.values().len() != rows,
        None => false,
    };
    if rows == 0
        || rows != columns
        || matches!(
            matrix,
            Some(matrix)
                if matrix.values().len()
                    != rows.checked_mul(if collection.reversible() {
                        columns.checked_add(1).ok_or_else(arithmetic_overflow)?
                    } else { columns }).ok_or_else(arithmetic_overflow)?
        )
        || invalid_offset_dimensions
    {
        return Err(invalid_transform());
    }
    if let (true, Some(matrix)) = (collection.reversible(), matrix) {
        crate::codestream::validate_reversible_mct_coefficients(matrix.values(), rows)?;
    }
    let mut source_indexes = Vec::with_capacity(columns);
    let mut destination_indexes = Vec::with_capacity(rows);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_indices_empty(before);
        assert(style.2.take(0) =~= Seq::empty());
        assert(source_indexes@ == Seq::empty());
    }
    let mut column = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant column <= columns,
            before == transform_components_view(components),
            style == crate::codestream::mct_collection_view(collection),
            rows == style.1.len(), columns == style.2.len(),
            crate::specs::part2_mct_decorrelation_dimensions(style) == Ok((rows, columns)),
            *work == initial_work,
            source_indexes@.len() == column,
            destination_indexes@.len() == 0,
            crate::specs::part2_mct_component_indices(before, style.2.take(column as int)) == Ok(source_indexes@),
            decreases columns - column,
        )
    )]
    while column < columns {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_indices_step(before, style.2, column as nat);
            crate::proofs::production_impl::production_mct_indices_error(before, style.2, column as nat + 1, columns as nat);
            assert(style.2.take(columns as int) =~= style.2);
        }
        source_indexes.push(find_transform_component(
            components,
            *collection
                .output_components()
                .get(column)
                .ok_or_else(invalid_transform)?,
        )?);
        column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(style.2.take(columns as int) =~= style.2);
        crate::proofs::production_impl::production_mct_indices_empty(before);
        assert(style.1.take(0) =~= Seq::empty());
        assert(destination_indexes@ == Seq::empty());
    }
    let mut row = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant row <= rows,
            before == transform_components_view(components),
            style == crate::codestream::mct_collection_view(collection),
            rows == style.1.len(), columns == style.2.len(),
            crate::specs::part2_mct_decorrelation_dimensions(style) == Ok((rows, columns)),
            *work == initial_work,
            source_indexes@.len() == columns,
            destination_indexes@.len() == row,
            crate::specs::part2_mct_component_indices(before, style.2) == Ok(source_indexes@),
            crate::specs::part2_mct_component_indices(before, style.1.take(row as int)) == Ok(destination_indexes@),
            decreases rows - row,
        )
    )]
    while row < rows {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_indices_step(before, style.1, row as nat);
            crate::proofs::production_impl::production_mct_indices_error(before, style.1, row as nat + 1, rows as nat);
            assert(style.1.take(rows as int) =~= style.1);
        }
        destination_indexes.push(find_transform_component(
            components,
            *collection
                .input_components()
                .get(row)
                .ok_or_else(invalid_transform)?,
        )?);
        row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(style.1.take(rows as int) =~= style.1); }
    let sample_count = validate_mct_components_layout(
        components,
        &source_indexes,
        &destination_indexes,
        collection.reversible(),
    )?;
    if collection.reversible() && matrix.is_some() {
        admit_reversible_mct_decorrelation(sample_count, rows, limits, work)?;
    } else {
        admit_mct_decorrelation(sample_count, rows, columns, limits, work)?;
    }
    let mut source_fraction_bits = Vec::with_capacity(source_indexes.len());
    let mut index_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index_index <= source_indexes.len(),
            before == transform_components_view(components),
            style == crate::codestream::mct_collection_view(collection),
            rows == style.1.len(), columns == style.2.len(),
            crate::specs::part2_mct_decorrelation_dimensions(style) == Ok((rows, columns)),
            crate::specs::part2_mct_component_indices(before, style.2) == Ok(source_indexes@),
            crate::specs::part2_mct_component_indices(before, style.1) == Ok(destination_indexes@),
            crate::specs::part2_mct_validate_layout(before, source_indexes@, destination_indexes@, style.0) == Ok(sample_count),
            crate::specs::part2_mct_collection_admission(style, sample_count, rows, columns, initial_work,
                crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)) == (Ok(()), *work),
            forall |position: int| 0 <= position < source_indexes@.len()
                ==> source_indexes@[position] < before.len(),
            source_fraction_bits@ == Seq::new(index_index as nat, |position: int| before[source_indexes@[position] as int].2),
            decreases source_indexes.len() - index_index,
        )
    )]
    while index_index < source_indexes.len() {
        let index = *source_indexes
            .get(index_index)
            .ok_or_else(invalid_transform)?;
        source_fraction_bits.push(
            *components
                .get(index)
                .ok_or_else(invalid_transform)?
                .fraction_bits,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(source_fraction_bits@ =~= Seq::new(index_index as nat + 1,
                |position: int| before[source_indexes@[position] as int].2));
        }
        index_index = index_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(MctDecorrelationPreparation {
        source_indexes,
        destination_indexes,
        source_fraction_bits,
        sample_count,
        rows,
        columns,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_decorrelation_row(
        crate::codestream::mct_collection_view(collection), source@, source_fraction_bits@, row,
    ),
))]
pub(super) fn decorrelation_mct_row(
    collection: &MctCollection,
    source: &[i64],
    source_fraction_bits: &[u8],
    row: usize,
) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::mct_fixed_precision_is_q32(); }
    let matrix = collection.matrix();
    if collection.reversible() {
        if let Some(matrix) = matrix {
            reversible_mct_row(matrix, collection.offsets(), source, row)
        } else {
            (*source.get(row).ok_or_else(invalid_transform)?)
                .checked_add(offset_value(collection.offsets(), row)?)
                .ok_or_else(arithmetic_overflow)
        }
    } else if let Some(matrix) = matrix {
        fixed_mct_row_scaled(
            matrix,
            collection.offsets(),
            source,
            source_fraction_bits,
            row,
        )
    } else {
        let scaled = rescale_i128(
            i128::from(*source.get(row).ok_or_else(invalid_transform)?),
            *source_fraction_bits
                .get(row)
                .ok_or_else(invalid_transform)?,
            MCT_FIXED_BITS,
        )?;
        let sum = scaled
            .checked_add(offset_value_scaled(collection.offsets(), row)?)
            .ok_or_else(arithmetic_overflow)?;
        match i64::try_from(sum) {
            Ok(value) => Ok(value),
            Err(_) => Err(arithmetic_overflow()),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(output)@) == crate::specs::part2_mct_decorrelation_rows(
        old(output)@, crate::codestream::mct_collection_view(collection), source@, source_fraction_bits@, rows as nat,
    ),
))]
pub(super) fn append_mct_decorrelation_rows(
    output: &mut Vec<i64>,
    collection: &MctCollection,
    source: &[i64],
    source_fraction_bits: &[u8],
    rows: usize,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = output@;
        let ghost style = crate::codestream::mct_collection_view(collection);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_rows_empty(initial, style, source@, source_fraction_bits@);
    }
    let transformed = if rows > 0 && collection.reversible() {
        match collection.matrix() {
            None => None,
            Some(matrix) => {
                if matches!(collection.offsets(), Some(offsets) if offsets.fraction_bits() != 0) {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_mct_rows_step(initial, style, source@, source_fraction_bits@, 0);
                        crate::proofs::production_impl::production_mct_rows_error(initial, style, source@, source_fraction_bits@, 1, rows as nat);
                    }
                    return Err(invalid_transform());
                }
                match inverse_reversible_mct(matrix, source) {
                    Ok(values) => Some(values),
                    Err(error) => {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            crate::proofs::production_impl::production_mct_rows_step(initial, style, source@, source_fraction_bits@, 0);
                            crate::proofs::production_impl::production_mct_rows_error(initial, style, source@, source_fraction_bits@, 1, rows as nat);
                        }
                        return Err(error);
                    }
                }
            }
        }
    } else {
        None
    };
    let mut row = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant row <= rows,
            initial == old(output)@,
            style == crate::codestream::mct_collection_view(collection),
            match &transformed {
                Some(values) => style.0 && style.4.is_some()
                    && (match style.5 { Some(offsets) => offsets.3 == 0, None => true })
                    && crate::specs::part2_inverse_reversible_mct(style.4.unwrap(), source@) == Ok(values@),
                None => rows == 0 || !style.0 || style.4.is_none(),
            },
            crate::specs::part2_mct_decorrelation_rows(initial, style, source@, source_fraction_bits@, row as nat)
                == (Ok(()), output@),
            decreases rows - row,
        )
    )]
    while row < rows {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_rows_step(initial, style, source@, source_fraction_bits@, row as nat);
        }
        let value_result = match &transformed {
            Some(values) => reversible_mct_output(values, collection.offsets(), row),
            None => decorrelation_mct_row(collection, source, source_fraction_bits, row),
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(value_result == crate::specs::part2_mct_decorrelation_row(style, source@, source_fraction_bits@, row));
        }
        let value = match value_result {
            Ok(value) => value,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(crate::specs::part2_mct_decorrelation_rows(initial, style, source@, source_fraction_bits@, row as nat + 1)
                        == (Err(error), output@));
                    crate::proofs::production_impl::production_mct_rows_error(initial, style, source@, source_fraction_bits@, row as nat + 1, rows as nat);
                }
                return Err(error);
            }
        };
        output.push(value);
        row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(source)@, final(output)@) == crate::specs::part2_mct_begin_pixel(
        transform_components_view(components), indexes@, sample_index, count as nat,
    ),
))]
pub(super) fn begin_mct_pixel(
    components: &[TransformComponentMut<'_>],
    indexes: &[usize],
    count: usize,
    sample_index: usize,
    source: &mut Vec<i64>,
    output: &mut Vec<i64>,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = transform_components_view(components); }
    source.clear();
    output.clear();
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_snapshot_empty(before, indexes@, sample_index);
    }
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= count,
        before == transform_components_view(components),
        output@ == Seq::<i64>::empty(),
        crate::specs::part2_mct_source_snapshot(before, indexes@, sample_index, index as nat) == (Ok(()), source@),
        decreases count - index,
    ))]
    while index < count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_snapshot_step(before, indexes@, sample_index, index as nat);
            crate::proofs::production_impl::production_mct_snapshot_error(
                before, indexes@, sample_index, index as nat + 1, count as nat);
        }
        let component = *indexes.get(index).ok_or_else(invalid_transform)?;
        let value = read_transform_sample(components, component, sample_index)?;
        source.push(value);
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, transform_components_view(final(components))) == crate::specs::part2_mct_store_output_rows(
        transform_components_view(old(components)), destinations@, output@, sample_index, rows as nat,
    ),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
pub(super) fn store_mct_output_rows(
    components: &mut [TransformComponentMut<'_>],
    destinations: &[usize],
    output: &[i64],
    sample_index: usize,
    rows: usize,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = transform_components_view(components); }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_store_rows_empty(before, destinations@, output@, sample_index);
    }
    let mut row = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row <= rows,
        before == transform_components_view(old(components)),
        transform_components_borrow_frame(old(components)@, components@),
        crate::specs::part2_mct_store_output_rows(before, destinations@, output@, sample_index, row as nat)
            == (Ok(()), transform_components_view(components)),
        decreases rows - row,
    ))]
    while row < rows {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_store_rows_step(before, destinations@, output@, sample_index, row as nat);
            crate::proofs::production_impl::production_mct_store_rows_error(
                before, destinations@, output@, sample_index, row as nat + 1, rows as nat);
        }
        let destination = *destinations.get(row).ok_or_else(invalid_transform)?;
        let value = *output.get(row).ok_or_else(invalid_transform)?;
        store_transform_sample(components, destination, sample_index, value)?;
        row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, transform_components_view(final(components)), final(source)@, final(output)@)
        == crate::specs::part2_mct_decorrelation_pixel(
            transform_components_view(old(components)), crate::codestream::mct_collection_view(collection),
            mct_decorrelation_preparation_view(prepared), sample_index,
        ),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
pub(super) fn apply_mct_decorrelation_pixel(
    components: &mut [TransformComponentMut<'_>],
    collection: &MctCollection,
    prepared: &MctDecorrelationPreparation,
    sample_index: usize,
    source: &mut Vec<i64>,
    output: &mut Vec<i64>,
) -> Result<(), DecodeError> {
    begin_mct_pixel(
        components,
        &prepared.source_indexes,
        prepared.source_indexes.len(),
        sample_index,
        source,
        output,
    )?;
    append_mct_decorrelation_rows(
        output,
        collection,
        source,
        &prepared.source_fraction_bits,
        prepared.rows,
    )?;
    store_mct_output_rows(
        components,
        &prepared.destination_indexes,
        output,
        sample_index,
        prepared.rows,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, transform_components_view(final(components)), *final(work)) == crate::specs::part2_mct_decorrelation(
        transform_components_view(old(components)), crate::codestream::mct_collection_view(collection),
        *old(work), crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
    ),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
pub(super) fn apply_mct_decorrelation(
    components: &mut [TransformComponentMut<'_>],
    collection: &MctCollection,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = transform_components_view(components);
        let ghost style = crate::codestream::mct_collection_view(collection);
        let ghost initial_work = *work;
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::mct_fixed_precision_is_q32(); }
    let prepared = prepare_mct_decorrelation(components, collection, limits, work)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost plan = mct_decorrelation_preparation_view(&prepared); }
    let mut source = Vec::with_capacity(prepared.columns);
    let mut output = Vec::with_capacity(prepared.rows);
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_mct_pixels_empty(before, style, plan); }
    let mut sample_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant sample_index <= prepared.sample_count,
            before == transform_components_view(old(components)),
            transform_components_borrow_frame(old(components)@, components@),
            style == crate::codestream::mct_collection_view(collection),
            plan == mct_decorrelation_preparation_view(&prepared),
            initial_work == *old(work),
            (Ok(plan), *work) == crate::specs::part2_mct_prepare_decorrelation(
                before, style, initial_work, crate::limits::resource_work_limit(limits),
                crate::limits::resource_decoded_bytes_limit(limits)),
            crate::specs::part2_mct_decorrelation_pixels(before, style, plan, sample_index as nat)
                == (Ok(()), transform_components_view(components)),
            decreases prepared.sample_count - sample_index,
        )
    )]
    while sample_index < prepared.sample_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_pixels_step(before, style, plan, sample_index as nat);
            crate::proofs::production_impl::production_mct_pixels_error(
                before, style, plan, sample_index as nat + 1, plan.3 as nat);
        }
        apply_mct_decorrelation_pixel(
            components,
            collection,
            &prepared,
            sample_index,
            &mut source,
            &mut output,
        )?;
        sample_index = sample_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    let output_fraction_bits = if collection.reversible() {
        0
    } else {
        MCT_FIXED_BITS
    };
    apply_mct_destination_precisions(
        components,
        &prepared.destination_indexes,
        output_fraction_bits,
    )
}
