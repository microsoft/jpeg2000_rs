use super::arithmetic::{arithmetic_overflow, invalid_transform};
use super::mct::{
    apply_mct_destination_precisions, charge_mct_work, check_mct_scratch, find_transform_component,
    offset_value, offset_value_scaled, rescale_i128,
};
use super::mct_decorrelation::{begin_mct_pixel, store_mct_output_rows};
use super::{MctDependencyPreparation, TransformComponentMut};
#[cfg(verus_keep_ghost)]
use super::{
    mct_component_pairs_outcome, mct_dependency_preparation_outcome,
    mct_dependency_preparation_view, transform_components_borrow_frame, transform_components_view,
};
use crate::codestream::{MCT_FIXED_BITS, MctCollection};
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_mct_pair_storage_result(
        transform_components_view(components), inputs@, outputs@, count, mct_component_pairs_outcome(result)),
    result != Err(DecodeError::AllocationFailed) ==>
        mct_component_pairs_outcome(result) == crate::specs::part2_mct_component_pairs(
            transform_components_view(components), inputs@, outputs@, count as nat),
))]
pub(super) fn mct_component_pair_indexes(
    components: &[TransformComponentMut<'_>],
    inputs: &[u16],
    outputs: &[u16],
    count: usize,
) -> Result<(Vec<usize>, Vec<usize>), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = transform_components_view(components); }
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_mct_pair_storage_normal(before, inputs@, outputs@, count); }
    let reserved = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_mct_runtime_capacity_observed(crate::specs::Part2MctRuntimeCapacity::PairIndexes {
            components:before,inputs:inputs@,outputs:outputs@,count,destination:false,
        },crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved { crate::specs::part2_mct_pair_storage_refused(before,inputs@,outputs@,count,false,error); }
    }
    let mut source = reserved?;
    let reserved = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_mct_runtime_capacity_observed(crate::specs::Part2MctRuntimeCapacity::PairIndexes {
            components:before,inputs:inputs@,outputs:outputs@,count,destination:true,
        },crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved { crate::specs::part2_mct_pair_storage_refused(before,inputs@,outputs@,count,true,error); }
    }
    let mut destination = reserved?;
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_mct_pairs_empty(before, inputs@, outputs@); }
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= count,
        before == transform_components_view(components),
        source@.len() == index, destination@.len() == index,
        crate::specs::part2_mct_component_pairs(before, inputs@, outputs@, index as nat) == Ok((source@, destination@)),
        crate::specs::part2_mct_pair_storage_result(before,inputs@,outputs@,count,
            crate::specs::part2_mct_component_pairs(before,inputs@,outputs@,count as nat)),
        decreases count - index,
    ))]
    while index < count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_pairs_step(before, inputs@, outputs@, index as nat);
            crate::proofs::production_impl::production_mct_pairs_error(before, inputs@, outputs@, index as nat + 1, count as nat);
        }
        source.push(find_transform_component(
            components,
            *inputs.get(index).ok_or_else(invalid_transform)?,
        )?);
        destination.push(find_transform_component(
            components,
            *outputs.get(index).ok_or_else(invalid_transform)?,
        )?);
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok((source, destination))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_dependency_coefficients(count, reversible),
))]
pub(super) fn mct_dependency_coefficient_count(
    count: usize,
    reversible: bool,
) -> Result<usize, DecodeError> {
    if reversible {
        let following = count.checked_add(1).ok_or_else(arithmetic_overflow)?;
        let product = count
            .checked_mul(following)
            .ok_or_else(arithmetic_overflow)?;
        let half = product.checked_div(2).ok_or_else(arithmetic_overflow)?;
        half.checked_sub(1).ok_or_else(arithmetic_overflow)
    } else {
        let product = count
            .checked_mul(count.saturating_sub(1))
            .ok_or_else(arithmetic_overflow)?;
        product.checked_div(2).ok_or_else(arithmetic_overflow)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, *final(work)) == crate::specs::part2_mct_dependency_admission(
        sample_count, expected_coefficients, count, *old(work),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(super) fn admit_mct_dependency(
    sample_count: usize,
    expected_coefficients: usize,
    count: usize,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<(), DecodeError> {
    let twice = (expected_coefficients as u64)
        .checked_mul(2)
        .ok_or_else(arithmetic_overflow)?;
    let per_sample = twice
        .checked_add(count as u64)
        .ok_or_else(arithmetic_overflow)?;
    let operations = (sample_count as u64)
        .checked_mul(per_sample)
        .ok_or_else(arithmetic_overflow)?;
    charge_mct_work(work, operations, limits)?;
    check_mct_scratch(count.saturating_mul(3), limits)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_validate_dependency_layout(
        transform_components_view(components), source_indexes@, destination_indexes@, reversible,
    ),
))]
pub(super) fn validate_mct_dependency_layout(
    components: &[TransformComponentMut<'_>],
    source_indexes: &[usize],
    destination_indexes: &[usize],
    reversible: bool,
) -> Result<usize, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::mct_fixed_precision_is_q32(); }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = transform_components_view(components); }
    let first_index = *source_indexes.first().ok_or_else(invalid_transform)?;
    let first = components.get(first_index).ok_or_else(invalid_transform)?;
    let sample_count = first.samples.len();
    let geometry = (
        first.width,
        first.height,
        first.x,
        first.y,
        first.x_subsampling,
        first.y_subsampling,
    );
    let mut list = 0_u8;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant list <= 2,
            MCT_FIXED_BITS == 32,
            before == transform_components_view(components),
            source_indexes@.len() > 0,
            source_indexes@[0] == first_index,
            first_index < before.len(),
            before[first_index as int].1 == (geometry.2, geometry.3, geometry.0, geometry.1, geometry.4, geometry.5),
            before[first_index as int].3.len() == sample_count,
            list > 0 ==> forall |position: int| 0 <= position < source_indexes@.len()
                ==> crate::specs::part2_mct_dependency_layout_index_valid(before, first_index, source_indexes@[position], reversible),
            list > 1 ==> forall |position: int| 0 <= position < destination_indexes@.len()
                ==> crate::specs::part2_mct_dependency_layout_index_valid(before, first_index, destination_indexes@[position], reversible),
            decreases 2 - list,
        )
    )]
    while list < 2 {
        let indexes = if list == 0 {
            source_indexes
        } else {
            destination_indexes
        };
        let mut component_position = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant component_position <= indexes.len(),
                list < 2,
                MCT_FIXED_BITS == 32,
                before == transform_components_view(components),
                source_indexes@.len() > 0,
                source_indexes@[0] == first_index,
                first_index < before.len(),
                before[first_index as int].1 == (geometry.2, geometry.3, geometry.0, geometry.1, geometry.4, geometry.5),
                before[first_index as int].3.len() == sample_count,
                indexes@ == if list == 0 { source_indexes@ } else { destination_indexes@ },
                list > 0 ==> forall |position: int| 0 <= position < source_indexes@.len()
                    ==> crate::specs::part2_mct_dependency_layout_index_valid(before, first_index, source_indexes@[position], reversible),
                forall |position: int| 0 <= position < component_position
                    ==> crate::specs::part2_mct_dependency_layout_index_valid(before, first_index, indexes@[position], reversible),
                decreases indexes.len() - component_position,
            )
        )]
        while component_position < indexes.len() {
            let index = *indexes
                .get(component_position)
                .ok_or_else(invalid_transform)?;
            let component = match components.get(index) {
                Some(component) => component,
                None => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(!crate::specs::part2_mct_dependency_layout_index_valid(before, first_index, index, reversible));
                        crate::proofs::production_impl::production_mct_dependency_layout_rejects(
                            before, source_indexes@, destination_indexes@, reversible, list == 0, component_position as nat);
                    }
                    return Err(invalid_transform());
                }
            };
            if (
                component.width,
                component.height,
                component.x,
                component.y,
                component.x_subsampling,
                component.y_subsampling,
            ) != geometry
                || component.samples.len() != sample_count
                || *component.fraction_bits > MCT_FIXED_BITS
                || (reversible && *component.fraction_bits != 0)
            {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(!crate::specs::part2_mct_dependency_layout_index_valid(before, first_index, index, reversible));
                    crate::proofs::production_impl::production_mct_dependency_layout_rejects(
                        before, source_indexes@, destination_indexes@, reversible, list == 0, component_position as nat);
                }
                return Err(invalid_transform());
            }
            component_position = component_position
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        list = list.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(sample_count)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_mct_dependency_prepare_storage_result(crate::specs::Part2MctRuntimeContext {
        components:transform_components_view(components),collection:crate::codestream::mct_collection_view(collection),
        work:*old(work),maximum_work:crate::limits::resource_work_limit(limits),maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits),
    },(mct_dependency_preparation_outcome(result),*final(work))),
    result!=Err(DecodeError::AllocationFailed) ==>
        (mct_dependency_preparation_outcome(result), *final(work)) == crate::specs::part2_mct_prepare_dependency(
        transform_components_view(components), crate::codestream::mct_collection_view(collection), *old(work),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(super) fn prepare_mct_dependency(
    components: &[TransformComponentMut<'_>],
    collection: &MctCollection,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<MctDependencyPreparation, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = transform_components_view(components);
        let ghost style = crate::codestream::mct_collection_view(collection);
        let ghost initial_work = *work;
        let ghost context=crate::specs::Part2MctRuntimeContext {
            components:before,collection:style,work:initial_work,
            maximum_work:crate::limits::resource_work_limit(limits),maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_mct_dependency_prepare_storage_normal(context); }
    let count = collection.input_components().len();
    if count == 0 || count != collection.output_components().len() {
        return Err(invalid_transform());
    }
    let expected_coefficients = mct_dependency_coefficient_count(count, collection.reversible())?;
    if matches!(collection.matrix(), Some(coefficients) if coefficients.values().len() != expected_coefficients)
        || matches!(collection.offsets(), Some(offsets) if offsets.values().len() != count)
    {
        return Err(invalid_transform());
    }
    let pairs = mct_component_pair_indexes(
        components,
        collection.input_components(),
        collection.output_components(),
        count,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=pairs {
            crate::specs::part2_mct_dependency_prepare_pair_error(context,count,expected_coefficients,error);
        }
    }
    let (source_indexes, destination_indexes) = pairs?;
    let sample_count = validate_mct_dependency_layout(
        components,
        &source_indexes,
        &destination_indexes,
        collection.reversible(),
    )?;
    if collection.reversible()
        && (matches!(
            collection.matrix(),
            Some(coefficients) if coefficients.fraction_bits() != 0
        ) || matches!(
            collection.offsets(),
            Some(offsets) if offsets.fraction_bits() != 0
        ))
    {
        return Err(invalid_transform());
    }
    admit_mct_dependency(sample_count, expected_coefficients, count, limits, work)?;
    Ok(MctDependencyPreparation {
        source_indexes,
        destination_indexes,
        sample_count,
        count,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(output)@) == crate::specs::part2_mct_dependency_rows(
        old(output)@, crate::codestream::mct_collection_view(collection), source@, source_fraction_bits@, count as nat,
    ),
))]
fn append_mct_dependency_rows(
    output: &mut Vec<i64>,
    collection: &MctCollection,
    source: &[i64],
    source_fraction_bits: &[u8],
    count: usize,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = output@;
        let ghost style = crate::codestream::mct_collection_view(collection);
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_mct_dependency_rows_empty(initial, style, source@, source_fraction_bits@); }
    let mut row = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row <= count,
        initial == old(output)@,
        style == crate::codestream::mct_collection_view(collection),
        crate::specs::part2_mct_dependency_rows(initial, style, source@, source_fraction_bits@, row as nat) == (Ok(()), output@),
        decreases count - row,
    ))]
    while row < count {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_mct_dependency_rows_step(initial, style, source@, source_fraction_bits@, row as nat); }
        let computed = if collection.reversible() {
            reversible_dependency_row(collection, source, output, row)
        } else {
            irreversible_dependency_row(collection, source, source_fraction_bits, output, row)
        };
        let value = match computed {
            Ok(value) => value,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! { crate::proofs::production_impl::production_mct_dependency_rows_error(initial, style, source@, source_fraction_bits@, row as nat + 1, count as nat); }
                return Err(error);
            }
        };
        output.push(value);
        row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, transform_components_view(final(components)), final(source)@, final(output)@)
        == crate::specs::part2_mct_dependency_pixel(
            transform_components_view(old(components)), crate::codestream::mct_collection_view(collection),
            mct_dependency_preparation_view(prepared), source_fraction_bits@, sample_index,
        ),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
pub(super) fn apply_mct_dependency_pixel(
    components: &mut [TransformComponentMut<'_>],
    collection: &MctCollection,
    prepared: &MctDependencyPreparation,
    source_fraction_bits: &[u8],
    sample_index: usize,
    source: &mut Vec<i64>,
    output: &mut Vec<i64>,
) -> Result<(), DecodeError> {
    begin_mct_pixel(
        components,
        &prepared.source_indexes,
        prepared.count,
        sample_index,
        source,
        output,
    )?;
    append_mct_dependency_rows(
        output,
        collection,
        source,
        source_fraction_bits,
        prepared.count,
    )?;
    store_mct_output_rows(
        components,
        &prepared.destination_indexes,
        output,
        sample_index,
        prepared.count,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_mct_dependency_storage_result(crate::specs::Part2MctRuntimeContext {
        components:transform_components_view(old(components)),collection:crate::codestream::mct_collection_view(collection),
        work:*old(work),maximum_work:crate::limits::resource_work_limit(limits),maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits),
    },(result,transform_components_view(final(components)),*final(work))),
    result!=Err(DecodeError::AllocationFailed) ==>
        (result, transform_components_view(final(components)), *final(work)) == crate::specs::part2_mct_dependency(
        transform_components_view(old(components)), crate::codestream::mct_collection_view(collection),
        *old(work), crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
    ),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
pub(super) fn apply_mct_dependency(
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
        let ghost context=crate::specs::Part2MctRuntimeContext {
            components:before,collection:style,work:initial_work,
            maximum_work:crate::limits::resource_work_limit(limits),maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::codestream::mct_fixed_precision_is_q32();
        crate::specs::part2_mct_dependency_storage_normal(context);
    }
    let preparation = prepare_mct_dependency(components, collection, limits, work);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=preparation { crate::specs::part2_mct_dependency_storage_prepare_error(context,error,*work); }
    }
    let prepared = preparation?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost plan = mct_dependency_preparation_view(&prepared); }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_pairs_lengths(before, style.1, style.2, plan.3 as nat, plan.0, plan.1);
        crate::proofs::production_impl::production_mct_dependency_layout_bounds(before, plan.0, plan.1, style.0, plan.2);
    }
    let count = prepared.count;
    let sample_count = prepared.sample_count;
    let reserved = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_mct_runtime_capacity_observed(crate::specs::Part2MctRuntimeCapacity::DependencyScratch {
            context,role:crate::specs::Part2MctRuntimeRole::SourceSamples,
        },crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved { crate::specs::part2_mct_dependency_storage_scratch_error(
            context,plan,*work,crate::specs::Part2MctRuntimeRole::SourceSamples,error); }
    }
    let mut source = reserved?;
    let reserved = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_mct_runtime_capacity_observed(crate::specs::Part2MctRuntimeCapacity::DependencyScratch {
            context,role:crate::specs::Part2MctRuntimeRole::OutputSamples,
        },crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved { crate::specs::part2_mct_dependency_storage_scratch_error(
            context,plan,*work,crate::specs::Part2MctRuntimeRole::OutputSamples,error); }
    }
    let mut output = reserved?;
    let reserved = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_mct_runtime_capacity_observed(crate::specs::Part2MctRuntimeCapacity::DependencyScratch {
            context,role:crate::specs::Part2MctRuntimeRole::FractionBits,
        },crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved { crate::specs::part2_mct_dependency_storage_scratch_error(
            context,plan,*work,crate::specs::Part2MctRuntimeRole::FractionBits,error); }
    }
    let mut source_fraction_bits = reserved?;
    let mut index = 0;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= count,
            before == transform_components_view(old(components)),
            transform_components_borrow_frame(old(components)@, components@),
            before == transform_components_view(components),
            style == crate::codestream::mct_collection_view(collection),
            plan == mct_dependency_preparation_view(&prepared),
            count == plan.3, sample_count == plan.2,
            initial_work == *old(work),
            context == (crate::specs::Part2MctRuntimeContext {components:before,collection:style,work:initial_work,
                maximum_work:crate::limits::resource_work_limit(limits),maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits)}),
            (Ok(plan), *work) == crate::specs::part2_mct_prepare_dependency(
                before, style, initial_work, crate::limits::resource_work_limit(limits),
                crate::limits::resource_decoded_bytes_limit(limits)),
            plan.0.len() == count, plan.1.len() == count,
            forall |position: int| 0 <= position < plan.0.len() ==> plan.0[position] < before.len(),
            source_fraction_bits@ == Seq::new(index as nat, |position: int| before[plan.0[position] as int].2),
            crate::specs::part2_mct_dependency_storage_result(context,crate::specs::part2_mct_dependency(
                before,style,initial_work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits))),
            decreases count - index,
        )
    )]
    while index < count {
        source_fraction_bits.push(
            *components
                .get(
                    *prepared
                        .source_indexes
                        .get(index)
                        .ok_or_else(invalid_transform)?,
                )
                .ok_or_else(invalid_transform)?
                .fraction_bits,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(source_fraction_bits@ =~= Seq::new(index as nat + 1, |position: int| before[plan.0[position] as int].2));
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_dependency_pixels_empty(before, style, plan, source_fraction_bits@);
    }
    let mut sample_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant sample_index <= sample_count,
            before == transform_components_view(old(components)),
            transform_components_borrow_frame(old(components)@, components@),
            style == crate::codestream::mct_collection_view(collection),
            plan == mct_dependency_preparation_view(&prepared),
            count == plan.3, sample_count == plan.2,
            initial_work == *old(work),
            context == (crate::specs::Part2MctRuntimeContext {components:before,collection:style,work:initial_work,
                maximum_work:crate::limits::resource_work_limit(limits),maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits)}),
            (Ok(plan), *work) == crate::specs::part2_mct_prepare_dependency(
                before, style, initial_work, crate::limits::resource_work_limit(limits),
                crate::limits::resource_decoded_bytes_limit(limits)),
            source_fraction_bits@ == Seq::new(plan.0.len(), |position: int| before[plan.0[position] as int].2),
            crate::specs::part2_mct_dependency_storage_result(context,crate::specs::part2_mct_dependency(
                before,style,initial_work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits))),
            crate::specs::part2_mct_dependency_pixels(before, style, plan, source_fraction_bits@, sample_index as nat)
                == (Ok(()), transform_components_view(components)),
            decreases sample_count - sample_index,
        )
    )]
    while sample_index < sample_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_dependency_pixels_step(before, style, plan, source_fraction_bits@, sample_index as nat);
            crate::proofs::production_impl::production_mct_dependency_pixels_error(before, style, plan, source_fraction_bits@, sample_index as nat + 1, sample_count as nat);
        }
        apply_mct_dependency_pixel(
            components,
            collection,
            &prepared,
            &source_fraction_bits,
            sample_index,
            &mut source,
            &mut output,
        )?;
        sample_index = sample_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    apply_mct_destination_precisions(
        components,
        &prepared.destination_indexes,
        if collection.reversible() {
            0
        } else {
            MCT_FIXED_BITS
        },
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_dependency_row(
        crate::codestream::mct_collection_view(collection).4, crate::codestream::mct_collection_view(collection).5,
        source@, None, output@, row,
    ),
))]
pub(super) fn reversible_dependency_row(
    collection: &MctCollection,
    source: &[i64],
    output: &[i64],
    row: usize,
) -> Result<i64, DecodeError> {
    let base = (*source.get(row).ok_or_else(invalid_transform)?)
        .checked_add(offset_value(collection.offsets(), row)?)
        .ok_or_else(arithmetic_overflow)?;
    let Some(coefficients) = collection.matrix() else {
        return Ok(base);
    };
    if row == 0 {
        return Ok(base);
    }
    let next_row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
    let triangle = row.checked_mul(next_row).ok_or_else(arithmetic_overflow)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(triangle >= 2) by (nonlinear_arith)
            requires row > 0, next_row as int == row as int + 1,
                triangle as int == row as int * next_row as int;
    }
    let half = triangle.checked_div(2).ok_or_else(arithmetic_overflow)?;
    let row_start = half.checked_sub(1).ok_or_else(arithmetic_overflow)?;
    let scale = *coefficients
        .values()
        .get(row_start.checked_add(row).ok_or_else(arithmetic_overflow)?)
        .ok_or_else(invalid_transform)?;
    if scale <= 0 {
        return Err(invalid_transform());
    }
    let mut prediction = i128::from(scale / 2);
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial = prediction; }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_dot_empty(initial, crate::codestream::mct_array_view(coefficients), output@, None, row_start);
    }
    let mut column = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant column <= row,
            row > 0,
            crate::specs::part2_mct_dependency_initial(crate::codestream::mct_collection_view(collection).5, source@, None, row) == Ok(base as i128),
            crate::codestream::mct_collection_view(collection).4 == Some(crate::codestream::mct_array_view(coefficients)),
            row as nat + 1 <= usize::MAX,
            row as nat * (row as nat + 1) <= usize::MAX,
            row_start as nat == row as nat * (row as nat + 1) / 2 - 1,
            (row_start as nat + row as nat) < crate::codestream::mct_array_view(coefficients).4.len(),
            row_start as nat + row as nat <= usize::MAX,
            crate::codestream::mct_array_view(coefficients).4[row_start as int + row as int] == scale,
            scale > 0,
            initial == (scale / 2) as i128,
            crate::specs::part2_mct_dot_prefix(initial, crate::codestream::mct_array_view(coefficients), output@, None, row_start, column as nat) == Ok(prediction),
            decreases row - column,
        )
    )]
    while column < row {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_dot_step(initial, crate::codestream::mct_array_view(coefficients), output@, None, row_start, column as nat);
            crate::proofs::production_impl::production_mct_dot_error_guard(initial, crate::codestream::mct_array_view(coefficients), output@, None, row_start, column as nat + 1, row as nat);
        }
        let coefficient = *coefficients
            .values()
            .get(
                row_start
                    .checked_add(column)
                    .ok_or_else(arithmetic_overflow)?,
            )
            .ok_or_else(invalid_transform)?;
        let product = i128::from(coefficient)
            .checked_mul(i128::from(
                *output.get(column).ok_or_else(invalid_transform)?,
            ))
            .ok_or_else(arithmetic_overflow)?;
        prediction = prediction
            .checked_add(product)
            .ok_or_else(arithmetic_overflow)?;
        column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let divisor = i128::from(scale);
    let quotient = prediction / divisor;
    let predicted = if prediction % divisor < 0 {
        quotient.checked_sub(1).ok_or_else(arithmetic_overflow)?
    } else {
        quotient
    };
    match i64::try_from(
        i128::from(base)
            .checked_add(predicted)
            .ok_or_else(arithmetic_overflow)?,
    ) {
        Ok(value) => Ok(value),
        Err(_) => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_dependency_row(
        crate::codestream::mct_collection_view(collection).4, crate::codestream::mct_collection_view(collection).5,
        source@, Some(source_fraction_bits@), output@, row,
    ),
))]
pub(super) fn irreversible_dependency_row(
    collection: &MctCollection,
    source: &[i64],
    source_fraction_bits: &[u8],
    output: &[i64],
    row: usize,
) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::mct_fixed_precision_is_q32(); }
    let mut sum = rescale_i128(
        i128::from(*source.get(row).ok_or_else(invalid_transform)?),
        *source_fraction_bits
            .get(row)
            .ok_or_else(invalid_transform)?,
        MCT_FIXED_BITS,
    )?
    .checked_add(offset_value_scaled(collection.offsets(), row)?)
    .ok_or_else(arithmetic_overflow)?;
    let Some(coefficients) = collection.matrix() else {
        return match i64::try_from(sum) {
            Ok(value) => Ok(value),
            Err(_) => Err(arithmetic_overflow()),
        };
    };
    let previous = row.saturating_sub(1);
    let triangle = row.checked_mul(previous).ok_or_else(arithmetic_overflow)?;
    let row_start = triangle.checked_div(2).ok_or_else(arithmetic_overflow)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial = sum; }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_dot_empty(initial, crate::codestream::mct_array_view(coefficients), output@, Some(Seq::new(output@.len(), |index: int| 32u8)), row_start);
    }
    let mut column = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant column <= row,
            MCT_FIXED_BITS == 32,
            crate::specs::part2_mct_dependency_initial(crate::codestream::mct_collection_view(collection).5, source@, Some(source_fraction_bits@), row) == Ok(initial),
            crate::codestream::mct_collection_view(collection).4 == Some(crate::codestream::mct_array_view(coefficients)),
            previous as nat == if row == 0 { 0nat } else { (row - 1) as nat },
            row as nat * previous as nat <= usize::MAX,
            row_start as nat == row as nat * previous as nat / 2,
            crate::specs::part2_mct_dot_prefix(initial, crate::codestream::mct_array_view(coefficients), output@, Some(Seq::new(output@.len(), |index: int| 32u8)), row_start, column as nat) == Ok(sum),
            decreases row - column,
        )
    )]
    while column < row {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_dot_step(initial, crate::codestream::mct_array_view(coefficients), output@, Some(Seq::new(output@.len(), |index: int| 32u8)), row_start, column as nat);
            crate::proofs::production_impl::production_mct_dot_error_guard(initial, crate::codestream::mct_array_view(coefficients), output@, Some(Seq::new(output@.len(), |index: int| 32u8)), row_start, column as nat + 1, row as nat);
        }
        let coefficient = *coefficients
            .values()
            .get(
                row_start
                    .checked_add(column)
                    .ok_or_else(arithmetic_overflow)?,
            )
            .ok_or_else(invalid_transform)?;
        let product = i128::from(coefficient)
            .checked_mul(i128::from(
                *output.get(column).ok_or_else(invalid_transform)?,
            ))
            .ok_or_else(arithmetic_overflow)?;
        sum = sum
            .checked_add(rescale_i128(
                product,
                coefficients
                    .fraction_bits()
                    .checked_add(MCT_FIXED_BITS)
                    .ok_or_else(arithmetic_overflow)?,
                MCT_FIXED_BITS,
            )?)
            .ok_or_else(arithmetic_overflow)?;
        column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    match i64::try_from(sum) {
        Ok(value) => Ok(value),
        Err(_) => Err(arithmetic_overflow()),
    }
}
