use super::arithmetic::{arithmetic_overflow, invalid_transform};
use super::mct::{
    apply_mct_destination_precisions, ceil_divide_by_two, charge_mct_work, check_mct_scratch,
    read_transform_sample, rescale_i128,
};
use super::mct_decorrelation::store_mct_output_rows;
use super::mct_dependency::{mct_component_pair_indexes, validate_mct_dependency_layout};
use super::{MctWaveletPreparation, TransformComponentMut};
#[cfg(verus_keep_ghost)]
use super::{
    mct_wavelet_partition_outcome, mct_wavelet_preparation_outcome, mct_wavelet_preparation_view,
    transform_components_borrow_frame, transform_components_view,
};
use crate::codestream::{MCT_FIXED_BITS, MctCollection, MctWavelet, MctWaveletType};
use crate::transform::{inverse_5_3, inverse_9_7};
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_mct_partition_storage_result(count,crate::codestream::mct_wavelet_view(wavelet),
        mct_wavelet_partition_outcome(result)),
    result!=Err(DecodeError::AllocationFailed) ==>
        mct_wavelet_partition_outcome(result) == crate::specs::part2_mct_wavelet_partition(
        count, crate::codestream::mct_wavelet_view(wavelet)),
))]
pub(super) fn prepare_mct_wavelet_partition(
    count: usize,
    wavelet: MctWavelet,
) -> Result<(Vec<bool>, Vec<usize>, usize), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost style = crate::codestream::mct_wavelet_view(wavelet); }
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_mct_partition_storage_normal(count,style); }
    let levels = usize::from(wavelet.levels());
    let reserved = if levels == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(levels)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_mct_runtime_capacity_observed(crate::specs::Part2MctRuntimeCapacity::WaveletPartition {
            count,wavelet:style,high:false,
        },crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved {crate::specs::part2_mct_partition_storage_refused(count,style,false,error);}
    }
    let mut low_first = reserved?;
    let reserved = if levels == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(levels)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_mct_runtime_capacity_observed(crate::specs::Part2MctRuntimeCapacity::WaveletPartition {
            count,wavelet:style,high:true,
        },crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved {crate::specs::part2_mct_partition_storage_refused(count,style,true,error);}
    }
    let mut high_lengths = reserved?;
    let mut canvas_start = i64::from(wavelet.component_offset());
    let signed_count = match i64::try_from(count) {
        Ok(value) => value,
        Err(_) => return Err(arithmetic_overflow()),
    };
    let mut canvas_end = canvas_start
        .checked_add(signed_count)
        .ok_or_else(arithmetic_overflow)?;
    let level_count = wavelet.levels();
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial_start = canvas_start; let ghost initial_end = canvas_end; }
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_mct_wavelet_intervals_empty(initial_start, initial_end); }
    let mut level = 0_u8;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant level <= level_count,
            style == crate::codestream::mct_wavelet_view(wavelet),
            level_count == style.1,
            count <= i64::MAX,
            initial_start == style.2 as i64,
            initial_end as int == initial_start as int + count as int,
            crate::specs::part2_mct_partition_storage_result(count,style,crate::specs::part2_mct_wavelet_partition(count,style)),
            crate::specs::part2_mct_wavelet_intervals(initial_start, initial_end, level as nat)
                == Ok((canvas_start, canvas_end, low_first@, high_lengths@)),
            decreases level_count - level,
        )
    )]
    while level < level_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_wavelet_intervals_step(initial_start, initial_end, level as nat);
            crate::proofs::production_impl::production_mct_wavelet_intervals_error(initial_start, initial_end, level as nat + 1, level_count as nat);
        }
        let next_start = ceil_divide_by_two(canvas_start)?;
        let next_end = ceil_divide_by_two(canvas_end)?;
        let low_difference = next_end
            .checked_sub(next_start)
            .ok_or_else(arithmetic_overflow)?;
        let low_length = match usize::try_from(low_difference) {
            Ok(value) => value,
            Err(_) => return Err(invalid_transform()),
        };
        let current_difference = canvas_end
            .checked_sub(canvas_start)
            .ok_or_else(arithmetic_overflow)?;
        let current_length = match usize::try_from(current_difference) {
            Ok(value) => value,
            Err(_) => return Err(invalid_transform()),
        };
        low_first.push(canvas_start % 2 == 0);
        high_lengths.push(
            current_length
                .checked_sub(low_length)
                .ok_or_else(arithmetic_overflow)?,
        );
        canvas_start = next_start;
        canvas_end = next_end;
        level = level.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let low_difference = canvas_end
        .checked_sub(canvas_start)
        .ok_or_else(arithmetic_overflow)?;
    let low_length = match usize::try_from(low_difference) {
        Ok(value) => value,
        Err(_) => return Err(invalid_transform()),
    };
    Ok((low_first, high_lengths, low_length))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, *final(work)) == crate::specs::part2_mct_wavelet_admission(
        sample_count, count, levels, *old(work), crate::limits::resource_work_limit(limits),
        crate::limits::resource_decoded_bytes_limit(limits)),
))]
fn admit_mct_wavelet(
    sample_count: usize,
    count: usize,
    levels: u8,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<(), DecodeError> {
    let products = (sample_count as u64)
        .checked_mul(count as u64)
        .ok_or_else(arithmetic_overflow)?;
    let stages = products
        .checked_mul(u64::from(levels).saturating_add(1))
        .ok_or_else(arithmetic_overflow)?;
    let operations = stages.checked_mul(8).ok_or_else(arithmetic_overflow)?;
    charge_mct_work(work, operations, limits)?;
    check_mct_scratch(count.saturating_mul(3), limits)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_mct_wavelet_prepare_storage_result(crate::specs::Part2MctRuntimeContext {
        components:transform_components_view(components),collection:crate::codestream::mct_collection_view(collection),
        work:*old(work),maximum_work:crate::limits::resource_work_limit(limits),maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits),
    },(mct_wavelet_preparation_outcome(result),*final(work))),
    result!=Err(DecodeError::AllocationFailed) ==>
        (mct_wavelet_preparation_outcome(result), *final(work)) == crate::specs::part2_mct_prepare_wavelet(
        transform_components_view(components), crate::codestream::mct_collection_view(collection), *old(work),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
))]
fn prepare_mct_wavelet(
    components: &[TransformComponentMut<'_>],
    collection: &MctCollection,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<MctWaveletPreparation, DecodeError> {
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
    proof! {crate::specs::part2_mct_wavelet_prepare_storage_normal(context);}
    let wavelet = collection.wavelet().ok_or_else(invalid_transform)?;
    let count = collection.input_components().len();
    if count == 0 || count != collection.output_components().len() {
        return Err(invalid_transform());
    }
    let pairs = mct_component_pair_indexes(
        components,
        collection.input_components(),
        collection.output_components(),
        count,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=pairs {crate::specs::part2_mct_wavelet_prepare_pair_error(context,error);}}
    let (source_indexes, destination_indexes) = pairs?;
    let reversible = matches!(wavelet.transform(), MctWaveletType::Reversible5x3);
    let sample_count = validate_mct_dependency_layout(
        components,
        &source_indexes,
        &destination_indexes,
        reversible,
    )?;
    let partition = prepare_mct_wavelet_partition(count, wavelet);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=partition {crate::specs::part2_mct_wavelet_prepare_partition_error(
    context,crate::codestream::mct_wavelet_view(wavelet),count,sample_count,error);}}
    let (low_first, high_lengths, low_length) = partition?;
    admit_mct_wavelet(sample_count, count, wavelet.levels(), limits, work)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_dependency_layout_bounds(
            before, source_indexes@, destination_indexes@, reversible, sample_count);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost expected_plan=(source_indexes@,destination_indexes@,low_first@,high_lengths@,low_length,sample_count,count,
            crate::codestream::mct_wavelet_view(wavelet),
            Seq::new(source_indexes@.len(),|position:int|before[source_indexes@[position] as int].2));
    }
    let reserved = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_mct_wavelet_prepare_value(context)==(Ok(expected_plan),*work));
        crate::specs::part2_mct_runtime_capacity_observed(crate::specs::Part2MctRuntimeCapacity::WaveletFractions {context},
            crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved {crate::specs::part2_mct_wavelet_prepare_fraction_error(context,expected_plan,*work,error);}
    }
    let mut source_fraction_bits = reserved?;
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= source_indexes.len(),
            before == transform_components_view(components),
            style == crate::codestream::mct_collection_view(collection),
            style.6 == Some(crate::codestream::mct_wavelet_view(wavelet)),
            count > 0, count == style.1.len(), count == style.2.len(),
            crate::specs::part2_mct_component_pairs(before, style.1, style.2, count as nat) == Ok((source_indexes@, destination_indexes@)),
            crate::specs::part2_mct_validate_dependency_layout(before, source_indexes@, destination_indexes@, reversible) == Ok(sample_count),
            reversible == crate::specs::part2_mct_wavelet_reversible(crate::codestream::mct_wavelet_view(wavelet)),
            crate::specs::part2_mct_wavelet_partition(count, crate::codestream::mct_wavelet_view(wavelet)) == Ok((low_first@, high_lengths@, low_length)),
            crate::specs::part2_mct_wavelet_admission(sample_count, count, crate::codestream::mct_wavelet_view(wavelet).1,
                initial_work, crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)) == (Ok(()), *work),
            forall |position: int| 0 <= position < source_indexes@.len() ==> source_indexes@[position] < before.len(),
            source_fraction_bits@ == Seq::new(index as nat, |position: int| before[source_indexes@[position] as int].2),
            context == (crate::specs::Part2MctRuntimeContext {components:before,collection:style,work:initial_work,
                maximum_work:crate::limits::resource_work_limit(limits),maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits)}),
            crate::specs::part2_mct_wavelet_prepare_storage_result(context,crate::specs::part2_mct_prepare_wavelet(
                before,style,initial_work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits))),
            decreases source_indexes.len() - index,
        )
    )]
    while index < source_indexes.len() {
        let source_index = *source_indexes.get(index).ok_or_else(invalid_transform)?;
        source_fraction_bits.push(
            *components
                .get(source_index)
                .ok_or_else(invalid_transform)?
                .fraction_bits,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(source_fraction_bits@ =~= Seq::new(index as nat + 1, |position: int| before[source_indexes@[position] as int].2));
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(MctWaveletPreparation {
        source_indexes,
        destination_indexes,
        low_first,
        high_lengths,
        low_length,
        sample_count,
        count,
        wavelet,
        source_fraction_bits,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_wavelet_source_value(
        transform_components_view(components), indexes@, fractions@, sample, index as nat, reversible),
))]
fn read_mct_wavelet_source(
    components: &[TransformComponentMut<'_>],
    indexes: &[usize],
    fractions: &[u8],
    sample: usize,
    index: usize,
    reversible: bool,
) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::mct_fixed_precision_is_q32(); }
    let component = *indexes.get(index).ok_or_else(invalid_transform)?;
    let value = read_transform_sample(components, component, sample)?;
    if reversible {
        Ok(value)
    } else {
        let scaled = rescale_i128(
            i128::from(value),
            *fractions.get(index).ok_or_else(invalid_transform)?,
            MCT_FIXED_BITS,
        )?;
        match i64::try_from(scaled) {
            Ok(value) => Ok(value),
            Err(_) => Err(arithmetic_overflow()),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(source)@) == crate::specs::part2_mct_wavelet_snapshot(
        transform_components_view(components), indexes@, fractions@, sample, reversible, count as nat),
))]
pub(super) fn begin_mct_wavelet_pixel(
    source: &mut Vec<i64>,
    components: &[TransformComponentMut<'_>],
    indexes: &[usize],
    fractions: &[u8],
    sample: usize,
    count: usize,
    reversible: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = transform_components_view(components); }
    source.clear();
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_mct_wavelet_snapshot_empty(before, indexes@, fractions@, sample, reversible); }
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= count, before == transform_components_view(components),
        crate::specs::part2_mct_wavelet_snapshot(before, indexes@, fractions@, sample, reversible, index as nat) == (Ok(()), source@),
        decreases count - index,
    ))]
    while index < count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_wavelet_snapshot_step(before, indexes@, fractions@, sample, reversible, index as nat);
            crate::proofs::production_impl::production_mct_wavelet_snapshot_error(before, indexes@, fractions@, sample, reversible, index as nat + 1, count as nat);
        }
        let value =
            read_mct_wavelet_source(components, indexes, fractions, sample, index, reversible)?;
        source.push(value);
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_mct_line_reconstruction_result(source@,high_lengths@,low_first@,reversible,low_length,count,crate::transform::sequence_outcome(result)),
        crate::transform::sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> crate::transform::sequence_outcome(result) == crate::specs::part2_mct_wavelet_reconstruction(
        source@, high_lengths@, low_first@, reversible, low_length, count),
))]
fn reconstruct_mct_wavelet(
    source: &[i64],
    high_lengths: &[usize],
    low_first: &[bool],
    reversible: bool,
    low_length: usize,
    count: usize,
) -> Result<Vec<i64>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_mct_line_reconstruction_normal(source@,high_lengths@,low_first@,reversible,low_length,count);}
    let mut cursor = low_length;
    let reserved = if low_length == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(low_length)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_mct_runtime_capacity_observed(crate::specs::Part2MctRuntimeCapacity::WaveletReconstruction {
            source:source@,high:high_lengths@,first:low_first@,reversible,low:low_length,count,
        },crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved {crate::specs::part2_mct_line_reconstruction_capacity_error(
            source@,high_lengths@,low_first@,reversible,low_length,count,error);}
    }
    let mut reconstructed = reserved?;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_wavelet_reconstruction_empty(source@, high_lengths@, low_first@, reversible, low_length);
        crate::proofs::production_impl::production_mct_wavelet_reconstruction_error(source@, high_lengths@, low_first@, reversible, low_length, 0, high_lengths@.len());
    }
    reconstructed.extend_from_slice(source.get(..low_length).ok_or_else(invalid_transform)?);
    #[cfg(verus_keep_ghost)]
    proof! { assert(reconstructed@ =~= source@.take(low_length as int)); }
    let mut level_index = high_lengths.len();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant level_index <= high_lengths.len(),
        crate::specs::part2_mct_line_reconstruction_result(source@,high_lengths@,low_first@,reversible,low_length,count,
            crate::specs::part2_mct_wavelet_reconstruction(source@,high_lengths@,low_first@,reversible,low_length,count)),
        crate::specs::part2_mct_wavelet_reconstruction_steps(source@, high_lengths@, low_first@, reversible, low_length,
            (high_lengths.len() - level_index) as nat) == Ok((cursor, reconstructed@)),
        decreases level_index,
    ))]
    while level_index != 0 {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_wavelet_reconstruction_step(
                source@, high_lengths@, low_first@, reversible, low_length, (high_lengths.len() - level_index) as nat);
            crate::proofs::production_impl::production_mct_wavelet_reconstruction_error(
                source@, high_lengths@, low_first@, reversible, low_length, (high_lengths.len() - level_index + 1) as nat, high_lengths@.len());
        }
        level_index = level_index.checked_sub(1).ok_or_else(arithmetic_overflow)?;
        let high_length = *high_lengths
            .get(level_index)
            .ok_or_else(invalid_transform)?;
        let high_end = cursor
            .checked_add(high_length)
            .ok_or_else(arithmetic_overflow)?;
        let high = source.get(cursor..high_end).ok_or_else(invalid_transform)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost previous=(cursor,reconstructed@);}
        let parity = *low_first.get(level_index).ok_or_else(invalid_transform)?;
        let transformed = if reversible {
            inverse_5_3(&reconstructed, high, parity)
        } else {
            inverse_9_7(&reconstructed, high, parity)
        };
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=transformed{crate::specs::part2_mct_line_child_error(source@,high_lengths@,low_first@,reversible,low_length,count,
        (high_lengths.len()-level_index-1) as nat,previous,high_end,high@,parity,error);}}
        reconstructed = transformed?;
        cursor = high_end;
    }
    if cursor != count || reconstructed.len() != count {
        return Err(invalid_transform());
    }
    Ok(reconstructed)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_mct_line_pixel_result(transform_components_view(old(components)),mct_wavelet_preparation_view(prepared),sample_index,
        (result,transform_components_view(final(components)),final(source)@)),
        result!=Err(DecodeError::AllocationFailed) ==> (result, transform_components_view(final(components)), final(source)@) == crate::specs::part2_mct_wavelet_pixel(
        transform_components_view(old(components)), mct_wavelet_preparation_view(prepared), sample_index),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
fn apply_mct_wavelet_pixel(
    components: &mut [TransformComponentMut<'_>],
    prepared: &MctWaveletPreparation,
    sample_index: usize,
    source: &mut Vec<i64>,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before=transform_components_view(components);}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_mct_line_pixel_normal(before,mct_wavelet_preparation_view(prepared),sample_index);}
    let reversible = matches!(prepared.wavelet.transform(), MctWaveletType::Reversible5x3);
    begin_mct_wavelet_pixel(
        source,
        components,
        &prepared.source_indexes,
        &prepared.source_fraction_bits,
        sample_index,
        prepared.count,
        reversible,
    )?;
    let reconstructed_result = reconstruct_mct_wavelet(
        source,
        &prepared.high_lengths,
        &prepared.low_first,
        reversible,
        prepared.low_length,
        prepared.count,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=reconstructed_result{crate::specs::part2_mct_line_pixel_child_error(before,mct_wavelet_preparation_view(prepared),sample_index,source@,error);}}
    let reconstructed = reconstructed_result?;
    store_mct_output_rows(
        components,
        &prepared.destination_indexes,
        &reconstructed,
        sample_index,
        prepared.count,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_mct_line_wavelet_result(transform_components_view(old(components)),crate::codestream::mct_collection_view(collection),*old(work),
        crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),(result,transform_components_view(final(components)),*final(work))),
        result!=Err(DecodeError::AllocationFailed) ==> (result, transform_components_view(final(components)), *final(work)) == crate::specs::part2_mct_wavelet(
        transform_components_view(old(components)), crate::codestream::mct_collection_view(collection), *old(work),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
pub(super) fn apply_mct_wavelet(
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
    proof! { crate::codestream::mct_fixed_precision_is_q32(); }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_mct_line_wavelet_normal(before,style,initial_work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits));}
    let preparation = prepare_mct_wavelet(components, collection, limits, work);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=preparation {crate::specs::part2_mct_line_wavelet_prepare_error(context,error,*work);}}
    let prepared = preparation?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost plan = mct_wavelet_preparation_view(&prepared); }
    let reserved = if prepared.count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(prepared.count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_mct_runtime_capacity_observed(crate::specs::Part2MctRuntimeCapacity::WaveletSource {context},
            crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved {crate::specs::part2_mct_line_wavelet_source_error(context,plan,*work,error);}
    }
    let mut source = reserved?;
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_mct_wavelet_pixels_empty(before, plan); }
    let mut sample_index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant sample_index <= prepared.sample_count,
        before == transform_components_view(old(components)),
        transform_components_borrow_frame(old(components)@, components@),
        style == crate::codestream::mct_collection_view(collection),
        plan == mct_wavelet_preparation_view(&prepared),
        initial_work == *old(work),
        context == (crate::specs::Part2MctRuntimeContext {components:before,collection:style,work:initial_work,
            maximum_work:crate::limits::resource_work_limit(limits),maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits)}),
        crate::specs::part2_mct_line_wavelet_result(before,style,initial_work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),
            crate::specs::part2_mct_wavelet(before,style,initial_work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits))),
        (Ok(plan), *work) == crate::specs::part2_mct_prepare_wavelet(
            before, style, initial_work, crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
        crate::specs::part2_mct_wavelet_pixels(before, plan, sample_index as nat) == (Ok(()), transform_components_view(components)),
        decreases prepared.sample_count - sample_index,
    ))]
    while sample_index < prepared.sample_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_wavelet_pixels_step(before, plan, sample_index as nat);
            crate::proofs::production_impl::production_mct_wavelet_pixels_error(before, plan, sample_index as nat + 1, plan.5 as nat);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before_pixel=transform_components_view(components);}
        let pixel = apply_mct_wavelet_pixel(components, &prepared, sample_index, &mut source);
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=pixel{crate::specs::part2_mct_line_wavelet_pixel_error(before,style,initial_work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),
        plan,*work,sample_index as nat,before_pixel,(pixel,transform_components_view(components),source@));}}
        pixel?;
        sample_index = sample_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    apply_mct_destination_precisions(
        components,
        &prepared.destination_indexes,
        if matches!(prepared.wavelet.transform(), MctWaveletType::Reversible5x3) {
            0
        } else {
            MCT_FIXED_BITS
        },
    )
}

#[cfg(test)]
mod singleton_tests {
    use super::reconstruct_mct_wavelet;

    #[test]
    fn wavelet_line_storage_actual_spectral_prior_owner_and_exact_refusal_restore() {
        for reversible in [false, true] {
            let source = [7, 3, -2, 5];
            let expected =
                reconstruct_mct_wavelet(&source, &[2], &[true], reversible, 2, 4).unwrap();
            assert_eq!(
                crate::allocation::with_refusal(0, || reconstruct_mct_wavelet(
                    &source,
                    &[2],
                    &[true],
                    reversible,
                    2,
                    4
                )),
                Err(crate::DecodeError::AllocationFailed)
            );
            assert_eq!(
                reconstruct_mct_wavelet(&source, &[2], &[true], reversible, 2, 4).unwrap(),
                expected
            );
        }
    }

    #[test]
    fn sarah_engineering_nine_seven_spectral_consumer_retains_raw_operator_units() {
        for value in [i64::MIN, -257, -2, -1, 0, 1, 2, 257, i64::MAX] {
            for reversible in [false, true] {
                assert_eq!(
                    reconstruct_mct_wavelet(&[value], &[1], &[false], reversible, 0, 1).unwrap(),
                    [value >> 1],
                );
                assert_eq!(
                    reconstruct_mct_wavelet(&[value], &[0], &[true], reversible, 1, 1).unwrap(),
                    [value],
                );
            }
        }
    }
}
