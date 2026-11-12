#[cfg(any())]
use super::FIXED_BITS;
use super::arithmetic::{arithmetic_overflow, invalid_transform};
#[cfg(any())]
use super::component_transform::{component_sample, set_component_sample};
use super::mct_decorrelation::apply_mct_decorrelation;
use super::mct_dependency::apply_mct_dependency;
use super::mct_wavelet::apply_mct_wavelet;
use super::{DecodedComponent, DecodedImage, TransformComponentMut};
#[cfg(verus_keep_ghost)]
use super::{
    decoded_component_view, decoded_image_view, transform_component_borrow_frame,
    transform_component_final_precision, transform_component_final_samples,
    transform_component_mut_view, transform_components_borrow_frame, transform_components_view,
};
use crate::codestream::{
    MCT_FIXED_BITS, MctArray, MctCollection, MctCollectionKind, MctStage,
    MultipleComponentTransform,
};
use crate::{DecodeError, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_source_sample(transform_components_view(components), component, index),
))]
pub(super) fn read_transform_sample(
    components: &[TransformComponentMut<'_>],
    component: usize,
    index: usize,
) -> Result<i64, DecodeError> {
    let component = components.get(component).ok_or_else(invalid_transform)?;
    Ok(*component.samples.get(index).ok_or_else(invalid_transform)?)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, transform_component_mut_view(final(component))) == crate::specs::part2_mct_store_component_sample(
        transform_component_mut_view(old(component)), index, value,
    ),
    transform_component_borrow_frame(*old(component), *final(component)),
))]
pub(super) fn store_transform_component_sample(
    component: &mut TransformComponentMut<'_>,
    index: usize,
    value: i64,
) -> Result<(), DecodeError> {
    let sample = component
        .samples
        .get_mut(index)
        .ok_or_else(invalid_transform)?;
    *sample = value;
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, transform_components_view(final(components))) == crate::specs::part2_mct_store_sample(
        transform_components_view(old(components)), destination, index, value,
    ),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
pub(super) fn store_transform_sample(
    components: &mut [TransformComponentMut<'_>],
    destination: usize,
    index: usize,
    value: i64,
) -> Result<(), DecodeError> {
    let component = components
        .get_mut(destination)
        .ok_or_else(invalid_transform)?;
    store_transform_component_sample(component, index, value)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures transform_component_mut_view(final(component)) == crate::specs::part2_mct_component_precision(
        transform_component_mut_view(old(component)), precision,
    ),
    transform_component_borrow_frame(*old(component), *final(component)),
))]
fn set_transform_component_precision(component: &mut TransformComponentMut<'_>, precision: u8) {
    *component.fraction_bits = precision;
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, transform_components_view(final(components))) == crate::specs::part2_mct_set_precision(
        transform_components_view(old(components)), destination, precision,
    ),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
fn set_transform_precision(
    components: &mut [TransformComponentMut<'_>],
    destination: usize,
    precision: u8,
) -> Result<(), DecodeError> {
    let component = components
        .get_mut(destination)
        .ok_or_else(invalid_transform)?;
    set_transform_component_precision(component, precision);
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, transform_components_view(final(components))) == crate::specs::part2_mct_destination_precisions(
        transform_components_view(old(components)), destinations@, precision, destinations@.len(),
    ),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
pub(super) fn apply_mct_destination_precisions(
    components: &mut [TransformComponentMut<'_>],
    destinations: &[usize],
    precision: u8,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = transform_components_view(components); }
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_mct_precisions_empty(before, destinations@, precision); }
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= destinations.len(),
        before == transform_components_view(old(components)),
        transform_components_borrow_frame(old(components)@, components@),
        crate::specs::part2_mct_destination_precisions(before, destinations@, precision, index as nat)
            == (Ok(()), transform_components_view(components)),
        decreases destinations.len() - index,
    ))]
    while index < destinations.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_precisions_step(before, destinations@, precision, index as nat);
            crate::proofs::production_impl::production_mct_precisions_error(
                before, destinations@, precision, index as nat + 1, destinations@.len());
        }
        let destination = *destinations.get(index).ok_or_else(invalid_transform)?;
        set_transform_precision(components, destination, precision)?;
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, decoded_image_view(*final(image))) == crate::specs::part2_mct_decoded_image(
        decoded_image_view(*old(image)), crate::codestream::multiple_component_transform_view(transform),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub fn apply_multiple_component_transform(
    image: &mut DecodedImage,
    transform: &MultipleComponentTransform,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = decoded_image_view(*image); }
    let mut components = Vec::with_capacity(image.components.len());
    collect_decoded_transform_components(&mut image.components, 0, &mut components)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(Seq::new(components@.len(), |index: int| transform_component_mut_view(&components@[index]))
            =~= crate::specs::part2_mct_decoded_inputs(before.4));
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost collected = components@; }
    let mut work = 0_u64;
    let result = apply_multiple_component_transform_components(
        &mut components,
        transform,
        limits,
        &mut work,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |index: int| 0 <= index < components@.len() implies
            transform_component_final_samples(&components@[index]) == transform_component_mut_view(&components@[index]).3
                && transform_component_final_precision(&components@[index]) == transform_component_mut_view(&components@[index]).2 by {}
        assert forall |index: int| 0 <= index < components@.len() implies
            transform_component_final_samples(&collected[index]) == transform_component_final_samples(&components@[index])
                && transform_component_final_precision(&collected[index]) == transform_component_final_precision(&components@[index]) by {}
        assert(decoded_image_view(*final(image)).4.len() == before.4.len());
        assert(decoded_image_view(*final(image)).4 =~= Seq::new(before.4.len(), |index: int|
            (before.4[index].0, before.4[index].1, before.4[index].2,
                transform_component_mut_view(&components@[index]).2,
                transform_component_mut_view(&components@[index]).3)));
    }
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures
        result == if component_index as nat + old(decoded)@.len() > u16::MAX {
            Err(crate::specs::part1_transform_error(true))
        } else { Ok(()) },
        final(decoded)@.len() == old(decoded)@.len(),
        final(components)@.len() == old(components)@.len()
            + if old(decoded)@.len() > u16::MAX as nat - component_index as nat {
                (u16::MAX as nat - component_index as nat + 1) as nat
            } else { old(decoded)@.len() },
        final(components)@.take(old(components)@.len() as int) == old(components)@,
        forall |position: int| 0 <= position < final(components)@.len() - old(components)@.len() ==>
            transform_component_mut_view(&final(components)@[old(components)@.len() as int + position])
                == ((component_index as nat + position) as u16,
                    (0u32, 0u32, old(decoded)@[position].width, old(decoded)@[position].height,
                        old(decoded)@[position].info.x_subsampling, old(decoded)@[position].info.y_subsampling),
                    old(decoded)@[position].fraction_bits, old(decoded)@[position].samples@),
        forall |position: int| 0 <= position < old(decoded)@.len() ==>
            decoded_component_view(final(decoded)@[position])
                == if position < final(components)@.len() - old(components)@.len() {
                    (old(decoded)@[position].width, old(decoded)@[position].height, old(decoded)@[position].info,
                        transform_component_final_precision(&final(components)@[old(components)@.len() as int + position]),
                        transform_component_final_samples(&final(components)@[old(components)@.len() as int + position]))
                } else { decoded_component_view(old(decoded)@[position]) },
    decreases decoded.len(),
))]
fn collect_decoded_transform_components<'a>(
    decoded: &'a mut [DecodedComponent],
    component_index: u16,
    components: &mut Vec<TransformComponentMut<'a>>,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_decoded = decoded@;
        let ghost original_components = components@;
    }
    let Some((component, remaining)) = decoded.split_first_mut() else {
        return Ok(());
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost remaining_before = remaining@; }
    let info = component.info;
    components.push(TransformComponentMut {
        component: component_index,
        x: 0,
        y: 0,
        width: component.width,
        height: component.height,
        x_subsampling: info.x_subsampling,
        y_subsampling: info.y_subsampling,
        fraction_bits: &mut component.fraction_bits,
        samples: &mut component.samples,
    });
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost added = components@[original_components.len() as int]; }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(transform_component_mut_view(&added) == (component_index,
            (0u32, 0u32, original_decoded[0].width, original_decoded[0].height,
                original_decoded[0].info.x_subsampling, original_decoded[0].info.y_subsampling),
            original_decoded[0].fraction_bits, original_decoded[0].samples@));
    }
    let next_index = component_index
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?;
    let result = collect_decoded_transform_components(remaining, next_index, components);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(components@[original_components.len() as int] == added);
        assert forall |position: int| 0 <= position < components@.len() - original_components.len() implies
            transform_component_mut_view(&components@[original_components.len() as int + position])
                == ((component_index as nat + position) as u16,
                    (0u32, 0u32, original_decoded[position].width, original_decoded[position].height,
                        original_decoded[position].info.x_subsampling, original_decoded[position].info.y_subsampling),
                    original_decoded[position].fraction_bits, original_decoded[position].samples@) by {
            if position > 0 {
                assert(remaining_before[position - 1].width == original_decoded[position].width);
            }
        }
    }
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, transform_components_view(final(components)), *final(work)) == crate::specs::part2_mct_transform(
        transform_components_view(old(components)), crate::codestream::multiple_component_transform_view(transform), *old(work),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
pub(crate) fn apply_multiple_component_transform_components(
    components: &mut [TransformComponentMut<'_>],
    transform: &MultipleComponentTransform,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = transform_components_view(components);
        let ghost stages = crate::codestream::multiple_component_transform_view(transform);
        let ghost initial_work = *work;
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_mct_transform_empty(before, stages, initial_work,
    crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)); }
    let mut stage_index = transform.stages().len();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant stage_index <= stages.len(),
        stages == crate::codestream::multiple_component_transform_view(transform),
        before == transform_components_view(old(components)),
        initial_work == *old(work),
        transform_components_borrow_frame(old(components)@, components@),
        crate::specs::part2_mct_transform_prefix(before, stages, initial_work,
            crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
            (stages.len() - stage_index) as nat) == (Ok(()), transform_components_view(components), *work),
        decreases stage_index,
    ))]
    while stage_index != 0 {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_transform_step(before, stages, initial_work,
                crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
                (stages.len() - stage_index) as nat);
            crate::proofs::production_impl::production_mct_transform_error(before, stages, initial_work,
                crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
                (stages.len() - stage_index + 1) as nat, stages.len());
        }
        stage_index = crate::refinement::mct_reverse_stage(stage_index);
        let stage = transform
            .stages()
            .get(stage_index)
            .ok_or_else(invalid_transform)?;
        apply_mct_stage(components, stage, limits, work)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, transform_components_view(final(components)), *final(work)) == crate::specs::part2_mct_stage_prefix(
        transform_components_view(old(components)), crate::codestream::mct_stage_view(stage).1, *old(work),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
        crate::codestream::mct_stage_view(stage).1.len()),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
fn apply_mct_stage(
    components: &mut [TransformComponentMut<'_>],
    stage: &MctStage,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = transform_components_view(components);
        let ghost collections = crate::codestream::mct_stage_view(stage).1;
        let ghost initial_work = *work;
    }
    let collection_count = stage.collections().len();
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_mct_stage_empty(before, collections, initial_work,
    crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)); }
    let mut collection_index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant collection_index <= collection_count, collection_count == collections.len(),
        collections == crate::codestream::mct_stage_view(stage).1,
        before == transform_components_view(old(components)), initial_work == *old(work),
        transform_components_borrow_frame(old(components)@, components@),
        crate::specs::part2_mct_stage_prefix(before, collections, initial_work,
            crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
            collection_index as nat) == (Ok(()), transform_components_view(components), *work),
        decreases collection_count - collection_index,
    ))]
    while collection_index < collection_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_stage_step(before, collections, initial_work,
                crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits), collection_index as nat);
            crate::proofs::production_impl::production_mct_stage_error(before, collections, initial_work,
                crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
                collection_index as nat + 1, collections.len());
        }
        apply_mct_collection(
            components,
            stage
                .collections()
                .get(collection_index)
                .ok_or_else(invalid_transform)?,
            limits,
            work,
        )?;
        collection_index = collection_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, transform_components_view(final(components)), *final(work)) == crate::specs::part2_mct_collection(
        transform_components_view(old(components)), crate::codestream::mct_collection_view(collection), *old(work),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
    transform_components_borrow_frame(old(components)@, final(components)@),
))]
fn apply_mct_collection(
    components: &mut [TransformComponentMut<'_>],
    collection: &MctCollection,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<(), DecodeError> {
    match collection.kind() {
        MctCollectionKind::Dependency => apply_mct_dependency(components, collection, limits, work),
        MctCollectionKind::Decorrelation => {
            apply_mct_decorrelation(components, collection, limits, work)
        }
        MctCollectionKind::Wavelet => apply_mct_wavelet(components, collection, limits, work),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_validate_layout(
        transform_components_view(components), source_indexes@, destination_indexes@, reversible,
    ),
))]
pub(super) fn validate_mct_components_layout(
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
    let width = first.width;
    let height = first.height;
    let x = first.x;
    let y = first.y;
    let x_subsampling = first.x_subsampling;
    let y_subsampling = first.y_subsampling;
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
            before[first_index as int].1 == (x, y, width, height, x_subsampling, y_subsampling),
            before[first_index as int].3.len() == sample_count,
            list > 0 ==> forall |position: int| 0 <= position < source_indexes@.len()
                ==> crate::specs::part2_mct_layout_index_valid(before, first_index, source_indexes@[position]),
            list > 1 ==> forall |position: int| 0 <= position < destination_indexes@.len()
                ==> crate::specs::part2_mct_layout_index_valid(before, first_index, destination_indexes@[position]),
            decreases 2 - list,
        )
    )]
    while list < 2 {
        let indexes = if list == 0 {
            source_indexes
        } else {
            destination_indexes
        };
        let mut index_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index_index <= indexes.len(),
                list < 2,
                MCT_FIXED_BITS == 32,
                before == transform_components_view(components),
                source_indexes@.len() > 0,
                source_indexes@[0] == first_index,
                first_index < before.len(),
                before[first_index as int].1 == (x, y, width, height, x_subsampling, y_subsampling),
                before[first_index as int].3.len() == sample_count,
                indexes@ == if list == 0 { source_indexes@ } else { destination_indexes@ },
                list > 0 ==> forall |position: int| 0 <= position < source_indexes@.len()
                    ==> crate::specs::part2_mct_layout_index_valid(before, first_index, source_indexes@[position]),
                forall |position: int| 0 <= position < index_index
                    ==> crate::specs::part2_mct_layout_index_valid(before, first_index, indexes@[position]),
                decreases indexes.len() - index_index,
            )
        )]
        while index_index < indexes.len() {
            let index = *indexes.get(index_index).ok_or_else(invalid_transform)?;
            let component = components.get(index).ok_or_else(invalid_transform)?;
            if component.width != width
                || component.height != height
                || component.x != x
                || component.y != y
                || component.x_subsampling != x_subsampling
                || component.y_subsampling != y_subsampling
                || component.samples.len() != sample_count
                || *component.fraction_bits > MCT_FIXED_BITS
            {
                return Err(invalid_transform());
            }
            index_index = index_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        list = list.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    if reversible {
        let mut index_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index_index <= source_indexes.len(),
                reversible,
                before == transform_components_view(components),
                source_indexes@.len() > 0,
                source_indexes@[0] == first_index,
                first_index < before.len(),
                before[first_index as int].3.len() == sample_count,
                forall |position: int| 0 <= position < source_indexes@.len()
                    ==> crate::specs::part2_mct_layout_index_valid(before, first_index, source_indexes@[position]),
                forall |position: int| 0 <= position < destination_indexes@.len()
                    ==> crate::specs::part2_mct_layout_index_valid(before, first_index, destination_indexes@[position]),
                forall |position: int| 0 <= position < index_index
                    ==> before[source_indexes@[position] as int].2 == 0,
                decreases source_indexes.len() - index_index,
            )
        )]
        while index_index < source_indexes.len() {
            let index = *source_indexes
                .get(index_index)
                .ok_or_else(invalid_transform)?;
            if *components
                .get(index)
                .ok_or_else(invalid_transform)?
                .fraction_bits
                != 0
            {
                return Err(invalid_transform());
            }
            index_index = index_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
    }
    Ok(sample_count)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, *final(work)) == crate::specs::part2_mct_decorrelation_admission(
        sample_count, rows, columns, *old(work),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(super) fn admit_mct_decorrelation(
    sample_count: usize,
    rows: usize,
    columns: usize,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<(), DecodeError> {
    let sample_rows = (sample_count as u64)
        .checked_mul(rows as u64)
        .ok_or_else(arithmetic_overflow)?;
    let products = sample_rows
        .checked_mul(columns as u64)
        .ok_or_else(arithmetic_overflow)?;
    let repeated_sample_rows = (sample_count as u64)
        .checked_mul(rows as u64)
        .ok_or_else(arithmetic_overflow)?;
    let operations = products
        .checked_add(repeated_sample_rows)
        .ok_or_else(arithmetic_overflow)?;
    charge_mct_work(work, operations, limits)?;
    let values = rows.checked_add(columns).ok_or_else(arithmetic_overflow)?;
    let scratch_bytes = values
        .checked_mul(core::mem::size_of::<i64>())
        .ok_or_else(arithmetic_overflow)? as u64;
    if scratch_bytes > limits.maximum_decoded_bytes() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: limits.maximum_decoded_bytes(),
            actual: scratch_bytes,
        });
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_offset(crate::codestream::mct_array_option(offsets), row),
))]
pub(super) fn offset_value(offsets: Option<&MctArray>, row: usize) -> Result<i64, DecodeError> {
    match offsets {
        Some(offsets) if offsets.fraction_bits() == 0 => {
            Ok(*offsets.values().get(row).ok_or_else(invalid_transform)?)
        }
        Some(_) => Err(invalid_transform()),
        None => Ok(0),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, *final(work)) == crate::specs::part2_reversible_mct_admission(
        sample_count, count, *old(work),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(super) fn admit_reversible_mct_decorrelation(
    sample_count: usize,
    count: usize,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<(), DecodeError> {
    let per_component = (count as u64)
        .checked_add(2)
        .ok_or_else(arithmetic_overflow)?;
    let per_sample = (count as u64)
        .checked_mul(per_component)
        .ok_or_else(arithmetic_overflow)?;
    let operations = (sample_count as u64)
        .checked_mul(per_sample)
        .ok_or_else(arithmetic_overflow)?;
    charge_mct_work(work, operations, limits)?;
    check_mct_scratch(
        count.checked_mul(3).ok_or_else(arithmetic_overflow)?,
        limits,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_offset_scaled(crate::codestream::mct_array_option(offsets), row),
))]
pub(super) fn offset_value_scaled(
    offsets: Option<&MctArray>,
    row: usize,
) -> Result<i128, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::codestream::mct_fixed_precision_is_q32();
        reveal(crate::specs::part2_mct_offset_scaled);
    }
    match offsets {
        Some(offsets) if offsets.fraction_bits() <= MCT_FIXED_BITS => rescale_i128(
            i128::from(*offsets.values().get(row).ok_or_else(invalid_transform)?),
            offsets.fraction_bits(),
            MCT_FIXED_BITS,
        ),
        Some(_) => Err(invalid_transform()),
        None => Ok(0),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, *final(work)) == crate::specs::part2_mct_charge_work(
        *old(work), operations, crate::limits::resource_work_limit(limits),
    ),
))]
pub(super) fn charge_mct_work(
    work: &mut u64,
    operations: u64,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    *work = work
        .checked_add(operations)
        .ok_or_else(arithmetic_overflow)?;
    if *work > limits.maximum_work_units() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: *work,
        });
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_image_byte_budget(values as nat, 8, crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub(super) fn check_mct_scratch(values: usize, limits: &ResourceLimits) -> Result<(), DecodeError> {
    let bytes = (values as u64)
        .checked_mul(core::mem::size_of::<i64>() as u64)
        .ok_or_else(arithmetic_overflow)?;
    if bytes > limits.maximum_decoded_bytes() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: limits.maximum_decoded_bytes(),
            actual: bytes,
        });
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_ceil_half(value),
))]
pub(super) fn ceil_divide_by_two(value: i64) -> Result<i64, DecodeError> {
    let quotient = value / 2;
    quotient
        .checked_add(if value % 2 > 0 { 1 } else { 0 })
        .ok_or_else(arithmetic_overflow)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_find_component(transform_components_view(components), reference),
))]
pub(super) fn find_transform_component(
    components: &[TransformComponentMut<'_>],
    reference: u16,
) -> Result<usize, DecodeError> {
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= components.len(),
            forall |earlier: int| 0 <= earlier < index ==> transform_components_view(components)[earlier].0 != reference,
            decreases components.len() - index,
        )
    )]
    while index < components.len() {
        let matches = match components.get(index) {
            Some(component) => component.component == reference,
            None => false,
        };
        if matches {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_mct_component_found(transform_components_view(components), reference, index);
            }
            return Ok(index);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |earlier: int| 0 <= earlier < index + 1 implies
                transform_components_view(components)[earlier].0 != reference by {
                if earlier == index { assert(transform_components_view(components)[earlier].0 != reference); }
            }
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_component_missing(transform_components_view(components), reference);
    }
    Err(invalid_transform())
}

#[cfg(any())]
fn apply_multiple_component_transform_legacy(
    image: &mut DecodedImage,
    transform: &MultipleComponentTransform,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    let components = transform.input_components().len();
    if components == 0
        || components != image.components.len()
        || transform.output_components().len() != components
        || transform.matrix().values().len()
            != components
                .checked_mul(components)
                .ok_or_else(arithmetic_overflow)?
    {
        return Err(invalid_transform());
    }
    let invalid_offset_dimensions = match transform.offsets() {
        Some(offsets) => offsets.values().len() != components,
        None => false,
    };
    if invalid_offset_dimensions {
        return Err(invalid_transform());
    }
    let first = image.components.first().ok_or_else(invalid_transform)?;
    let sample_count = first.samples.len();
    let expected_fraction_bits = if transform.reversible() {
        0
    } else {
        FIXED_BITS
    };
    let mut component = 0_usize;
    while component < components {
        let input_reference = *transform
            .input_components()
            .get(component)
            .ok_or_else(invalid_transform)?;
        let output_reference = *transform
            .output_components()
            .get(component)
            .ok_or_else(invalid_transform)?;
        if usize::from(input_reference) != component || usize::from(output_reference) != component {
            return Err(invalid_transform());
        }
        let current = image
            .components
            .get(component)
            .ok_or_else(invalid_transform)?;
        if current.width != first.width
            || current.height != first.height
            || current.samples.len() != sample_count
            || current.info.x_subsampling != first.info.x_subsampling
            || current.info.y_subsampling != first.info.y_subsampling
            || (transform.reversible() && current.fraction_bits != 0)
            || (!transform.reversible()
                && current.fraction_bits != 0
                && current.fraction_bits != FIXED_BITS)
        {
            return Err(invalid_transform());
        }
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let operations = (sample_count as u64)
        .checked_mul(components as u64)
        .and_then(|value| value.checked_mul(components as u64))
        .ok_or_else(arithmetic_overflow)?;
    if operations > limits.maximum_work_units() {
        return Err(DecodeError::limit(
            Resource::WorkUnits,
            limits.maximum_work_units(),
            operations,
        ));
    }

    let mut source = Vec::with_capacity(components);
    let mut output = Vec::with_capacity(components);
    let mut sample_index = 0_usize;
    while sample_index < sample_count {
        source.clear();
        output.clear();
        component = 0;
        while component < components {
            source.push(component_sample(image, component, sample_index)?);
            component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        let mut row = 0_usize;
        while row < components {
            let transformed = if transform.reversible() {
                reversible_mct_row(transform.matrix(), transform.offsets(), &source, row)?
            } else {
                fixed_mct_row(transform.matrix(), transform.offsets(), &source, image, row)?
            };
            output.push(transformed);
            row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        component = 0;
        while component < components {
            set_component_sample(
                image,
                component,
                sample_index,
                *output.get(component).ok_or_else(invalid_transform)?,
            )?;
            component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        sample_index = sample_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    component = 0;
    while component < components {
        image
            .components
            .get_mut(component)
            .ok_or_else(invalid_transform)?
            .fraction_bits = expected_fraction_bits;
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_reversible_mct_row(
        crate::codestream::mct_array_view(matrix), crate::codestream::mct_array_option(offsets), source@, row,
    ),
))]
pub(super) fn reversible_mct_row(
    matrix: &MctArray,
    offsets: Option<&MctArray>,
    source: &[i64],
    row: usize,
) -> Result<i64, DecodeError> {
    let floating_offsets = match offsets {
        Some(array) => array.fraction_bits() != 0,
        None => false,
    };
    if matrix.fraction_bits() != 0 || floating_offsets {
        return Err(invalid_transform());
    }
    let values = inverse_reversible_mct(matrix, source)?;
    reversible_mct_output(&values, offsets, row)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_reversible_mct_output(
        values@, crate::codestream::mct_array_option(offsets), row,
    ),
))]
pub(super) fn reversible_mct_output(
    values: &[i64],
    offsets: Option<&MctArray>,
    row: usize,
) -> Result<i64, DecodeError> {
    values
        .get(row)
        .ok_or_else(invalid_transform)?
        .checked_add(offset_value(offsets, row)?)
        .ok_or_else(arithmetic_overflow)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_reversible_mct_stage(
        crate::codestream::mct_array_view(matrix), source@, stage,
    ),
))]
pub(super) fn reversible_mct_stage(
    matrix: &MctArray,
    source: &[i64],
    stage: usize,
) -> Result<i64, DecodeError> {
    let width = source.len();
    if width == 0 || stage > width || matrix.fraction_bits() != 0 {
        return Err(invalid_transform());
    }
    let target = if stage == width {
        width - 1
    } else {
        width - 1 - stage
    };
    let row_start = stage.checked_mul(width).ok_or_else(arithmetic_overflow)?;
    let pivot_index = row_start
        .checked_add(target)
        .ok_or_else(arithmetic_overflow)?;
    let pivot = *matrix
        .values()
        .get(pivot_index)
        .ok_or_else(invalid_transform)?;
    let divisor = crate::codestream::reversible_mct_scale(pivot, stage == width)?;
    let mut sum = divisor / 2;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial = sum; }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_serm_sum_empty(
            initial, crate::codestream::mct_array_view(matrix), source@, row_start, target,
        );
    }
    let mut column = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant column <= width,
            width == source.len(),
            row_start as int == stage as int * width as int,
            width > 0,
            stage <= width,
            target as int == if stage == width { width as int - 1 } else { width as int - 1 - stage as int },
            pivot_index as int == row_start as int + target as int,
            pivot_index < crate::codestream::mct_array_view(matrix).4.len(),
            crate::codestream::mct_array_view(matrix).3 == 0,
            crate::codestream::mct_array_view(matrix).4[pivot_index as int] == pivot,
            crate::specs::part2_reversible_mct_scale(pivot, stage == width) == Ok(divisor),
            divisor > 0,
            initial == divisor / 2,
            crate::specs::part2_reversible_mct_sum(
                initial, crate::codestream::mct_array_view(matrix), source@, row_start, target, column as nat,
            ) == Ok(sum),
        decreases width - column,
    ))]
    while column < width {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_serm_sum_step(
                initial, crate::codestream::mct_array_view(matrix), source@, row_start, target, column as nat,
            );
            crate::proofs::production_impl::production_mct_serm_sum_error(
                initial, crate::codestream::mct_array_view(matrix), source@, row_start, target, column as nat + 1, width as nat,
            );
        }
        if column != target {
            let coefficient = *matrix
                .values()
                .get(
                    row_start
                        .checked_add(column)
                        .ok_or_else(arithmetic_overflow)?,
                )
                .ok_or_else(invalid_transform)?;
            let product = i128::from(coefficient)
                .checked_mul(i128::from(
                    *source.get(column).ok_or_else(invalid_transform)?,
                ))
                .ok_or_else(arithmetic_overflow)?;
            sum = sum.checked_add(product).ok_or_else(arithmetic_overflow)?;
        }
        column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let quotient = sum / divisor;
    let prediction = if sum % divisor < 0 {
        quotient.checked_sub(1).ok_or_else(arithmetic_overflow)?
    } else {
        quotient
    };
    let value = i128::from(*source.get(target).ok_or_else(invalid_transform)?)
        .checked_sub(prediction)
        .ok_or_else(arithmetic_overflow)?;
    let value = if pivot < 0 {
        0_i128.checked_sub(value).ok_or_else(arithmetic_overflow)?
    } else {
        value
    };
    match i64::try_from(value) {
        Ok(value) => Ok(value),
        Err(_) => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::transform::sequence_outcome(result) == crate::specs::part2_inverse_reversible_mct(
        crate::codestream::mct_array_view(matrix), source@,
    ),
))]
pub(super) fn inverse_reversible_mct(
    matrix: &MctArray,
    source: &[i64],
) -> Result<Vec<i64>, DecodeError> {
    if matrix.fraction_bits() != 0 {
        return Err(invalid_transform());
    }
    let count = source.len();
    crate::codestream::validate_reversible_mct_coefficients(matrix.values(), count)?;
    let stages = count.checked_add(1).ok_or_else(arithmetic_overflow)?;
    let mut values = Vec::with_capacity(count);
    values.extend_from_slice(source);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(values@ =~= source@);
        crate::proofs::production_impl::production_mct_serm_stages_empty(
            crate::codestream::mct_array_view(matrix), source@,
        );
    }
    let mut stage = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant stage <= stages,
            count > 0,
            count == source.len(),
            stages as int == count as int + 1,
            values@.len() == count,
            crate::codestream::mct_array_view(matrix).3 == 0,
            crate::specs::part2_validate_reversible_mct_coefficients(
                crate::codestream::mct_array_view(matrix).4, count,
            ) == Ok(()),
            crate::specs::part2_reversible_mct_stages(
                crate::codestream::mct_array_view(matrix), source@, stage as nat,
            ) == Ok(values@),
        decreases stages - stage,
    ))]
    while stage < stages {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_mct_serm_stages_step(
                crate::codestream::mct_array_view(matrix), source@, stage as nat,
            );
            crate::proofs::production_impl::production_mct_serm_stages_error(
                crate::codestream::mct_array_view(matrix), source@, stage as nat + 1, stages as nat,
            );
        }
        let target = if stage == count {
            count - 1
        } else {
            count - 1 - stage
        };
        let value = reversible_mct_stage(matrix, &values, stage)?;
        *values.get_mut(target).ok_or_else(invalid_transform)? = value;
        stage += 1;
    }
    Ok(values)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_matrix_row(
        crate::codestream::mct_array_view(matrix), crate::codestream::mct_array_option(offsets), source@, Some(source_fraction_bits@), row,
    ),
))]
pub(super) fn fixed_mct_row_scaled(
    matrix: &MctArray,
    offsets: Option<&MctArray>,
    source: &[i64],
    source_fraction_bits: &[u8],
    row: usize,
) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::mct_fixed_precision_is_q32(); }
    let invalid_offset_precision = match offsets {
        Some(array) => array.fraction_bits() > MCT_FIXED_BITS,
        None => false,
    };
    if source.len() != source_fraction_bits.len()
        || matrix.fraction_bits() > MCT_FIXED_BITS
        || invalid_offset_precision
    {
        return Err(invalid_transform());
    }
    let mut sum = match offsets {
        Some(array) => rescale_i128(
            i128::from(*array.values().get(row).ok_or_else(invalid_transform)?),
            array.fraction_bits(),
            MCT_FIXED_BITS,
        )?,
        None => 0,
    };
    let width = source.len();
    let row_start = row.checked_mul(width).ok_or_else(arithmetic_overflow)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial = sum; }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_dot_empty(initial, crate::codestream::mct_array_view(matrix), source@, Some(source_fraction_bits@), row_start);
    }
    let mut column = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant column <= width,
            width == source.len(),
            row_start as nat == row as nat * width as nat,
            crate::specs::part2_mct_row_initial(crate::codestream::mct_array_view(matrix), crate::codestream::mct_array_option(offsets), width as nat, Some(source_fraction_bits@), row) == Ok(initial),
            crate::specs::part2_mct_dot_prefix(initial, crate::codestream::mct_array_view(matrix), source@, Some(source_fraction_bits@), row_start, column as nat) == Ok(sum),
            decreases width - column,
        )
    )]
    while column < width {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::codestream::mct_fixed_precision_is_q32();
            crate::proofs::production_impl::production_mct_dot_step(initial, crate::codestream::mct_array_view(matrix), source@, Some(source_fraction_bits@), row_start, column as nat);
            crate::proofs::production_impl::production_mct_dot_error_guard(initial, crate::codestream::mct_array_view(matrix), source@, Some(source_fraction_bits@), row_start, column as nat + 1, width as nat);
        }
        let coefficient = *matrix
            .values()
            .get(
                row_start
                    .checked_add(column)
                    .ok_or_else(arithmetic_overflow)?,
            )
            .ok_or_else(invalid_transform)?;
        let sample = *source.get(column).ok_or_else(invalid_transform)?;
        let product_fraction_bits = matrix
            .fraction_bits()
            .checked_add(
                *source_fraction_bits
                    .get(column)
                    .ok_or_else(invalid_transform)?,
            )
            .ok_or_else(arithmetic_overflow)?;
        let product = i128::from(coefficient)
            .checked_mul(i128::from(sample))
            .ok_or_else(arithmetic_overflow)?;
        sum = sum
            .checked_add(rescale_i128(
                product,
                product_fraction_bits,
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_rescale(value, from_bits, to_bits),
))]
pub(super) fn rescale_i128(value: i128, from_bits: u8, to_bits: u8) -> Result<i128, DecodeError> {
    if from_bits == to_bits {
        return Ok(value);
    }
    if from_bits < to_bits {
        let shift = to_bits
            .checked_sub(from_bits)
            .ok_or_else(arithmetic_overflow)?;
        if shift > 126 {
            return Err(arithmetic_overflow());
        }
        return value
            .checked_mul(1_i128 << u32::from(shift))
            .ok_or_else(arithmetic_overflow);
    }
    rounded_shift_i128(
        value,
        from_bits
            .checked_sub(to_bits)
            .ok_or_else(arithmetic_overflow)?,
    )
}

#[cfg(any())]
fn fixed_mct_row(
    matrix: &MctArray,
    offsets: Option<&MctArray>,
    source: &[i64],
    image: &DecodedImage,
    row: usize,
) -> Result<i64, DecodeError> {
    let offset = match offsets {
        Some(array) => fixed_array_value(array, row)?,
        None => 0,
    };
    let mut sum = i128::from(offset)
        .checked_mul(1_i128 << u32::from(FIXED_BITS))
        .ok_or_else(arithmetic_overflow)?;
    let width = source.len();
    let row_start = row.checked_mul(width).ok_or_else(arithmetic_overflow)?;
    let mut column = 0_usize;
    while column < width {
        let coefficient = fixed_array_value(
            matrix,
            row_start
                .checked_add(column)
                .ok_or_else(arithmetic_overflow)?,
        )?;
        let sample = *source.get(column).ok_or_else(invalid_transform)?;
        let fraction_bits = image
            .components
            .get(column)
            .ok_or_else(invalid_transform)?
            .fraction_bits;
        let fixed_sample = if fraction_bits == 0 {
            sample
                .checked_mul(1_i64 << u32::from(FIXED_BITS))
                .ok_or_else(arithmetic_overflow)?
        } else {
            sample
        };
        sum = sum
            .checked_add(
                i128::from(coefficient)
                    .checked_mul(i128::from(fixed_sample))
                    .ok_or_else(arithmetic_overflow)?,
            )
            .ok_or_else(arithmetic_overflow)?;
        column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let rounded = rounded_shift_i128(sum, FIXED_BITS)?;
    i64::try_from(rounded).map_err(|_| arithmetic_overflow())
}

#[cfg(any())]
fn fixed_array_value(array: &MctArray, index: usize) -> Result<i64, DecodeError> {
    let value = *array.values().get(index).ok_or_else(invalid_transform)?;
    match array.fraction_bits() {
        0 => value
            .checked_mul(1_i64 << u32::from(FIXED_BITS))
            .ok_or_else(arithmetic_overflow),
        FIXED_BITS => Ok(value),
        _ => Err(invalid_transform()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_mct_round_shift(value, bits),
))]
pub(super) fn rounded_shift_i128(value: i128, bits: u8) -> Result<i128, DecodeError> {
    if bits == 0 {
        return Ok(value);
    }
    if bits > 126 {
        return Err(arithmetic_overflow());
    }
    let half = 1_i128 << u32::from(bits - 1);
    let divisor = 1_i128 << u32::from(bits);
    if divisor == 0 || divisor == -1 {
        return Err(arithmetic_overflow());
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((1i128 << (bits as u32)) > 0) by (bit_vector)
            requires bits > 0, bits <= 126;
        assert((1i128 << ((bits - 1) as u32)) > 0) by (bit_vector)
            requires bits > 0, bits <= 126;
    }
    if value < 0 {
        let magnitude = 0_i128.checked_sub(value).ok_or_else(arithmetic_overflow)?;
        let magnitude = magnitude
            .checked_add(half)
            .ok_or_else(arithmetic_overflow)?;
        let rounded = magnitude / divisor;
        0_i128.checked_sub(rounded).ok_or_else(arithmetic_overflow)
    } else {
        let rounded = value.checked_add(half).ok_or_else(arithmetic_overflow)?;
        Ok(rounded / divisor)
    }
}
