//! Fallible deep copies for the reached cold-parser MCT parameter owner.

use super::{
    DecodeError, MctArray, MctCollection, MctCollectionReference, MctCopyPath, MctParameters,
    MctRecord, MctStage, MultipleComponentTransform, ResolvedCopyContext, ResolvedCopyPath,
    ResolvedCopyRole,
};
#[cfg(verus_keep_ghost)]
use super::{
    mcc_collection_reference_view, mcc_collection_references_view, mct_array_view, mct_arrays_view,
    mct_collection_view, mct_collections_view, mct_parameter_copy_view, mct_parameters_view,
    mct_record_view, mct_records_view, mct_stage_view, mct_stages_view,
    multiple_component_transform_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) open spec fn copy_outcome<T>(result: Result<T, DecodeError>) -> Result<(), DecodeError> {
        match result { Err(error) => Err(error), Ok(_) => Ok(()) }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::storage_copy_result(source@, result),
        crate::specs::part1_mct_copy_result(
            crate::specs::part1_mct_copy_leaf(_path, source.len()), copy_outcome(result)),
))]
fn copy_values_for<T: Copy>(source: &[T], _path: MctCopyPath) -> Result<Vec<T>, DecodeError> {
    let result = crate::allocation::copy_values(source);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part1_mct_copy_observed(_path, source.len(), copy_outcome(result));
    }
    result
}

impl MultipleComponentTransform {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_mct_transform_duplicate_requests(multiple_component_transform_view(self)), copy_outcome(result)),
            match result { Err(error) => error == DecodeError::AllocationFailed,
                Ok(value) => multiple_component_transform_view(&value) == multiple_component_transform_view(self) },
    ))]
    pub(super) fn try_duplicate(&self) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost source = multiple_component_transform_view(self);
            let ghost all = crate::specs::part1_mct_transform_duplicate_requests(source);
            let ghost mut done = crate::specs::part1_mct_copy_leaf(
                MctCopyPath::Resolved(ResolvedCopyPath::Stages(ResolvedCopyRole::Tile)), self.stages.len());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(multiple_component_transform_view); reveal(mct_stages_view); reveal(copy_outcome);
            crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        }
        let reserved = reserve_values(
            self.stages.len(),
            MctCopyPath::Resolved(ResolvedCopyPath::Stages(ResolvedCopyRole::Tile)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_mct_copy_continue(Seq::empty(), done,
                crate::specs::part1_mct_stages_duplicate_requests(source, 0), copy_outcome(reserved));
            assert((Seq::empty() + done) + crate::specs::part1_mct_stages_duplicate_requests(source, 0) =~= all);
        }
        let mut stages = reserved?;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= self.stages.len(), source == multiple_component_transform_view(self),
                all == crate::specs::part1_mct_transform_duplicate_requests(source),
                mct_stages_view(stages@) == source.take(index as int),
                crate::specs::part1_mct_copy_result(done, Ok(())),
                all == done + crate::specs::part1_mct_stages_duplicate_requests(source, index as nat),
            decreases self.stages.len() - index,
        ))]
        while index < self.stages.len() {
            let copied = self.stages[index].try_duplicate(index);
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_mct_stages_duplicate_requests, 1);
                let step = crate::specs::part1_mct_stage_duplicate_requests(source[index as int], index);
                let rest = crate::specs::part1_mct_stages_duplicate_requests(source, index as nat + 1);
                crate::specs::part1_mct_copy_continue(done, step, rest, copy_outcome(copied));
                assert(done + (step + rest) =~= (done + step) + rest);
                done = done + step;
            }
            let value = copied?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous = stages@;
                let ghost copied_view = mct_stage_view(&value);
            }
            stages.push(value);
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(mct_stages_view);
                assert(mct_stages_view(stages@) =~= mct_stages_view(previous).push(copied_view));
                assert(source.take(index as int + 1) =~= source.take(index as int).push(source[index as int]));
                assert(mct_stages_view(stages@) =~= source.take(index as int + 1));
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_mct_stages_duplicate_requests, 1);
            assert(all =~= done); assert(source.take(index as int) =~= source);
        }
        Ok(Self { stages })
    }
}

impl MctStage {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_mct_stage_duplicate_requests(mct_stage_view(self), stage), copy_outcome(result)),
            match result { Err(error) => error == DecodeError::AllocationFailed,
                Ok(value) => mct_stage_view(&value) == mct_stage_view(self) },
    ))]
    fn try_duplicate(&self, stage: usize) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost source = mct_stage_view(self);
            let ghost all = crate::specs::part1_mct_stage_duplicate_requests(source, stage);
            let ghost mut done = crate::specs::part1_mct_copy_leaf(MctCopyPath::Resolved(
                ResolvedCopyPath::Collections(ResolvedCopyRole::Tile, stage, self.index as usize)), self.collections.len());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(mct_stage_view); reveal(mct_collections_view); reveal(copy_outcome);
            crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        }
        let reserved = reserve_values(
            self.collections.len(),
            MctCopyPath::Resolved(ResolvedCopyPath::Collections(
                ResolvedCopyRole::Tile,
                stage,
                usize::from(self.index),
            )),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_mct_copy_continue(Seq::empty(), done,
                crate::specs::part1_mct_collections_duplicate_requests(source.1, stage, source.0, 0), copy_outcome(reserved));
            assert((Seq::empty() + done) + crate::specs::part1_mct_collections_duplicate_requests(source.1, stage, source.0, 0) =~= all);
        }
        let mut collections = reserved?;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= self.collections.len(), source == mct_stage_view(self),
                all == crate::specs::part1_mct_stage_duplicate_requests(source, stage),
                mct_collections_view(collections@) == source.1.take(index as int),
                crate::specs::part1_mct_copy_result(done, Ok(())),
                all == done + crate::specs::part1_mct_collections_duplicate_requests(source.1, stage, source.0, index as nat),
            decreases self.collections.len() - index,
        ))]
        while index < self.collections.len() {
            let context = ResolvedCopyContext {
                role: ResolvedCopyRole::Tile,
                stage,
                record: usize::from(self.index),
                collection: index,
            };
            let copied = self.collections[index].try_duplicate(context);
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_mct_collections_duplicate_requests, 1);
                let step = crate::specs::part1_mct_collection_duplicate_tail(source.1[index as int], context, 0);
                let rest = crate::specs::part1_mct_collections_duplicate_requests(source.1, stage, source.0, index as nat + 1);
                crate::specs::part1_mct_copy_continue(done, step, rest, copy_outcome(copied));
                assert(done + (step + rest) =~= (done + step) + rest);
                done = done + step;
            }
            let value = copied?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous = collections@;
                let ghost copied_view = mct_collection_view(&value);
            }
            collections.push(value);
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(mct_collections_view);
                assert(mct_collections_view(collections@) =~= mct_collections_view(previous).push(copied_view));
                assert(source.1.take(index as int + 1) =~= source.1.take(index as int).push(source.1[index as int]));
                assert(mct_collections_view(collections@) =~= source.1.take(index as int + 1));
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_mct_collections_duplicate_requests, 1);
            assert(all =~= done); assert(source.1.take(index as int) =~= source.1);
        }
        Ok(Self {
            index: self.index,
            collections,
        })
    }
}

impl MctCollection {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_mct_collection_duplicate_tail(mct_collection_view(self), context, 0), copy_outcome(result)),
            match result { Err(error) => error == DecodeError::AllocationFailed,
                Ok(value) => mct_collection_view(&value) == mct_collection_view(self) },
    ))]
    fn try_duplicate(&self, context: ResolvedCopyContext) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost source = mct_collection_view(self);
            let ghost mut done = Seq::<crate::specs::Part1MctCopyRequest>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(mct_collection_view); reveal(mct_array_view); reveal(copy_outcome);
            crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
            assert(done + crate::specs::part1_mct_collection_duplicate_tail(source, context, 0)
                =~= crate::specs::part1_mct_collection_duplicate_tail(source, context, 0));
        }
        let copied = copy_values_for(
            &self.input_components,
            MctCopyPath::Resolved(ResolvedCopyPath::Inputs(context)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            done = crate::specs::part1_mct_collection_duplicate_advance(source, context, 0, done, copy_outcome(copied));
        }
        let input_components = copied?;
        let copied = copy_values_for(
            &self.output_components,
            MctCopyPath::Resolved(ResolvedCopyPath::Outputs(context)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            done = crate::specs::part1_mct_collection_duplicate_advance(source, context, 1, done, copy_outcome(copied));
        }
        let output_components = copied?;
        let copied = match &self.matrix {
            None => Ok(None),
            Some(array) => match array.try_duplicate_for(MctCopyPath::Resolved(
                ResolvedCopyPath::Matrix(context, array.index),
            )) {
                Err(error) => Err(error),
                Ok(value) => Ok(Some(value)),
            },
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            done = crate::specs::part1_mct_collection_duplicate_advance(source, context, 2, done, copy_outcome(copied));
        }
        let matrix = copied?;
        let copied = match &self.offsets {
            None => Ok(None),
            Some(array) => match array.try_duplicate_for(MctCopyPath::Resolved(
                ResolvedCopyPath::Offsets(context, array.index),
            )) {
                Err(error) => Err(error),
                Ok(value) => Ok(Some(value)),
            },
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            done = crate::specs::part1_mct_collection_duplicate_advance(source, context, 3, done, copy_outcome(copied));
        }
        let offsets = copied?;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_mct_collection_duplicate_tail, 1);
            assert(done =~= crate::specs::part1_mct_collection_duplicate_tail(source, context, 0));
        }
        Ok(Self {
            reversible: self.reversible,
            input_components,
            output_components,
            kind: self.kind,
            matrix,
            offsets,
            wavelet: self.wavelet,
        })
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part1_mct_copy_result(crate::specs::part1_mct_copy_leaf(_path, count), copy_outcome(result)),
        match result { Ok(values) => values@.len() == 0, Err(error) => error == DecodeError::AllocationFailed },
))]
pub(super) fn reserve_values<T>(count: usize, _path: MctCopyPath) -> Result<Vec<T>, DecodeError> {
    let result = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(copy_outcome);
        crate::specs::part1_mct_copy_observed(_path, count, copy_outcome(result));
    }
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part1_mct_copy_result(crate::specs::part1_mct_copy_leaf(_path, count), copy_outcome(result)),
        match result { Ok(values) => values@ == Seq::new(count as nat, |_: int| value),
            Err(error) => error == DecodeError::AllocationFailed },
))]
pub(super) fn filled_values<T: Copy>(
    value: T,
    count: usize,
    _path: MctCopyPath,
) -> Result<Vec<T>, DecodeError> {
    let mut values = reserve_values(count, _path)?;
    #[cfg(verus_keep_ghost)]
    proof! { assert(values@ =~= Seq::<T>::empty()); }
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= count, values@ == Seq::new(index as nat, |_: int| value),
            crate::specs::part1_mct_copy_result(crate::specs::part1_mct_copy_leaf(_path, count), Ok(())),
        decreases count - index,
    ))]
    while index < count {
        values.push(value);
        #[cfg(verus_keep_ghost)]
        proof! { assert(Seq::new(index as nat + 1, |_: int| value) =~= Seq::new(index as nat, |_: int| value).push(value)); }
        index += 1;
    }
    Ok(values)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part1_mct_copy_result(
        crate::specs::part1_mct_copy_leaf(_path, source.len()), copy_outcome(result)),
        match result { Ok(values) => values@ == source@, Err(error) => error == DecodeError::AllocationFailed },
))]
pub(super) fn copy_flat<T: Copy>(source: &[T], _path: MctCopyPath) -> Result<Vec<T>, DecodeError> {
    let result = crate::allocation::copy_values(source);
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(copy_outcome);
        crate::specs::part1_mct_copy_observed(_path, source.len(), copy_outcome(result));
    }
    result
}

impl MctArray {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_mct_copy_leaf(_path, mct_array_view(self).4.len() as usize), copy_outcome(result)),
            match result { Ok(value) => mct_array_view(&value) == mct_array_view(self),
                Err(error) => error == DecodeError::AllocationFailed },
    ))]
    pub(super) fn try_duplicate_for(&self, _path: MctCopyPath) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(mct_array_view); }
        let index = self.index;
        let kind = self.kind;
        let numeric_format = self.numeric_format;
        let fraction_bits = self.fraction_bits;
        let values = copy_flat(&self.values, _path)?;
        Ok(Self {
            index,
            kind,
            numeric_format,
            fraction_bits,
            values,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_mct_array_copy_requests(mct_array_view(self), _position), copy_outcome(result)),
            match result { Ok(value) => mct_array_view(&value) == mct_array_view(self),
                Err(error) => error == DecodeError::AllocationFailed },
    ))]
    fn try_duplicate_at(&self, _position: usize) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(mct_array_view); reveal(copy_outcome); }
        let index = self.index;
        let kind = self.kind;
        let numeric_format = self.numeric_format;
        let fraction_bits = self.fraction_bits;
        let values = copy_flat(&self.values, MctCopyPath::ArrayValues(_position))?;
        Ok(Self {
            index,
            kind,
            numeric_format,
            fraction_bits,
            values,
        })
    }
}

impl MctCollectionReference {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(crate::specs::part1_mct_collection_copy_requests(
            mcc_collection_reference_view(self), _record, _position), copy_outcome(result)),
            match result { Ok(value) => mcc_collection_reference_view(&value) == mcc_collection_reference_view(self),
                Err(error) => error == DecodeError::AllocationFailed },
    ))]
    fn try_duplicate_at(&self, _record: usize, _position: usize) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost first = crate::specs::part1_mct_copy_leaf(MctCopyPath::Inputs(_record, _position), self.input_components.len());
            let ghost last = crate::specs::part1_mct_copy_leaf(MctCopyPath::Outputs(_record, _position), self.output_components.len());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(mcc_collection_reference_view); reveal(copy_outcome);
            crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        }
        let input = copy_flat(
            &self.input_components,
            MctCopyPath::Inputs(_record, _position),
        );
        #[cfg(verus_keep_ghost)]
        proof! { crate::specs::part1_mct_copy_continue(Seq::empty(), first, last, copy_outcome(input)); }
        let input_components = input?;
        let output = copy_flat(
            &self.output_components,
            MctCopyPath::Outputs(_record, _position),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(Seq::<crate::specs::Part1MctCopyRequest>::empty() + first =~= first);
            crate::specs::part1_mct_copy_continue(first, last, Seq::empty(), copy_outcome(output));
            assert((first + last) + Seq::<crate::specs::Part1MctCopyRequest>::empty() =~= first + last);
        }
        let output_components = output?;
        Ok(Self {
            input_components,
            output_components,
            transform: self.transform,
        })
    }
}

impl MctRecord {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_mct_record_copy_requests(mct_record_view(self), _position), copy_outcome(result)),
            match result { Ok(value) => mct_record_view(&value) == mct_record_view(self),
                Err(error) => error == DecodeError::AllocationFailed },
    ))]
    fn try_duplicate_at(&self, _position: usize) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(mct_record_view); reveal(mcc_collection_references_view); reveal(copy_outcome);
            crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        }
        let index = self.index;
        let reserved = reserve_values(self.collections.len(), MctCopyPath::Collections(_position));
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost all = crate::specs::part1_mct_record_copy_requests(mct_record_view(self), _position);
            let ghost mut done = crate::specs::part1_mct_copy_leaf(MctCopyPath::Collections(_position), self.collections.len());
            let ghost source = mcc_collection_references_view(self.collections@);
        }
        #[cfg(verus_keep_ghost)]
        proof! { crate::specs::part1_mct_copy_continue(Seq::empty(), done,
        crate::specs::part1_mct_collections_copy_requests(source, _position, 0), copy_outcome(reserved)); }
        let mut collections: Vec<MctCollectionReference> = reserved?;
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= self.collections.len(),
                source == mcc_collection_references_view(self.collections@),
                mcc_collection_references_view(collections@) == source.take(position as int),
                all == crate::specs::part1_mct_record_copy_requests(mct_record_view(self), _position),
                all == done + crate::specs::part1_mct_collections_copy_requests(source, _position, position as nat),
                crate::specs::part1_mct_copy_result(done, Ok(())),
            decreases self.collections.len() - position,
        ))]
        while position < self.collections.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_mct_collections_copy_requests, 1);
                reveal(mcc_collection_references_view);
            }
            let copied = self.collections[position].try_duplicate_at(_position, position);
            #[cfg(verus_keep_ghost)]
            proof! {
                let step = crate::specs::part1_mct_collection_copy_requests(source[position as int], _position, position);
                let suffix = crate::specs::part1_mct_collections_copy_requests(source, _position, position as nat + 1);
                crate::specs::part1_mct_copy_continue(done, step, suffix, copy_outcome(copied));
                assert((done + step) + suffix =~= done + (step + suffix));
            }
            let value = copied?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous = collections@;
                let ghost copied_view = mcc_collection_reference_view(&value);
            }
            collections.push(value);
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(mcc_collection_references_view);
                assert(mcc_collection_references_view(collections@) =~=
                    mcc_collection_references_view(previous).push(copied_view));
                assert(source.take(position as int + 1) =~= source.take(position as int).push(source[position as int]));
                done = done + crate::specs::part1_mct_collection_copy_requests(source[position as int], _position, position);
                assert(mcc_collection_references_view(collections@) =~= source.take(position as int + 1));
            }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_mct_collections_copy_requests, 1);
            assert(all =~= done); assert(source.take(position as int) =~= source);
        }
        Ok(Self { index, collections })
    }
}

impl MctParameters {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_mct_owner_copy_requests(mct_parameter_copy_view(self)), copy_outcome(result)),
            match result { Ok(value) => mct_parameter_copy_view(&value) == mct_parameter_copy_view(self),
                Err(error) => error == DecodeError::AllocationFailed },
    ))]
    pub(super) fn try_duplicate(&self) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(mct_parameter_copy_view); reveal(mct_parameters_view);
            reveal(mct_arrays_view); reveal(mct_records_view); reveal(copy_outcome);
            crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost source = mct_parameter_copy_view(self);
            let ghost all = crate::specs::part1_mct_owner_copy_requests(source);
            let ghost records_tail = crate::specs::part1_mct_copy_leaf(MctCopyPath::Records, self.records.len())
                + crate::specs::part1_mct_records_copy_requests(source.1, 0)
                + crate::specs::part1_mct_copy_leaf(MctCopyPath::Order, self.order.len());
            let ghost mut done = crate::specs::part1_mct_copy_leaf(MctCopyPath::Arrays, self.arrays.len());
        }
        let reserved = reserve_values(self.arrays.len(), MctCopyPath::Arrays);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_mct_copy_continue(Seq::empty(), done,
                crate::specs::part1_mct_arrays_copy_requests(source.0, 0) + records_tail, copy_outcome(reserved));
            assert(all =~= done + (crate::specs::part1_mct_arrays_copy_requests(source.0, 0) + records_tail));
        }
        let mut arrays: Vec<MctArray> = reserved?;
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= self.arrays.len(), source == mct_parameter_copy_view(self),
                mct_arrays_view(arrays@) == source.0.take(position as int),
                all == crate::specs::part1_mct_owner_copy_requests(source),
                records_tail == crate::specs::part1_mct_copy_leaf(MctCopyPath::Records, self.records.len())
                    + crate::specs::part1_mct_records_copy_requests(source.1, 0)
                    + crate::specs::part1_mct_copy_leaf(MctCopyPath::Order, self.order.len()),
                all == done + (crate::specs::part1_mct_arrays_copy_requests(source.0, position as nat) + records_tail),
                crate::specs::part1_mct_copy_result(done, Ok(())),
            decreases self.arrays.len() - position,
        ))]
        while position < self.arrays.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_mct_arrays_copy_requests, 1);
                reveal(mct_parameter_copy_view); reveal(mct_parameters_view); reveal(mct_arrays_view);
            }
            let copied = self.arrays[position].try_duplicate_at(position);
            #[cfg(verus_keep_ghost)]
            proof! {
                let step = crate::specs::part1_mct_array_copy_requests(source.0[position as int], position);
                let suffix = crate::specs::part1_mct_arrays_copy_requests(source.0, position as nat + 1) + records_tail;
                crate::specs::part1_mct_copy_continue(done, step, suffix, copy_outcome(copied));
                assert(all =~= (done + step) + suffix);
            }
            let value = copied?;
            #[cfg(verus_keep_ghost)]
            proof! { assert(mct_array_view(&value) == source.0[position as int]); }
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous = arrays@;
                let ghost copied_view = mct_array_view(&value);
            }
            arrays.push(value);
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(mct_arrays_view);
                assert(mct_arrays_view(arrays@) =~= mct_arrays_view(previous).push(copied_view));
                assert(source.0.take(position as int + 1) =~= source.0.take(position as int).push(source.0[position as int]));
                done = done + crate::specs::part1_mct_array_copy_requests(source.0[position as int], position);
                assert(mct_arrays_view(arrays@) =~= source.0.take(position as int + 1));
            }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_mct_arrays_copy_requests, 1);
            assert(all =~= done + records_tail); assert(source.0.take(position as int) =~= source.0);
        }
        let reserved = reserve_values(self.records.len(), MctCopyPath::Records);
        #[cfg(verus_keep_ghost)]
        proof! {
            let step = crate::specs::part1_mct_copy_leaf(MctCopyPath::Records, self.records.len());
            let suffix = crate::specs::part1_mct_records_copy_requests(source.1, 0)
                + crate::specs::part1_mct_copy_leaf(MctCopyPath::Order, self.order.len());
            crate::specs::part1_mct_copy_continue(done, step, suffix, copy_outcome(reserved));
            assert(all =~= (done + step) + suffix);
            done = done + step;
        }
        let mut records: Vec<MctRecord> = reserved?;
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= self.records.len(), source == mct_parameter_copy_view(self),
                mct_arrays_view(arrays@) == source.0,
                mct_records_view(records@) == source.1.take(position as int),
                all == crate::specs::part1_mct_owner_copy_requests(source),
                all == done + (crate::specs::part1_mct_records_copy_requests(source.1, position as nat)
                    + crate::specs::part1_mct_copy_leaf(MctCopyPath::Order, self.order.len())),
                crate::specs::part1_mct_copy_result(done, Ok(())),
            decreases self.records.len() - position,
        ))]
        while position < self.records.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_mct_records_copy_requests, 1);
                reveal(mct_parameter_copy_view); reveal(mct_parameters_view); reveal(mct_records_view);
            }
            let copied = self.records[position].try_duplicate_at(position);
            #[cfg(verus_keep_ghost)]
            proof! {
                let step = crate::specs::part1_mct_record_copy_requests(source.1[position as int], position);
                let suffix = crate::specs::part1_mct_records_copy_requests(source.1, position as nat + 1)
                    + crate::specs::part1_mct_copy_leaf(MctCopyPath::Order, self.order.len());
                crate::specs::part1_mct_copy_continue(done, step, suffix, copy_outcome(copied));
                assert(all =~= (done + step) + suffix);
            }
            let value = copied?;
            #[cfg(verus_keep_ghost)]
            proof! { assert(mct_record_view(&value) == source.1[position as int]); }
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous = records@;
                let ghost copied_view = mct_record_view(&value);
            }
            records.push(value);
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(mct_records_view);
                assert(mct_records_view(records@) =~= mct_records_view(previous).push(copied_view));
                assert(source.1.take(position as int + 1) =~= source.1.take(position as int).push(source.1[position as int]));
                done = done + crate::specs::part1_mct_record_copy_requests(source.1[position as int], position);
                assert(mct_records_view(records@) =~= source.1.take(position as int + 1));
            }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_mct_records_copy_requests, 1);
            assert(all =~= done + crate::specs::part1_mct_copy_leaf(MctCopyPath::Order, self.order.len()));
            assert(source.1.take(position as int) =~= source.1);
        }
        let copied = copy_flat(&self.order, MctCopyPath::Order);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_mct_copy_continue(done,
                crate::specs::part1_mct_copy_leaf(MctCopyPath::Order, self.order.len()), Seq::empty(), copy_outcome(copied));
            assert(all + Seq::<crate::specs::Part1MctCopyRequest>::empty() =~= all);
        }
        let order = copied?;
        Ok(Self {
            arrays,
            records,
            order,
        })
    }
}
