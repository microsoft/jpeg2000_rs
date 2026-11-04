//! Multiple-component-transform metadata, construction and equality.

use super::{
    MctArray, MctArrayKind, MctCollection, MctCollectionKind, MctCollectionReference,
    MctNumericFormat, MctParameters, MctRecord, MctStage, MctWavelet, MctWaveletType,
    MultipleComponentTransform,
};
#[cfg(verus_keep_ghost)]
use super::{
    mcc_collection_reference_view, mcc_collection_references_view, mct_array_option,
    mct_array_view, mct_arrays_view, mct_collection_view, mct_parameter_copy_view,
    mct_parameters_view, mct_record_view, mct_records_view, mct_stage_view, mct_wavelet_option,
    mct_wavelet_view, multiple_component_transform_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl MctArray {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == mct_array_view(self).0,))]
    pub const fn index(&self) -> u8 {
        self.index
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == mct_array_view(self).1,))]
    pub const fn kind(&self) -> MctArrayKind {
        self.kind
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == mct_array_view(self).2,))]
    pub const fn numeric_format(&self) -> MctNumericFormat {
        self.numeric_format
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == mct_array_view(self).3,))]
    pub const fn fraction_bits(&self) -> u8 {
        self.fraction_bits
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result@ == mct_array_view(self).4,))]
    pub fn values(&self) -> &[i64] {
        &self.values
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_mct_array_identity(mct_array_view(self), mct_array_view(other)),
    ))]
    pub fn equals(&self, other: &Self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(mct_array_view); }
        if self.index != other.index
            || !mct_array_kinds_equal(self.kind, other.kind)
            || !mct_numeric_formats_equal(self.numeric_format, other.numeric_format)
            || self.fraction_bits != other.fraction_bits
            || self.values.len() != other.values.len()
        {
            return false;
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.values.len(),
                    self.index == other.index, self.kind == other.kind, self.numeric_format == other.numeric_format,
                    self.fraction_bits == other.fraction_bits, self.values.len() == other.values.len(),
                    forall |i: int| 0 <= i < index ==> self.values@[i] == other.values@[i],
                decreases self.values.len() - index,
            )
        )]
        while index < self.values.len() {
            if self.values[index] != other.values[index] {
                return false;
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(self.values@ =~= other.values@); }
        true
    }

    #[cfg(test)]
    pub(crate) fn from_values(
        index: u8,
        kind: MctArrayKind,
        numeric_format: MctNumericFormat,
        fraction_bits: u8,
        values: Vec<i64>,
    ) -> Self {
        Self {
            index,
            kind,
            numeric_format,
            fraction_bits,
            values,
        }
    }
}
impl MultipleComponentTransform {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures Seq::new(result@.len(), |index: int| mct_stage_view(&result@[index]))
            == multiple_component_transform_view(self),
    ))]
    pub fn stages(&self) -> &[MctStage] {
        &self.stages
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_mct_identity(multiple_component_transform_view(self), multiple_component_transform_view(other)),
    ))]
    pub fn equals(&self, other: &Self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(multiple_component_transform_view); }
        if self.stages.len() != other.stages.len() {
            return false;
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.stages.len(),
                    self.stages.len() == other.stages.len(),
                    forall |i: int| 0 <= i < index ==> mct_stage_view(&self.stages@[i]) == mct_stage_view(&other.stages@[i]),
                decreases self.stages.len() - index,
            )
        )]
        while index < self.stages.len() {
            let Some(left) = self.stages.get(index) else {
                return false;
            };
            let Some(right) = other.stages.get(index) else {
                return false;
            };
            if !left.equals(right) {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(multiple_component_transform_view(self)[index as int]
                        != multiple_component_transform_view(other)[index as int]);
                }
                return false;
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(multiple_component_transform_view(self) =~= multiple_component_transform_view(other)); }
        true
    }

    #[cfg(test)]
    pub(crate) fn from_arrays(
        reversible: bool,
        components: u16,
        matrix: MctArray,
        offsets: Option<MctArray>,
    ) -> Self {
        let mut references = Vec::with_capacity(usize::from(components));
        let mut component = 0_u16;
        while component < components {
            references.push(component);
            component += 1;
        }
        Self {
            stages: vec![MctStage {
                index: 1,
                collections: vec![MctCollection {
                    reversible,
                    input_components: references.clone(),
                    output_components: references,
                    kind: MctCollectionKind::Decorrelation,
                    matrix: Some(matrix),
                    offsets,
                    wavelet: None,
                }],
            }],
        }
    }

    #[cfg(test)]
    pub(crate) fn from_stages(stages: Vec<MctStage>) -> Self {
        Self { stages }
    }
}
impl MctStage {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == mct_stage_view(self).0,))]
    pub const fn index(&self) -> u8 {
        self.index
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures Seq::new(result@.len(), |index: int| mct_collection_view(&result@[index])) == mct_stage_view(self).1,
    ))]
    pub fn collections(&self) -> &[MctCollection] {
        &self.collections
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_mct_stage_identity(mct_stage_view(self), mct_stage_view(other)),
    ))]
    pub fn equals(&self, other: &Self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(mct_stage_view);
            assert(mct_stage_view(self).1.len() == self.collections@.len());
            assert(mct_stage_view(other).1.len() == other.collections@.len());
        }
        if self.index != other.index || self.collections.len() != other.collections.len() {
            return false;
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.collections.len(),
                    self.index == other.index, self.collections.len() == other.collections.len(),
                    forall |i: int| 0 <= i < index ==> mct_collection_view(&self.collections@[i]) == mct_collection_view(&other.collections@[i]),
                decreases self.collections.len() - index,
            )
        )]
        while index < self.collections.len() {
            let Some(left) = self.collections.get(index) else {
                return false;
            };
            let Some(right) = other.collections.get(index) else {
                return false;
            };
            if !left.equals(right) {
                #[cfg(verus_keep_ghost)]
                proof! { assert(mct_stage_view(self).1[index as int] != mct_stage_view(other).1[index as int]); }
                return false;
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(mct_stage_view(self).1 =~= mct_stage_view(other).1); }
        true
    }

    #[cfg(test)]
    pub(crate) fn from_collections(index: u8, collections: Vec<MctCollection>) -> Self {
        Self { index, collections }
    }
}
impl MctCollection {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == mct_collection_view(self).0,))]
    pub const fn reversible(&self) -> bool {
        self.reversible
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result@ == mct_collection_view(self).1,))]
    pub fn input_components(&self) -> &[u16] {
        &self.input_components
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result@ == mct_collection_view(self).2,))]
    pub fn output_components(&self) -> &[u16] {
        &self.output_components
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == mct_collection_view(self).3,))]
    pub const fn kind(&self) -> MctCollectionKind {
        self.kind
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures mct_array_option(result) == mct_collection_view(self).4,))]
    pub const fn matrix(&self) -> Option<&MctArray> {
        self.matrix.as_ref()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures mct_array_option(result) == mct_collection_view(self).5,))]
    pub const fn offsets(&self) -> Option<&MctArray> {
        self.offsets.as_ref()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures mct_wavelet_option(result) == mct_collection_view(self).6,))]
    pub const fn wavelet(&self) -> Option<MctWavelet> {
        self.wavelet
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_mct_collection_identity(mct_collection_view(self), mct_collection_view(other)),
    ))]
    pub fn equals(&self, other: &Self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(mct_collection_view); }
        if self.reversible != other.reversible
            || !u16_lists_equal(&self.input_components, &other.input_components)
            || !u16_lists_equal(&self.output_components, &other.output_components)
            || !mct_collection_kinds_equal(self.kind, other.kind)
        {
            return false;
        }
        let matrices_equal = match (&self.matrix, &other.matrix) {
            (Some(left), Some(right)) => left.equals(right),
            (None, None) => true,
            _ => false,
        };
        let offsets_equal = match (&self.offsets, &other.offsets) {
            (Some(left), Some(right)) => left.equals(right),
            (None, None) => true,
            _ => false,
        };
        matrices_equal && offsets_equal && mct_wavelets_equal(self.wavelet, other.wavelet)
    }

    #[cfg(test)]
    pub(crate) fn from_arrays(
        reversible: bool,
        input_components: Vec<u16>,
        output_components: Vec<u16>,
        matrix: MctArray,
        offsets: Option<MctArray>,
    ) -> Self {
        Self {
            reversible,
            input_components,
            output_components,
            kind: MctCollectionKind::Decorrelation,
            matrix: Some(matrix),
            offsets,
            wavelet: None,
        }
    }

    #[cfg(test)]
    pub(crate) fn from_dependency(
        reversible: bool,
        components: Vec<u16>,
        coefficients: Option<MctArray>,
        offsets: Option<MctArray>,
    ) -> Self {
        Self {
            reversible,
            input_components: components.clone(),
            output_components: components,
            kind: MctCollectionKind::Dependency,
            matrix: coefficients,
            offsets,
            wavelet: None,
        }
    }

    #[cfg(test)]
    pub(crate) fn from_wavelet(
        input_components: Vec<u16>,
        output_components: Vec<u16>,
        transform: MctWaveletType,
        levels: u8,
        component_offset: i32,
    ) -> Self {
        Self {
            reversible: matches!(transform, MctWaveletType::Reversible5x3),
            input_components,
            output_components,
            kind: MctCollectionKind::Wavelet,
            matrix: None,
            offsets: None,
            wavelet: Some(MctWavelet {
                transform,
                levels,
                component_offset,
            }),
        }
    }
}
impl MctWavelet {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == mct_wavelet_view(self).0,))]
    pub const fn transform(self) -> MctWaveletType {
        self.transform
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == mct_wavelet_view(self).1,))]
    pub const fn levels(self) -> u8 {
        self.levels
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == mct_wavelet_view(self).2,))]
    pub const fn component_offset(self) -> i32 {
        self.component_offset
    }
}
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (left == right),))]
const fn mct_collection_kinds_equal(left: MctCollectionKind, right: MctCollectionKind) -> bool {
    matches!(
        (left, right),
        (MctCollectionKind::Dependency, MctCollectionKind::Dependency)
            | (
                MctCollectionKind::Decorrelation,
                MctCollectionKind::Decorrelation
            )
            | (MctCollectionKind::Wavelet, MctCollectionKind::Wavelet)
    )
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == (mct_wavelet_option(left) == mct_wavelet_option(right)),
))]
const fn mct_wavelets_equal(left: Option<MctWavelet>, right: Option<MctWavelet>) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(mct_wavelet_view); }
    match (left, right) {
        (Some(left), Some(right)) => {
            mct_wavelet_types_equal(left.transform, right.transform)
                && left.levels == right.levels
                && left.component_offset == right.component_offset
        }
        (None, None) => true,
        _ => false,
    }
}
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (left == right),))]
const fn mct_wavelet_types_equal(left: MctWaveletType, right: MctWaveletType) -> bool {
    matches!(
        (left, right),
        (
            MctWaveletType::Irreversible9x7,
            MctWaveletType::Irreversible9x7
        ) | (MctWaveletType::Reversible5x3, MctWaveletType::Reversible5x3)
    )
}
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (left == right),))]
pub(super) const fn mct_array_kinds_equal(left: MctArrayKind, right: MctArrayKind) -> bool {
    matches!(
        (left, right),
        (MctArrayKind::Dependency, MctArrayKind::Dependency)
            | (MctArrayKind::Decorrelation, MctArrayKind::Decorrelation)
            | (MctArrayKind::Offset, MctArrayKind::Offset)
    )
}
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (left == right),))]
const fn mct_numeric_formats_equal(left: MctNumericFormat, right: MctNumericFormat) -> bool {
    matches!(
        (left, right),
        (MctNumericFormat::Int16, MctNumericFormat::Int16)
            | (MctNumericFormat::Int32, MctNumericFormat::Int32)
            | (MctNumericFormat::Float32, MctNumericFormat::Float32)
            | (MctNumericFormat::Float64, MctNumericFormat::Float64)
    )
}
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (left@ == right@),))]
pub(super) fn u16_lists_equal(left: &[u16], right: &[u16]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= left.len(),
                left.len() == right.len(),
                forall |i: int| 0 <= i < index ==> left@[i] == right@[i],
            decreases left.len() - index,
        )
    )]
    while index < left.len() {
        if left[index] != right[index] {
            return false;
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(left@ =~= right@); }
    true
}
// Match the original derives' field order and Copy-field clone calls.
#[allow(clippy::clone_on_copy)]
impl Clone for MctCollectionReference {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures mcc_collection_reference_view(&result)
            == crate::specs::part1_mcc_collection_reference_copy(mcc_collection_reference_view(self)),
    ))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(mcc_collection_reference_view); }
        Self {
            input_components: Clone::clone(&self.input_components),
            output_components: Clone::clone(&self.output_components),
            transform: Clone::clone(&self.transform),
        }
    }
}

#[allow(clippy::clone_on_copy)]
impl Clone for MctRecord {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures mct_record_view(&result)
            == crate::specs::part1_mct_record_copy(mct_record_view(self)),
    ))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(mct_record_view);
            reveal(mcc_collection_references_view);
            reveal(crate::specs::part1_mct_record_copy);
        }
        Self {
            index: Clone::clone(&self.index),
            collections: Clone::clone(&self.collections),
        }
    }
}

impl Clone for MctParameters {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures mct_parameter_copy_view(&result)
            == crate::specs::part1_mct_parameters_copy(mct_parameter_copy_view(self)),
    ))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(mct_parameters_view);
            reveal(mct_parameter_copy_view);
            reveal(mct_arrays_view);
            reveal(mct_records_view);
            reveal(crate::specs::part1_mct_parameters_copy);
            reveal(crate::specs::part1_mct_record_copy);
        }
        Self {
            arrays: Clone::clone(&self.arrays),
            records: Clone::clone(&self.records),
            order: Clone::clone(&self.order),
        }
    }
}

impl Clone for MctArray {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures mct_array_view(&result) == mct_array_view(self),))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(mct_array_view); }
        Self {
            index: self.index,
            kind: self.kind,
            numeric_format: self.numeric_format,
            fraction_bits: self.fraction_bits,
            values: self.values.clone(),
        }
    }
}
impl Clone for MctCollection {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures mct_collection_view(&result) == mct_collection_view(self),))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(mct_collection_view); }
        Self {
            reversible: self.reversible,
            input_components: self.input_components.clone(),
            output_components: self.output_components.clone(),
            kind: self.kind,
            matrix: self.matrix.clone(),
            offsets: self.offsets.clone(),
            wavelet: self.wavelet,
        }
    }
}
impl Clone for MctStage {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures mct_stage_view(&result) == mct_stage_view(self),))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(mct_stage_view); }
        Self {
            index: self.index,
            collections: self.collections.clone(),
        }
    }
}
impl Clone for MultipleComponentTransform {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures multiple_component_transform_view(&result) == multiple_component_transform_view(self),))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(multiple_component_transform_view); }
        Self {
            stages: self.stages.clone(),
        }
    }
}
