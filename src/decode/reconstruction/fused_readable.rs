use crate::DecodeError;
use crate::tier1::{CodeBlockPlane, CoefficientState, PrivateHtDecoder};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
pub(super) enum ReadablePlane<'a> {
    Wide(&'a CodeBlockPlane),
    Private(&'a PrivateHtDecoder),
}

#[cfg(verus_keep_ghost)]
verus! {
    impl ReadablePlane<'_> {
        pub(super) closed spec fn view(self)->crate::specs::Tier1RawPlane {
            match self {
                Self::Wide(plane)=>crate::tier1::code_block_plane_view(plane),
                Self::Private(decoder)=>decoder.view().plane,
            }
        }
    }
}

impl ReadablePlane<'_> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result.0==self.view().width,result.1==self.view().height,
    ))]
    pub(super) fn dimensions(self) -> (u16, u16) {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(ReadablePlane::view);}
        match self {
            Self::Wide(plane) => (plane.width(), plane.height()),
            Self::Private(decoder) => decoder.dimensions(),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result==self.view().coefficients.len(),
            forall|i:int|0<=i<self.view().coefficients.len() ==> #[trigger] self.view().coefficients[i].limbs.len()==6,
    ))]
    pub(super) fn coefficient_count(self) -> usize {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(ReadablePlane::view);}
        match self {
            Self::Wide(plane) => plane.coefficients().len(),
            Self::Private(decoder) => decoder.coefficient_count(),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires index<self.view().coefficients.len(),
        ensures result.is_ok(),
            crate::tier1::coefficient_raw_outcome(result)==Ok(self.view().coefficients[index as int]),
    ))]
    pub(super) fn coefficient(self, index: usize) -> Result<CoefficientState, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(ReadablePlane::view);}
        match self {
            Self::Wide(plane) => Ok(plane.coefficients()[index]),
            Self::Private(decoder) => decoder.raw_coefficient(index),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_coefficient_collect_result(self.view(),crate::transform::quantized_coefficients_outcome(result)),
            crate::transform::quantized_coefficients_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
                crate::transform::quantized_coefficients_outcome(result)==crate::specs::part1_prepare_collect_coefficients(self.view()),
    ))]
    pub(super) fn collect(self) -> Result<Vec<crate::transform::SignedMagnitude>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(ReadablePlane::view);}
        match self {
            Self::Wide(plane) => super::collect_prepare_coefficients(plane),
            Self::Private(decoder) => decoder.collect(),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.view()==crate::tier1::code_block_plane_view(plane),
))]
pub(super) fn from_wide(plane: &CodeBlockPlane) -> ReadablePlane<'_> {
    #[cfg(verus_keep_ghost)]
    proof! {reveal(ReadablePlane::view);}
    ReadablePlane::Wide(plane)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.view()==plane.view().plane,
))]
pub(super) fn from_private(plane: &PrivateHtDecoder) -> ReadablePlane<'_> {
    #[cfg(verus_keep_ghost)]
    proof! {reveal(ReadablePlane::view);}
    ReadablePlane::Private(plane)
}
