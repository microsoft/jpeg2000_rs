use crate::DecodeError;
use crate::tier1::{CodeBlockPlane, CoefficientState, PrivateHtDecoder};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(super) type WidePlane<'a> = &'a CodeBlockPlane;
pub(super) type PrivatePlane<'a> = &'a PrivateHtDecoder;
pub(super) type WideRow<'a> = &'a [CoefficientState];

#[derive(Clone, Copy)]
pub(super) struct PrivateRow<'a> {
    decoder: &'a PrivateHtDecoder,
    start: usize,
    end: usize,
}

pub(super) trait ReadableRow: Copy {
    #[cfg(verus_keep_ghost)]
    verus! {
        spec fn raw_row(self) -> Seq<crate::specs::Tier1RawCoefficient>;
        spec fn valid(self) -> bool;
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.valid(),index<self.raw_row().len(),
        ensures result==Ok(crate::specs::part2_narrow_magnitude(self.raw_row()[index as int])),
    ))]
    fn narrow(self, index: usize) -> Result<Option<u64>, DecodeError>;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.valid(),index<self.raw_row().len(),
            crate::specs::part2_narrow_magnitude(self.raw_row()[index as int]).is_some(),
        ensures result==Ok((crate::specs::part2_narrow_magnitude(self.raw_row()[index as int]).get_Some_0(),
            self.raw_row()[index as int].significant && self.raw_row()[index as int].negative)),
    ))]
    fn bounded(self, index: usize) -> Result<(u64, bool), DecodeError>;
}

pub(super) trait ReadablePlane: Copy {
    type Row: ReadableRow;

    #[cfg(verus_keep_ghost)]
    verus! {
        spec fn raw_plane(self) -> crate::specs::Tier1RawPlane;
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result.0==self.raw_plane().width,result.1==self.raw_plane().height,
    ))]
    fn dimensions(self) -> (u16, u16);

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result==self.raw_plane().coefficients.len(),
            forall|i:int|0<=i<self.raw_plane().coefficients.len() ==> #[trigger] self.raw_plane().coefficients[i].limbs.len()==6,
    ))]
    fn coefficient_count(self) -> usize;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires start<=end,end<=self.raw_plane().coefficients.len(),
        ensures result.valid(),
            result.raw_row()==self.raw_plane().coefficients.subrange(start as int,end as int),
    ))]
    fn row(self, start: usize, end: usize) -> Self::Row;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_coefficient_collect_result(self.raw_plane(),crate::transform::quantized_coefficients_outcome(result)),
            crate::transform::quantized_coefficients_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
                crate::transform::quantized_coefficients_outcome(result)==crate::specs::part1_prepare_collect_coefficients(self.raw_plane()),
    ))]
    fn collect(self) -> Result<Vec<crate::transform::SignedMagnitude>, DecodeError>;
}

impl ReadableRow for WideRow<'_> {
    #[cfg(verus_keep_ghost)]
    verus! {
        closed spec fn raw_row(self) -> Seq<crate::specs::Tier1RawCoefficient> {
            crate::tier1::coefficient_raw_views(self@)
        }
        closed spec fn valid(self) -> bool {
            true
        }
    }

    #[inline]
    fn narrow(self, index: usize) -> Result<Option<u64>, DecodeError> {
        let coefficient = &self[index];
        Ok(coefficient.narrow_reconstructed_magnitude())
    }

    #[inline]
    fn bounded(self, index: usize) -> Result<(u64, bool), DecodeError> {
        let coefficient = &self[index];
        Ok((
            coefficient.reconstructed_magnitude_bounded(),
            coefficient.reconstructed_negative(),
        ))
    }
}

impl ReadableRow for PrivateRow<'_> {
    #[cfg(verus_keep_ghost)]
    verus! {
        closed spec fn raw_row(self) -> Seq<crate::specs::Tier1RawCoefficient> {
            self.decoder.view().plane.coefficients.subrange(self.start as int,self.end as int)
        }
        closed spec fn valid(self) -> bool {
            self.start<=self.end && self.end<=self.decoder.view().plane.coefficients.len()
        }
    }

    #[inline]
    fn narrow(self, index: usize) -> Result<Option<u64>, DecodeError> {
        let coefficient = self.coefficient(index)?;
        Ok(coefficient.narrow_reconstructed_magnitude())
    }

    #[inline]
    fn bounded(self, index: usize) -> Result<(u64, bool), DecodeError> {
        let coefficient = self.coefficient(index)?;
        Ok((
            coefficient.reconstructed_magnitude_bounded(),
            coefficient.reconstructed_negative(),
        ))
    }
}

impl PrivateRow<'_> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.valid(),index<self.raw_row().len(),
        ensures result.is_ok(),
            crate::tier1::coefficient_raw_outcome(result)==Ok(self.raw_row()[index as int]),
    ))]
    #[inline]
    fn coefficient(self, index: usize) -> Result<CoefficientState, DecodeError> {
        debug_assert!(self.start + index < self.end);
        self.decoder.raw_coefficient(self.start + index)
    }
}

impl<'a> ReadablePlane for WidePlane<'a> {
    type Row = WideRow<'a>;

    #[cfg(verus_keep_ghost)]
    verus! {
        closed spec fn raw_plane(self) -> crate::specs::Tier1RawPlane {
            crate::tier1::code_block_plane_view(self)
        }
    }

    fn dimensions(self) -> (u16, u16) {
        (self.width(), self.height())
    }

    fn coefficient_count(self) -> usize {
        self.coefficients().len()
    }

    #[inline]
    fn row(self, start: usize, end: usize) -> Self::Row {
        &self.coefficients()[start..end]
    }

    fn collect(self) -> Result<Vec<crate::transform::SignedMagnitude>, DecodeError> {
        super::collect_prepare_coefficients(self)
    }
}

impl<'a> ReadablePlane for PrivatePlane<'a> {
    type Row = PrivateRow<'a>;

    #[cfg(verus_keep_ghost)]
    verus! {
        closed spec fn raw_plane(self) -> crate::specs::Tier1RawPlane {
            self.view().plane
        }
    }

    fn dimensions(self) -> (u16, u16) {
        PrivateHtDecoder::dimensions(self)
    }

    fn coefficient_count(self) -> usize {
        PrivateHtDecoder::coefficient_count(self)
    }

    fn row(self, start: usize, end: usize) -> Self::Row {
        PrivateRow {
            decoder: self,
            start,
            end,
        }
    }

    fn collect(self) -> Result<Vec<crate::transform::SignedMagnitude>, DecodeError> {
        PrivateHtDecoder::collect(self)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.raw_plane()==crate::tier1::code_block_plane_view(plane),
))]
pub(super) fn from_wide(plane: &CodeBlockPlane) -> WidePlane<'_> {
    plane
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.raw_plane()==plane.view().plane,
))]
pub(super) fn from_private(plane: &PrivateHtDecoder) -> PrivatePlane<'_> {
    plane
}
