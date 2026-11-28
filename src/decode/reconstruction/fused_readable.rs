use crate::DecodeError;
use crate::tier1::{CodeBlockPlane, CoefficientState, PrivateHtDecoder};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

const PACKED_MAG: u64 = u32::MAX as u64;
const PACKED_BP_SHIFT: u32 = 32;
const PACKED_BP_MASK: u64 = 63 << PACKED_BP_SHIFT;
const PACKED_SIG: u64 = 1 << 38;
const PACKED_NEG: u64 = 1 << 39;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures Some(result)==crate::specs::part2_narrow_magnitude(crate::specs::compact_coefficient(value)),
))]
#[inline]
fn compact_word_reconstructed_magnitude(value: u64) -> u64 {
    if value & PACKED_SIG == 0 {
        return 0;
    }
    let bp = (value & PACKED_BP_MASK) >> PACKED_BP_SHIFT;
    let magnitude = value & PACKED_MAG;
    let midpoint = if bp == 63 {
        0
    } else {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(bp == ((value >> 32) & 63) && bp < 63) by(bit_vector)
                requires bp == (value & (63u64 << 32)) >> 32, bp != 63;
        }
        crate::refinement::tier1_midpoint_delta(bp as u16)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bp == ((value >> 32) & 63) && bp <= 63) by(bit_vector)
            requires bp == (value & (63u64 << 32)) >> 32;
        assert(magnitude <= 0xffff_ffffu64) by(bit_vector)
            requires magnitude == value & 0xffff_ffffu64;
        if bp == 63 || bp == 0 {
            assert(midpoint == 0u64);
        } else {
            let shift: u64 = (bp - 1) as u64;
            assert(midpoint == (1u64 << shift));
            assert((1u64 << shift) <= 0x2000_0000_0000_0000u64) by(bit_vector)
                requires shift < 62u64;
        }
        assert(midpoint <= 0x2000_0000_0000_0000u64);
        assert(magnitude as int + midpoint as int <= u64::MAX as int);
    }
    magnitude + midpoint
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == (crate::specs::compact_coefficient(value).significant
        && crate::specs::compact_coefficient(value).negative),
))]
#[inline]
fn compact_word_reconstructed_negative(value: u64) -> bool {
    (value & PACKED_SIG != 0) && (value & PACKED_NEG != 0)
}

pub(super) type WidePlane<'a> = &'a CodeBlockPlane;
pub(super) type WideRow<'a> = &'a [CoefficientState];
pub(super) type PackedRow<'a> = &'a [u64];

#[derive(Clone, Copy)]
pub(super) struct PackedPlane<'a> {
    width: u16,
    height: u16,
    words: &'a [u64],
    decoder: &'a PrivateHtDecoder,
}

#[cfg(test)]
pub(super) type PrivatePlane<'a> = &'a PrivateHtDecoder;

#[cfg(test)]
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

pub(super) trait FusedReadablePlane: Copy {
    type Row: ReadableRow;

    #[cfg(verus_keep_ghost)]
    verus! {
        spec fn raw_plane(self) -> crate::specs::Tier1RawPlane;
        spec fn plane_valid(self) -> bool;
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.plane_valid(),
        ensures result.0==self.raw_plane().width,result.1==self.raw_plane().height,
    ))]
    fn dimensions(self) -> (u16, u16);

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.plane_valid(),
        ensures result==self.raw_plane().coefficients.len(),
            forall|i:int|0<=i<self.raw_plane().coefficients.len() ==> #[trigger] self.raw_plane().coefficients[i].limbs.len()==6,
    ))]
    fn coefficient_count(self) -> usize;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.plane_valid(),start<=end,end<=self.raw_plane().coefficients.len(),
        ensures result.valid(),
            result.raw_row()==self.raw_plane().coefficients.subrange(start as int,end as int),
    ))]
    fn row(self, start: usize, end: usize) -> Self::Row;
}

pub(super) trait ReadablePlane: FusedReadablePlane {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.plane_valid(),
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

impl ReadableRow for PackedRow<'_> {
    #[cfg(verus_keep_ghost)]
    verus! {
        closed spec fn raw_row(self) -> Seq<crate::specs::Tier1RawCoefficient> {
            self@.map_values(|word:u64|crate::specs::compact_coefficient(word))
        }
        closed spec fn valid(self) -> bool {
            true
        }
    }

    #[inline]
    fn narrow(self, index: usize) -> Result<Option<u64>, DecodeError> {
        let word = self[index];
        Ok(Some(compact_word_reconstructed_magnitude(word)))
    }

    #[inline]
    fn bounded(self, index: usize) -> Result<(u64, bool), DecodeError> {
        let word = self[index];
        Ok((
            compact_word_reconstructed_magnitude(word),
            compact_word_reconstructed_negative(word),
        ))
    }
}

#[cfg(test)]
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

#[cfg(test)]
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

impl<'a> FusedReadablePlane for WidePlane<'a> {
    type Row = WideRow<'a>;

    #[cfg(verus_keep_ghost)]
    verus! {
        closed spec fn raw_plane(self) -> crate::specs::Tier1RawPlane {
            crate::tier1::code_block_plane_view(self)
        }
        closed spec fn plane_valid(self) -> bool {
            true
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
}

impl<'a> ReadablePlane for WidePlane<'a> {
    fn collect(self) -> Result<Vec<crate::transform::SignedMagnitude>, DecodeError> {
        super::collect_prepare_coefficients(self)
    }
}

#[cfg(test)]
impl<'a> FusedReadablePlane for PrivatePlane<'a> {
    type Row = PrivateRow<'a>;

    #[cfg(verus_keep_ghost)]
    verus! {
        closed spec fn raw_plane(self) -> crate::specs::Tier1RawPlane {
            self.view().plane
        }
        closed spec fn plane_valid(self) -> bool {
            true
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
}

#[cfg(test)]
impl<'a> ReadablePlane for PrivatePlane<'a> {
    fn collect(self) -> Result<Vec<crate::transform::SignedMagnitude>, DecodeError> {
        PrivateHtDecoder::collect(self)
    }
}

impl<'a> FusedReadablePlane for PackedPlane<'a> {
    type Row = PackedRow<'a>;

    #[cfg(verus_keep_ghost)]
    verus! {
        closed spec fn raw_plane(self) -> crate::specs::Tier1RawPlane {
            self.decoder.view().plane
        }
        closed spec fn plane_valid(self) -> bool {
            self.width == self.decoder.view().plane.width
                && self.height == self.decoder.view().plane.height
                && self.decoder.view().plane.coefficients
                    == self.words@.map_values(|word:u64|crate::specs::compact_coefficient(word))
        }
    }

    #[inline]
    fn dimensions(self) -> (u16, u16) {
        (self.width, self.height)
    }

    #[inline]
    fn coefficient_count(self) -> usize {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|i:int| 0<=i<self.words@.len() implies #[trigger] self.raw_plane().coefficients[i].limbs.len()==6 by {
                assert(self.raw_plane().coefficients[i]==crate::specs::compact_coefficient(self.words@[i]));
            }
        }
        self.words.len()
    }

    #[inline]
    fn row(self, start: usize, end: usize) -> Self::Row {
        let slice = &self.words[start..end];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(slice@.map_values(|word:u64|crate::specs::compact_coefficient(word))
                =~= self.words@.map_values(|word:u64|crate::specs::compact_coefficient(word)).subrange(start as int, end as int));
        }
        slice
    }
}

impl<'a> ReadablePlane for PackedPlane<'a> {
    fn collect(self) -> Result<Vec<crate::transform::SignedMagnitude>, DecodeError> {
        PrivateHtDecoder::collect(self.decoder)
    }
}

#[derive(Clone, Copy)]
pub(super) struct CompactWordsPlane<'a> {
    width: u16,
    height: u16,
    words: &'a [u64],
}

impl<'a> FusedReadablePlane for CompactWordsPlane<'a> {
    type Row = PackedRow<'a>;

    #[cfg(verus_keep_ghost)]
    verus! {
        closed spec fn raw_plane(self) -> crate::specs::Tier1RawPlane {
            crate::specs::Tier1RawPlane {
                width: self.width,
                height: self.height,
                coefficients: self.words@.map_values(|word: u64| crate::specs::compact_coefficient(word)),
            }
        }
        closed spec fn plane_valid(self) -> bool {
            true
        }
    }

    #[inline]
    fn dimensions(self) -> (u16, u16) {
        (self.width, self.height)
    }

    #[inline]
    fn coefficient_count(self) -> usize {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|i: int| 0 <= i < self.words@.len() implies #[trigger] self.raw_plane().coefficients[i].limbs.len() == 6 by {
                assert(self.raw_plane().coefficients[i] == crate::specs::compact_coefficient(self.words@[i]));
            }
        }
        self.words.len()
    }

    #[inline]
    fn row(self, start: usize, end: usize) -> Self::Row {
        let slice = &self.words[start..end];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(slice@.map_values(|word: u64| crate::specs::compact_coefficient(word))
                =~= self.words@.map_values(|word: u64| crate::specs::compact_coefficient(word)).subrange(start as int, end as int));
        }
        slice
    }
}

#[derive(Clone, Copy)]
pub(super) struct EmptyRow {
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    len: usize,
}

impl ReadableRow for EmptyRow {
    #[cfg(verus_keep_ghost)]
    verus! {
        closed spec fn raw_row(self) -> Seq<crate::specs::Tier1RawCoefficient> {
            Seq::new(self.len as nat, |_: int| crate::specs::tier1_empty_coefficient())
        }
        closed spec fn valid(self) -> bool {
            true
        }
    }

    #[inline]
    fn narrow(self, _index: usize) -> Result<Option<u64>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part2_narrow_magnitude(crate::specs::tier1_empty_coefficient()) == Some(0u64)) by(compute);
        }
        Ok(Some(0))
    }

    #[inline]
    fn bounded(self, _index: usize) -> Result<(u64, bool), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part2_narrow_magnitude(crate::specs::tier1_empty_coefficient()) == Some(0u64)) by(compute);
            assert(!crate::specs::tier1_empty_coefficient().significant);
        }
        Ok((0, false))
    }
}

#[derive(Clone, Copy)]
pub(super) struct EmptyBlockPlane {
    width: u16,
    height: u16,
}

impl FusedReadablePlane for EmptyBlockPlane {
    type Row = EmptyRow;

    #[cfg(verus_keep_ghost)]
    verus! {
        closed spec fn raw_plane(self) -> crate::specs::Tier1RawPlane {
            crate::specs::Tier1RawPlane {
                width: self.width,
                height: self.height,
                coefficients: Seq::new((self.width as nat) * (self.height as nat), |_: int| crate::specs::tier1_empty_coefficient()),
            }
        }
        closed spec fn plane_valid(self) -> bool {
            (self.width as nat) * (self.height as nat) <= usize::MAX
        }
    }

    #[inline]
    fn dimensions(self) -> (u16, u16) {
        (self.width, self.height)
    }

    #[inline]
    fn coefficient_count(self) -> usize {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::tier1_empty_coefficient().limbs.len() == 6) by(compute);
        }
        usize::from(self.width) * usize::from(self.height)
    }

    #[inline]
    fn row(self, start: usize, end: usize) -> Self::Row {
        let len = end - start;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(Seq::new(len as nat, |_: int| crate::specs::tier1_empty_coefficient())
                =~= self.raw_plane().coefficients.subrange(start as int, end as int));
        }
        EmptyRow { len }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.plane_valid(),
        result.raw_plane() == (crate::specs::Tier1RawPlane {
            width,
            height,
            coefficients: words@.map_values(|word: u64| crate::specs::compact_coefficient(word)),
        }),
))]
#[inline]
pub(super) fn from_compact_words<'a>(
    width: u16,
    height: u16,
    words: &'a [u64],
) -> CompactWordsPlane<'a> {
    CompactWordsPlane {
        width,
        height,
        words,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires (width as nat) * (height as nat) <= usize::MAX,
    ensures result.plane_valid(),
        result.raw_plane() == (crate::specs::Tier1RawPlane {
            width,
            height,
            coefficients: Seq::new((width as nat) * (height as nat), |_: int| crate::specs::tier1_empty_coefficient()),
        }),
))]
#[inline]
pub(super) fn from_empty_block(width: u16, height: u16) -> EmptyBlockPlane {
    EmptyBlockPlane { width, height }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires width == decoder.view().plane.width,
        height == decoder.view().plane.height,
        decoder.view().plane.coefficients == words@.map_values(|word:u64|crate::specs::compact_coefficient(word)),
    ensures result.plane_valid(),
        result.raw_plane()==decoder.view().plane,
))]
#[inline]
pub(super) fn from_packed<'a>(
    width: u16,
    height: u16,
    words: &'a [u64],
    decoder: &'a PrivateHtDecoder,
) -> PackedPlane<'a> {
    PackedPlane {
        width,
        height,
        words,
        decoder,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.plane_valid(),
        result.raw_plane()==crate::tier1::code_block_plane_view(plane),
))]
pub(super) fn from_wide(plane: &CodeBlockPlane) -> WidePlane<'_> {
    plane
}

#[cfg(test)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.plane_valid(),
        result.raw_plane()==plane.view().plane,
))]
pub(super) fn from_private(plane: &PrivateHtDecoder) -> PrivatePlane<'_> {
    plane
}
