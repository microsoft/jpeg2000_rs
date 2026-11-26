use super::state::{
    ht_statistics_zero, invalid_code_block, sign_context, significant_neighbor_count,
    zero_coding_context,
};
use super::{
    CoefficientState, NeighborSummary, RUN_LENGTH_CONTEXT, SubbandOrientation, Tier1BitplaneState,
    Tier1BlockCoding, Tier1CodeBlockDecoder, Tier1PassKind, Tier1PassStatistics, UNIFORM_CONTEXT,
};
use crate::mq::MqDecoder;
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

const MAG: u64 = u32::MAX as u64;
const BP_SHIFT: u32 = 32;
const BP_MASK: u64 = 63 << BP_SHIFT;
const EMPTY: u64 = BP_MASK;
const SIG: u64 = 1 << 38;
const NEG: u64 = 1 << 39;
const REFINED: u64 = 1 << 40;
const SIG_NEIGHBORS: u32 = 41;
const NEG_NEIGHBORS: u32 = 49;
const DIRECTIONS: [(i32, i32); 8] = [
    (-1, -1),
    (0, -1),
    (1, -1),
    (-1, 0),
    (1, 0),
    (-1, 1),
    (0, 1),
    (1, 1),
];

struct CompactPlane {
    width: usize,
    height: usize,
    entries: Vec<u64>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl CompactPlane {
    closed spec fn view(&self)->crate::specs::Tier1RawPlane {
        crate::specs::compact_plane(self.width,self.height,self.entries@)
    }
    closed spec fn shape(&self)->bool {
        crate::specs::compact_shape(self.width,self.height,self.entries@)
    }
    closed spec fn ready(&self,state:&Tier1BitplaneState)->bool {
        self.shape() && crate::specs::compact_membership(self.width,self.height,self.entries@,super::legacy_bitplane_view(state))
    }
    closed spec fn frame(&self,state:&Tier1BitplaneState,decoder:&MqDecoder<'_>,statistics:Tier1PassStatistics)->crate::specs::Part1LegacyFrame {
        crate::specs::Part1LegacyFrame {
            plane:self.view(),state:super::legacy_bitplane_view(state),
            symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics,
        }
    }
}
impl Tier1CodeBlockDecoder {
    closed spec fn compact_view(&self,packed:&CompactPlane)->crate::specs::Tier1DecoderState {
        crate::specs::Tier1DecoderState {plane:packed.view(),..super::tier1_decoder_state(self)}
    }
    closed spec fn compact_run(&self,packed:&CompactPlane,decoder:&MqDecoder<'_>,statistics:Tier1PassStatistics)->crate::specs::Part1LegacySegmentRun {
        crate::specs::Part1LegacySegmentRun {
            decoder:self.compact_view(packed),symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics,
        }
    }
    proof fn compact_metadata(&self)
        ensures super::tier1_decoder_state(self).plane==super::code_block_plane_view(&self.plane),
            super::tier1_decoder_state(self).next_pass==self.next_pass,
            super::tier1_decoder_state(self).bitplane==self.bitplane,
            super::tier1_decoder_state(self).maximum_passes==self.maximum_passes,
            super::tier1_decoder_state(self).style==self.style,
            super::tier1_decoder_state(self).orientation==self.orientation,
            super::tier1_decoder_state(self).bitplane_state==super::legacy_bitplane_option_view(&self.bitplane_state),
    {reveal(super::tier1_decoder_state);reveal(super::legacy_bitplane_option_view);}
    proof fn compact_views(&self,packed:&CompactPlane,decoder:&MqDecoder<'_>,statistics:Tier1PassStatistics)
        ensures self.compact_view(packed)==crate::specs::compact_substitute_plane(super::tier1_decoder_state(self),packed.view()),
            self.compact_run(packed,decoder,statistics)==(crate::specs::Part1LegacySegmentRun {
                decoder:self.compact_view(packed),symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics}),
    {}
    proof fn compact_native_store(before:Self,after:Self)
        requires after==(Self {next_pass:after.next_pass,bitplane:after.bitplane,bitplane_state:after.bitplane_state,..before}),
        ensures super::tier1_decoder_state(&after)==(crate::specs::Tier1DecoderState {
            next_pass:after.next_pass,bitplane:after.bitplane,
            bitplane_state:super::legacy_bitplane_option_view(&after.bitplane_state),
            ..super::tier1_decoder_state(&before)
        }),
    {reveal(super::tier1_decoder_state);}
}
pub(super) closed spec fn compact_plane_outcome(result:Result<CompactPlane,DecodeError>)->Result<(usize,usize,Seq<u64>),DecodeError> {
    match result{Err(error)=>Err(error),Ok(plane)=>Ok((plane.width,plane.height,plane.entries@)),}
}
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires 0<width<=4096,0<height<=4096,width*height<=4096,
        ensures crate::specs::compact_initial_result(width,height,compact_plane_outcome(result)),
            crate::specs::compact_capacity_result(width,height,match result{Err(error)=>Err(error),Ok(_)=>Ok(())}),
            match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>
                value.width==width && value.height==height && value.entries@==Seq::new(width as nat*height as nat,|_:int|EMPTY)
                    && crate::specs::compact_cache(width,height,value.entries@)
                    && forall|i:int|0<=i<value.entries.len() ==> crate::specs::compact_precision_word(value.entries@[i])},
    ))]
fn new_compact_plane(width: usize, height: usize) -> Result<CompactPlane, DecodeError> {
    let count = width * height;
    let allocated = crate::allocation::empty_with_capacity(count);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(width*height>0) by(nonlinear_arith) requires width>0,height>0;
        crate::specs::compact_capacity_observed(width,height,match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())});
        crate::specs::compact_initial_observed(width,height,match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())});
    }
    let mut entries = allocated?;
    entries.resize(count, EMPTY);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i:int|0<=i<count implies entries@[i]==EMPTY by{
            assert(vstd::pervasive::cloned::<u64>(EMPTY,entries@[i]));
        }
        assert(entries@ =~= Seq::new(count as nat,|_:int|EMPTY));
        assert(EMPTY==0x3f_0000_0000u64) by(compute);
        crate::specs::compact_empty_cache(width,height,entries@);
        assert(crate::specs::compact_precision_word(EMPTY)) by(compute);
    }
    Ok(CompactPlane {
        width,
        height,
        entries,
    })
}

impl CompactPlane {
    #[cfg_attr(verus_keep_ghost, verus_spec(_result =>
        requires self.shape(),wide.width==self.width,wide.height==self.height,
            wide.coefficients.len()==self.entries.len(),
        ensures ((),super::code_block_plane_view(final(wide)))==crate::specs::compact_bulk_commit(
                super::code_block_plane_view(old(wide)),self.entries@),
            super::code_block_plane_view(final(wide))==self.view(),
    ))]
    fn commit(&self, wide: &mut super::CodeBlockPlane) {
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index<=self.entries.len(),
                wide.width==self.width,wide.height==self.height,
                wide.coefficients.len()==self.entries.len(),
                forall|i:int|0<=i<index ==> super::coefficient_raw_view(wide.coefficients@[i])==crate::specs::compact_coefficient(self.entries@[i]),
            decreases self.entries.len()-index,
        ))]
        while index < self.entries.len() {
            wide.coefficients[index] = unpack_word(self.entries[index]);
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {assert(super::code_block_plane_view(wide).coefficients =~= self.view().coefficients);}
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::coefficient_raw_view(result)==crate::specs::compact_coefficient(value),
))]
pub(super) fn unpack_word(value: u64) -> CoefficientState {
    let bp = (value & BP_MASK) >> BP_SHIFT;
    let coefficient = CoefficientState {
        magnitude: value & MAG,
        magnitude_high: [0; 5],
        legacy_bitplane: if bp == 63 { None } else { Some(bp as u16) },
        significant: value & SIG != 0,
        negative: value & NEG != 0,
        refined: value & REFINED != 0,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(super::coefficient_raw_view);
        assert(bp==((value>>32)&63) && bp<=63) by(bit_vector)
            requires bp==(value & (63u64<<32))>>32;
        assert(super::coefficient_raw_view(coefficient).limbs =~= crate::specs::compact_coefficient(value).limbs);
    }
    coefficient
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures Some(result)==crate::specs::part2_narrow_magnitude(crate::specs::compact_coefficient(value)),
))]
#[inline]
pub(crate) fn compact_word_reconstructed_magnitude(value: u64) -> u64 {
    if value & SIG == 0 {
        return 0;
    }
    let bp = (value & BP_MASK) >> BP_SHIFT;
    let magnitude = value & MAG;
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
        assert(midpoint <= (1u64 << 61)) by(bit_vector)
            requires bp == 63 ==> midpoint == 0u64,
                bp == 0 ==> midpoint == 0u64,
                (0 < bp && bp < 63) ==> midpoint == (1u64 << ((bp - 1) as u64));
        assert(magnitude as int + midpoint as int <= u64::MAX as int);
    }
    magnitude + midpoint
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == (crate::specs::compact_coefficient(value).significant
        && crate::specs::compact_coefficient(value).negative),
))]
#[inline]
pub(crate) fn compact_word_reconstructed_negative(value: u64) -> bool {
    (value & SIG != 0) && (value & NEG != 0)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::compact_packable_coefficient(super::coefficient_raw_view(coefficient)),
))]
pub(super) fn packable(coefficient: CoefficientState) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(super::coefficient_raw_view); }
    coefficient.magnitude <= MAG
        && coefficient.magnitude_high[0] == 0
        && coefficient.magnitude_high[1] == 0
        && coefficient.magnitude_high[2] == 0
        && coefficient.magnitude_high[3] == 0
        && coefficient.magnitude_high[4] == 0
        && match coefficient.legacy_bitplane {
            None => true,
            Some(bp) => bp < 63,
        }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::compact_packable_coefficient(super::coefficient_raw_view(coefficient)),
    ensures crate::specs::compact_coefficient(result) == super::coefficient_raw_view(coefficient),
))]
pub(super) fn pack_word(coefficient: CoefficientState) -> u64 {
    let bp = match coefficient.legacy_bitplane {
        Some(value) => u64::from(value),
        None => 63,
    };
    let mag = coefficient.magnitude;
    let significant = coefficient.significant;
    let negative = coefficient.negative;
    let is_refined = coefficient.refined;
    let sig = if significant { SIG } else { 0 };
    let neg = if negative { NEG } else { 0 };
    let refined = if is_refined { REFINED } else { 0 };
    let word = mag | (bp << BP_SHIFT) | sig | neg | refined;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(super::coefficient_raw_view);
        assert(mag <= 0xffff_ffff && bp <= 63);
        assert(SIG==1u64<<38 && NEG==1u64<<39 && REFINED==1u64<<40) by(compute);
        assert(sig == if significant { 1u64 << 38 } else { 0 });
        assert(neg == if negative { 1u64 << 39 } else { 0 });
        assert(refined == if is_refined { 1u64 << 40 } else { 0 });
        assert(word & 0xffff_ffffu64 == mag
            && ((word >> 32) & 63) == bp
            && ((word & (1u64 << 38)) != 0) == significant
            && ((word & (1u64 << 39)) != 0) == negative
            && ((word & (1u64 << 40)) != 0) == is_refined) by(bit_vector)
            requires mag <= 0xffff_ffff, bp <= 63,
                sig == (if significant { 1u64 << 38 } else { 0 }),
                neg == (if negative { 1u64 << 39 } else { 0 }),
                refined == (if is_refined { 1u64 << 40 } else { 0 }),
                word == mag | (bp << 32) | sig | neg | refined;
        assert(crate::specs::compact_coefficient(word).limbs =~= super::coefficient_raw_view(coefficient).limbs);
        let packed = crate::specs::compact_coefficient(word);
        let raw = super::coefficient_raw_view(coefficient);
        match coefficient.legacy_bitplane {
            None => {
                assert(bp==63);
                assert(packed.legacy_bitplane.is_none());
            },
            Some(index) => {
                assert(index<63 && bp as u16==index);
                assert(packed.legacy_bitplane==Some(index));
            },
        }
        assert(packed.legacy_bitplane==raw.legacy_bitplane);
        assert(packed.significant==raw.significant);
        assert(packed.negative==raw.negative);
        assert(packed.refined==raw.refined);
    }
    word
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires bp<31,
    ensures result==crate::specs::compact_mark_word(value,bp,negative),
        crate::specs::compact_coefficient(result).significant,
        crate::specs::compact_coefficient(result).negative==negative,
        !crate::specs::compact_coefficient(result).refined,
        crate::specs::compact_coefficient(result).legacy_bitplane==Some(bp),
        crate::specs::compact_coefficient(result).limbs[0]==1u64<<bp,
        result>>41==value>>41,
        crate::specs::compact_precision_word(result),
))]
fn mark_word(value: u64, bp: u16, negative: bool) -> u64 {
    let marked = (value & !(MAG | BP_MASK | NEG | REFINED))
        | (1u64 << bp)
        | ((u64::from(bp)) << BP_SHIFT)
        | SIG
        | if negative { NEG } else { 0 };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::compact_precision_mark(value,bp,negative);
        assert(marked==crate::specs::compact_mark_word(value,bp,negative)) by(bit_vector)
            requires bp<31,
                marked==(value & !(0xffff_ffffu64 | (63u64<<32) | (1u64<<39) | (1u64<<40)))
                    | (1u64<<bp) | ((bp as u64)<<32) | (1u64<<38) | if negative{1u64<<39}else{0u64};
        assert(marked>>41==value>>41
            && marked & (1u64<<38)!=0
            && (marked & (1u64<<39)!=0)==negative
            && marked & (1u64<<40)==0
            && ((marked>>32)&63)==bp as u64
            && marked & 0xffff_ffff==1u64<<bp) by(bit_vector)
            requires bp<31,marked==crate::specs::compact_mark_word(value,bp,negative);
    }
    marked
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires direction<8,
    ensures result==crate::specs::compact_add_neighbor(value,direction,negative),
        result==value | (1u64<<(41+direction)) | if negative{1u64<<(49+direction)}else{0u64},
        crate::specs::compact_coefficient(result)==crate::specs::compact_coefficient(value),
        result & 0x1ff_ffff_ffffu64==value & 0x1ff_ffff_ffffu64,
        crate::specs::compact_precision_word(result)==crate::specs::compact_precision_word(value),
))]
fn cache_word(value: u64, direction: u32, negative: bool) -> u64 {
    let updated = value
        | (1u64 << (SIG_NEIGHBORS + direction))
        | if negative {
            1u64 << (NEG_NEIGHBORS + direction)
        } else {
            0
        };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(updated & 0x1ff_ffff_ffffu64==value & 0x1ff_ffff_ffffu64) by(bit_vector)
            requires direction<8,updated==value | (1u64<<(41+direction)) | if negative{1u64<<(49+direction)}else{0u64};
        crate::specs::compact_precision_lower_frame(updated,value);
        assert(updated & 0xffff_ffffu64==value & 0xffff_ffffu64
            && ((updated>>32)&63)==((value>>32)&63)
            && updated & (1u64<<38)==value & (1u64<<38)
            && updated & (1u64<<39)==value & (1u64<<39)
            && updated & (1u64<<40)==value & (1u64<<40)) by(bit_vector)
            requires updated & 0x1ff_ffff_ffffu64==value & 0x1ff_ffff_ffffu64;
    }
    updated
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires bp<31,value & MAG<1u64<<31,
        value & (((1u64<<((bp+1) as u16))-1) as u64)==0,
    ensures result==crate::specs::compact_refine_word(value,bp,bit),
        crate::specs::compact_coefficient(result).limbs[0]==(value & MAG)+if bit{1u64<<bp}else{0u64},
        crate::specs::compact_coefficient(result).legacy_bitplane==Some(bp),
        crate::specs::compact_coefficient(result).refined,
        crate::specs::compact_coefficient(result).significant==crate::specs::compact_coefficient(value).significant,
        crate::specs::compact_coefficient(result).negative==crate::specs::compact_coefficient(value).negative,
        result>>41==value>>41,result & MAG<1u64<<31,
        crate::specs::compact_refinement_frontier(value,bp) ==> crate::specs::compact_precision_word(result),
))]
fn refine_word(value: u64, bp: u16, bit: bool) -> u64 {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(value<=u64::MAX-(1u64<<bp)) by(bit_vector)
            requires bp<31,value & 0xffff_ffffu64<1u64<<31,value & (((1u64<<((bp+1) as u16))-1) as u64)==0;
    }
    let next = if bit { value + (1u64 << bp) } else { value };
    let refined = (next & !BP_MASK) | ((u64::from(bp)) << BP_SHIFT) | REFINED;
    #[cfg(verus_keep_ghost)]
    proof! {
        if crate::specs::compact_refinement_frontier(value,bp){crate::specs::compact_precision_refine(value,bp,bit);}
        assert(refined & 0xffff_ffffu64==(value & 0xffff_ffffu64)+if bit{1u64<<bp}else{0u64}
            && refined & 0xffff_ffffu64<1u64<<31
            && ((refined>>32)&63)==bp as u64
            && refined & (1u64<<40)!=0
            && refined & (1u64<<38)==value & (1u64<<38)
            && refined & (1u64<<39)==value & (1u64<<39)
            && refined>>41==value>>41) by(bit_vector)
            requires bp<31,value & 0xffff_ffffu64<1u64<<31,value & (((1u64<<((bp+1) as u16))-1) as u64)==0,
                next==if bit{(value+(1u64<<bp)) as u64}else{value},
                refined==(next & !(63u64<<32)) | ((bp as u64)<<32) | (1u64<<40);
    }
    refined
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result==crate::specs::compact_flag_summary(sig,neg),
        result.horizontal_significant<=2,result.vertical_significant<=2,result.diagonal_significant<=4,
        -2<=result.horizontal_sign_balance<=2,-2<=result.vertical_sign_balance<=2,
))]
fn word_flag_summary(sig: u8, neg: u8) -> NeighborSummary {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost original_neg=neg;}
    let neg = neg & sig;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((sig&1)<=1 && ((sig>>1)&1)<=1 && ((sig>>2)&1)<=1 && ((sig>>3)&1)<=1
            && ((sig>>4)&1)<=1 && ((sig>>5)&1)<=1 && ((sig>>6)&1)<=1 && ((sig>>7)&1)<=1
            && ((neg>>1)&1)<=1 && ((neg>>3)&1)<=1 && ((neg>>4)&1)<=1 && ((neg>>6)&1)<=1) by(bit_vector);
        assert(((neg>>1)&1)<=((sig>>1)&1) && ((neg>>3)&1)<=((sig>>3)&1)
            && ((neg>>4)&1)<=((sig>>4)&1) && ((neg>>6)&1)<=((sig>>6)&1)) by(bit_vector)
            requires neg==original_neg & sig;
    }
    let h = ((sig >> 3) & 1) + ((sig >> 4) & 1);
    let v = ((sig >> 1) & 1) + ((sig >> 6) & 1);
    NeighborSummary {
        horizontal_significant: h,
        vertical_significant: v,
        diagonal_significant: (sig & 1) + ((sig >> 2) & 1) + ((sig >> 5) & 1) + ((sig >> 7) & 1),
        horizontal_sign_balance: h as i8 - 2 * (((neg >> 3) & 1) + ((neg >> 4) & 1)) as i8,
        vertical_sign_balance: v as i8 - 2 * (((neg >> 1) & 1) + ((neg >> 6) & 1)) as i8,
    }
}

impl CompactPlane {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.shape(),x<self.width,y<self.height,
            crate::specs::compact_cache(self.width,self.height,self.entries@),
        ensures result==crate::specs::compact_flag_summary(
            ((self.entries@[y*self.width+x]>>41) as u8) & if causal && y%4==3{0x1fu8}else{0xffu8},
            ((self.entries@[y*self.width+x]>>49) as u8) & if causal && y%4==3{0x1fu8}else{0xffu8}),
            crate::specs::ht_neighbors(self.view(),x as u16,y as u16,causal)==Ok(result),
    ))]
    fn summary(&self, x: usize, y: usize, causal: bool) -> NeighborSummary {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_index(self.width,self.height,self.entries@,x,y);
            crate::specs::compact_cached_summary(self.width,self.height,self.entries@,x,y,causal);
        }
        let value = self.entries[y * self.width + x];
        let sig = (value >> SIG_NEIGHBORS) as u8;
        let neg = (value >> NEG_NEIGHBORS) as u8;
        let mask = if causal && y % 4 == 3 { 0x1f } else { 0xff };
        word_flag_summary(sig & mask, neg & mask)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).shape(),x<old(self).width,y<old(self).height,bp<31,
            crate::specs::compact_cache(old(self).width,old(self).height,old(self).entries@),
            forall|i:int|0<=i<old(self).entries.len() ==> crate::specs::compact_precision_word(old(self).entries@[i]),
            old(self).entries@[(y*old(self).width+x) as int] & SIG==0,
        ensures final(self).shape(),final(self).width==old(self).width,final(self).height==old(self).height,
            crate::specs::compact_cache(final(self).width,final(self).height,final(self).entries@),
            forall|i:int|0<=i<final(self).entries.len() ==> crate::specs::compact_precision_word(final(self).entries@[i]),
            forall|i:int|0<=i<final(self).entries.len() && i!=(y*old(self).width+x) as int
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
            match result{Err(_)=>final(self).entries@==old(self).entries@,Ok(())=>
                crate::specs::compact_coefficient(final(self).entries@[(y*old(self).width+x) as int]).significant
                    && crate::specs::compact_coefficient(final(self).entries@[(y*old(self).width+x) as int]).legacy_bitplane==Some(bp)},
            (result,final(self).view(),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
                ==crate::specs::part1_legacy_sign_mark(old(self).view(),
                    crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),x as u16,y as u16,bp,summary),
    ))]
    fn sign_and_mark(
        &mut self,
        x: usize,
        y: usize,
        bp: u16,
        summary: NeighborSummary,
        decoder: &mut MqDecoder<'_>,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_legacy_sign_mark);reveal(crate::specs::part1_legacy_symbol);}
        let sign = sign_context(summary);
        let bit = decoder.decode(usize::from(sign.context))?;
        let negative = crate::refinement::tier1_decoded_sign(bit, sign.predicted_negative, false);
        self.mark(x, y, bp, negative);
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).shape(),x<old(self).width,y<old(self).height,bp<31,
            crate::specs::compact_cache(old(self).width,old(self).height,old(self).entries@),
            forall|i:int|0<=i<old(self).entries.len() ==> crate::specs::compact_precision_word(old(self).entries@[i]),
            old(self).entries@[(y*old(self).width+x) as int] & SIG==0,
        ensures final(self).shape(),final(self).width==old(self).width,final(self).height==old(self).height,
            crate::specs::compact_cache(final(self).width,final(self).height,final(self).entries@),
            forall|i:int|0<=i<final(self).entries.len() ==> crate::specs::compact_precision_word(final(self).entries@[i]),
            forall|i:int|0<=i<final(self).entries.len() ==>
                final(self).entries@[i] & 0x1ff_ffff_ffffu64==
                    (if i==(y*old(self).width+x) as int{crate::specs::compact_mark_word(old(self).entries@[i],bp,negative)}else{old(self).entries@[i]}) & 0x1ff_ffff_ffffu64,
            crate::specs::compact_coefficient(final(self).entries@[(y*old(self).width+x) as int]).significant,
            crate::specs::compact_coefficient(final(self).entries@[(y*old(self).width+x) as int]).legacy_bitplane==Some(bp),
            (Ok::<(),DecodeError>(()),final(self).view())==crate::specs::part1_legacy_mark(old(self).view(),x as u16,y as u16,bp,negative),
            final(self).view().coefficients==old(self).view().coefficients.update((y*old(self).width+x) as int,
                crate::specs::compact_coefficient(crate::specs::compact_mark_word(old(self).entries@[(y*old(self).width+x) as int],bp,negative))),
    ))]
    fn mark(&mut self, x: usize, y: usize, bp: u16, negative: bool) {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_index(self.width,self.height,self.entries@,x,y);
            crate::specs::compact_mark_coefficient(self.entries@[(y*self.width+x) as int],bp,negative);
            vstd::arithmetic::power2::lemma_pow2_pos(bp as nat);
            crate::specs::compact_cache_mark_start(self.width,self.height,self.entries@,x,y,bp,negative);
        }
        let index = y * self.width + x;
        self.entries[index] = mark_word(self.entries[index], bp, negative);
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost marked=self.view();}
        let mut direction = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant direction<=8,self.shape(),self.width==old(self).width,self.height==old(self).height,
                self.view()==marked,marked.coefficients==old(self).view().coefficients.update(index as int,
                    crate::specs::compact_coefficient(crate::specs::compact_mark_word(old(self).entries@[index as int],bp,negative))),
                index==y*self.width+x,x<self.width,y<self.height,
                old(self).shape(),old(self).entries@[index as int] & SIG==0,bp<31,
                crate::specs::compact_pending_cache(self.width,self.height,self.entries@,x as int,y as int,direction as u32),
                crate::specs::compact_coefficient(self.entries@[index as int]).significant,
                crate::specs::compact_coefficient(self.entries@[index as int]).negative==negative,
                forall|i:int|0<=i<self.entries.len() ==> crate::specs::compact_precision_word(self.entries@[i]),
                forall|i:int|0<=i<self.entries.len() ==> self.entries@[i] & 0x1ff_ffff_ffffu64==
                    (if i==index{crate::specs::compact_mark_word(old(self).entries@[i],bp,negative)}else{old(self).entries@[i]}) & 0x1ff_ffff_ffffu64,
            decreases 8-direction,
        ))]
        while direction < 8 {
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before_words=self.entries@;}
            let (dx, dy) = DIRECTIONS[direction];
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(direction==0 || direction==1 || direction==2 || direction==3
                    || direction==4 || direction==5 || direction==6 || direction==7);
                assert(dx as int==crate::specs::compact_dx(direction as u32));
                assert(dy as int==crate::specs::compact_dy(direction as u32));
                crate::specs::compact_cache_mark_step(self.width,self.height,before_words,x,y,direction as u32,negative);
            }
            let nx = x as i32 + dx;
            let ny = y as i32 + dy;
            if nx >= 0 && ny >= 0 && nx < self.width as i32 && ny < self.height as i32 {
                let bit = 7 - direction;
                #[cfg(verus_keep_ghost)]
                proof! {crate::specs::compact_index(self.width,self.height,self.entries@,nx as usize,ny as usize);}
                let target = ny as usize * self.width + nx as usize;
                self.entries[target] = cache_word(self.entries[target], bit as u32, negative);
                #[cfg(verus_keep_ghost)]
                proof! {assert(self.view().coefficients =~= marked.coefficients);}
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(self.entries@==match crate::specs::compact_neighbor_index(self.width,self.height,x as int,y as int,direction as u32){
                    None=>before_words,
                    Some(target)=>before_words.update(target,crate::specs::compact_add_neighbor(before_words[target],(7-direction) as u32,negative)),
                });
            }
            direction += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_mark_coefficient(old(self).entries@[index as int],bp,negative);
            crate::specs::compact_cache_mark_end(self.width,self.height,self.entries@,x,y);
            crate::specs::compact_lower_fields(self.entries@[index as int],
                crate::specs::compact_mark_word(old(self).entries@[index as int],bp,negative));
            vstd::arithmetic::power2::lemma_pow2_pos(bp as nat);
            crate::specs::compact_index(old(self).width,old(self).height,old(self).entries@,x,y);
            assert(crate::specs::tier1_raw_plane_index(old(self).view(),x as u16,y as u16)==Ok(index));
            let expected=crate::specs::part1_legacy_mark(old(self).view(),x as u16,y as u16,bp,negative);
            assert(expected.0==Ok(()));
            assert(expected.1.coefficients =~= self.view().coefficients);
            assert((Ok::<(),DecodeError>(()),self.view())==crate::specs::part1_legacy_mark(old(self).view(),x as u16,y as u16,bp,negative));
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.shape(),bp<31,
        ensures crate::specs::part2_bitplane_initial_result(self.view(),bp,super::legacy_bitplane_outcome(result)),
            super::legacy_bitplane_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
                super::legacy_bitplane_outcome(result)==crate::specs::part1_legacy_bitplane_initial(self.view(),bp),
            match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>
                Ok::<crate::specs::Part1LegacyBitplane,DecodeError>(super::legacy_bitplane_view(&value))
                    ==crate::specs::part1_legacy_bitplane_initial(self.view(),bp)},
    ))]
    fn initial_state(&self, bp: u16) -> Result<Tier1BitplaneState, DecodeError> {
        let allocated = crate::allocation::empty_with_capacity(self.entries.len());
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self.entries.len()>0) by(nonlinear_arith)
                requires self.width>0,self.height>0,self.entries.len()==self.width*self.height;
            crate::specs::part2_bitplane_capacity_observed(self.view(),bp,false,None,match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())});
            if let Err(error)=allocated{crate::specs::part2_bitplane_initial_first_error(self.view(),bp,error);}
        }
        let mut significant_before = allocated?;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index<=self.entries.len(),significant_before.len()==index,
                self.shape(),bp<31,
                crate::specs::part2_bitplane_capacity_result(self.view(),bp,false,None,Ok(())),
                forall|i:int|0<=i<index ==> significant_before@[i]==crate::specs::compact_coefficient(self.entries@[i]).significant,
            decreases self.entries.len()-index,
        ))]
        while index < self.entries.len() {
            significant_before.push(self.entries[index] & SIG != 0);
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {assert(significant_before@ =~= crate::specs::part2_bitplane_significant(self.view()));}
        let visited = crate::allocation::filled_values(false, self.entries.len());
        #[cfg(verus_keep_ghost)]
        proof! {
            let result=match visited{Err(error)=>Err(error),Ok(_)=>Ok(())};
            crate::specs::part2_bitplane_capacity_observed(self.view(),bp,true,Some(significant_before@),result);
            crate::specs::part2_bitplane_initial_observed(self.view(),bp,result);
        }
        let significance_visited = visited?;
        #[cfg(verus_keep_ghost)]
        proof! {reveal(super::legacy_bitplane_view);}
        Ok(Tier1BitplaneState {
            width: self.width as u16,
            height: self.height as u16,
            bitplane: bp,
            significant_before,
            significance_visited,
            significance_propagation_complete: false,
            magnitude_refinement_complete: false,
            cleanup_complete: false,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(old(state)),coordinate.0<old(self).width,coordinate.1<old(self).height,
            crate::specs::compact_statistics_room(*old(stats)),
        ensures final(self).ready(final(state)),final(self).width==old(self).width,final(self).height==old(self).height,
            crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(final(state))),
            (result,final(self).frame(final(state),final(decoder),*final(stats)))==crate::specs::part1_legacy_sig_cell(
                old(self).frame(old(state),old(decoder),*old(stats)),coordinate.0 as u16,coordinate.1 as u16,orientation,causal),
            crate::specs::compact_statistics_delta(*old(stats),*final(stats),2),
            forall|i:int|0<=i<final(self).entries.len() && i!=(coordinate.1*old(self).width+coordinate.0) as int
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
            forall|i:int|0<=i<final(self).entries.len() && old(state).significant_before@[i]
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
    ))]
    fn sig_cell(
        &mut self,
        coordinate: (usize, usize),
        state: &mut Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        orientation: SubbandOrientation,
        causal: bool,
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before_words=self.entries@;let ghost before_state=super::legacy_bitplane_view(state);}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_sig_cell);reveal(crate::specs::part1_legacy_symbol);
            reveal(crate::specs::compact_membership);
            reveal(super::legacy_bitplane_view);
            crate::specs::compact_index(self.width,self.height,self.entries@,coordinate.0,coordinate.1);
        }
        let (x, y) = coordinate;
        stats.coefficients_scanned += 1;
        let index = y * self.width + x;
        if self.entries[index] & SIG == 0 {
            let summary = self.summary(x, y, causal);
            if significant_neighbor_count(summary) != 0 {
                let bit = decoder.decode(usize::from(zero_coding_context(summary, orientation)))?;
                state.significance_visited[index] = true;
                stats.coding_symbols += 1;
                if bit {
                    let marked = self.sign_and_mark(x, y, state.bitplane, summary, decoder);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::specs::compact_membership_cell(self.width,self.height,before_words,self.entries@,
                            before_state,super::legacy_bitplane_view(state),index as int);
                    }
                    marked?;
                    stats.coding_symbols += 1;
                    stats.newly_significant += 1;
                }
            }
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(state),x<old(self).width,y<old(self).height,
            crate::specs::compact_statistics_room(*old(stats)),
            state.significant_before@[(y*old(self).width+x) as int] ==>
                crate::specs::compact_refinement_frontier(old(self).entries@[(y*old(self).width+x) as int],state.bitplane),
        ensures final(self).ready(state),final(self).width==old(self).width,final(self).height==old(self).height,
            (result,final(self).frame(state,final(decoder),*final(stats)))==crate::specs::part1_legacy_mag_cell(
                old(self).frame(state,old(decoder),*old(stats)),x as u16,y as u16,causal),
            crate::specs::compact_statistics_delta(*old(stats),*final(stats),2),
            forall|i:int|0<=i<final(self).entries.len() && i!=(y*old(self).width+x) as int
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
            result.is_ok() && state.significant_before@[(y*old(self).width+x) as int] ==>
                ((final(self).entries@[(y*old(self).width+x) as int]>>32)&63)==state.bitplane,
    ))]
    fn refine_cell(
        &mut self,
        x: usize,
        y: usize,
        state: &Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        causal: bool,
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before_words=self.entries@;}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_mag_cell);reveal(crate::specs::part1_legacy_symbol);
            reveal(crate::specs::compact_membership);
            reveal(super::legacy_bitplane_view);
            crate::specs::compact_index(self.width,self.height,self.entries@,x,y);
            crate::specs::compact_cached_summary(self.width,self.height,self.entries@,x,y,causal);
        }
        stats.coefficients_scanned += 1;
        let index = y * self.width + x;
        if state.significant_before[index] {
            let before = self.entries[index];
            let neighbors = if before & REFINED != 0 {
                0
            } else {
                significant_neighbor_count(self.summary(x, y, causal))
            };
            let context =
                crate::refinement::tier1_refinement_context(before & REFINED != 0, neighbors);
            let bit = decoder.decode(usize::from(context))?;
            stats.coding_symbols += 1;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::compact_frontier_low_bits(before,state.bitplane);
                crate::specs::compact_refinement_plane(self.width,self.height,self.entries@,x,y,state.bitplane,bit);
            }
            let refined = refine_word(before, state.bitplane, bit);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::compact_cache_value_frame(self.width,self.height,self.entries@,index as int,refined);}
            self.entries[index] = refined;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::compact_membership_cell(self.width,self.height,before_words,self.entries@,
                    super::legacy_bitplane_view(state),super::legacy_bitplane_view(state),index as int);
            }
            stats.refined_coefficients += 1;
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(state),coordinate.0<old(self).width,coordinate.1<old(self).height,
            crate::specs::compact_statistics_room(*old(stats)),
        ensures final(self).ready(state),final(self).width==old(self).width,final(self).height==old(self).height,
            (result,final(self).frame(state,final(decoder),*final(stats)))==crate::specs::part1_legacy_cleanup_cell(
                old(self).frame(state,old(decoder),*old(stats)),coordinate.0 as u16,coordinate.1 as u16,orientation,causal),
            final(stats).coefficients_scanned==old(stats).coefficients_scanned,
            crate::specs::compact_statistics_delta(*old(stats),*final(stats),2),
            forall|i:int|0<=i<final(self).entries.len() && i!=(coordinate.1*old(self).width+coordinate.0) as int
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
            forall|i:int|0<=i<final(self).entries.len() && state.significant_before@[i]
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    fn cleanup_cell(
        &mut self,
        coordinate: (usize, usize),
        state: &Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        orientation: SubbandOrientation,
        causal: bool,
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before_words=self.entries@;}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_cleanup_cell);reveal(crate::specs::part1_legacy_symbol);
            reveal(crate::specs::compact_membership);
            reveal(super::legacy_bitplane_view);
            crate::specs::compact_index(self.width,self.height,self.entries@,coordinate.0,coordinate.1);
        }
        let (x, y) = coordinate;
        let index = y * self.width + x;
        if self.entries[index] & SIG == 0 && !state.significance_visited[index] {
            let summary = self.summary(x, y, causal);
            let bit = decoder.decode(usize::from(zero_coding_context(summary, orientation)))?;
            stats.coding_symbols += 1;
            if bit {
                let marked = self.sign_and_mark(x, y, state.bitplane, summary, decoder);
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::compact_membership_cell(self.width,self.height,before_words,self.entries@,
                        super::legacy_bitplane_view(state),super::legacy_bitplane_view(state),index as int);
                }
                marked?;
                stats.coding_symbols += 1;
                stats.newly_significant += 1;
            }
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(state),coordinate.0<old(self).width,coordinate.1<old(self).height,
            old(self).entries@[(coordinate.1*old(self).width+coordinate.0) as int] & SIG==0,
            crate::specs::compact_statistics_room(*old(stats)),
        ensures final(self).ready(state),final(self).width==old(self).width,final(self).height==old(self).height,
            (result,final(self).frame(state,final(decoder),*final(stats)))==crate::specs::part1_legacy_sign_mark_stat(
                old(self).frame(state,old(decoder),*old(stats)),coordinate.0 as u16,coordinate.1 as u16,summary),
            crate::specs::compact_statistics_delta(*old(stats),*final(stats),1),
            forall|i:int|0<=i<final(self).entries.len() && state.significant_before@[i]
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
    ))]
    fn run_sign(
        &mut self,
        state: &Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        coordinate: (usize, usize),
        summary: NeighborSummary,
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before_words=self.entries@;}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::legacy_bitplane_view);
            reveal(crate::specs::compact_membership);
            crate::specs::compact_index(self.width,self.height,self.entries@,coordinate.0,coordinate.1);
        }
        let (x, y) = coordinate;
        let marked = self.sign_and_mark(x, y, state.bitplane, summary, decoder);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_membership_cell(self.width,self.height,before_words,self.entries@,
                super::legacy_bitplane_view(state),super::legacy_bitplane_view(state),(y*self.width+x) as int);
        }
        marked?;
        stats.coding_symbols += 1;
        stats.newly_significant += 1;
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.shape(),x<self.width,y<self.height,
            crate::specs::compact_cache(self.width,self.height,self.entries@),
            state.significance_visited.len()==self.entries.len(),
        ensures Ok::<bool,DecodeError>(result)==crate::specs::part1_legacy_cleanup_candidate(
            self.view(),super::legacy_bitplane_view(state),x as u16,y as u16,causal),
            result ==> self.entries@[(y*self.width+x) as int] & SIG==0,
    ))]
    fn run_candidate(&self, x: usize, y: usize, state: &Tier1BitplaneState, causal: bool) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_index(self.width,self.height,self.entries@,x,y);
            reveal(crate::specs::part1_legacy_cleanup_candidate);reveal(super::legacy_bitplane_view);
        }
        self.entries[y * self.width + x] & SIG == 0
            && !state.significance_visited[y * self.width + x]
            && significant_neighbor_count(self.summary(x, y, causal)) == 0
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(old(state)),coordinate.0<old(self).width,
            coordinate.2<=coordinate.3,0<coordinate.3<=4,coordinate.1+coordinate.3<=old(self).height,
            !coordinate.4 ==> context.0 is Cleanup,
            crate::specs::compact_statistics_le(*old(stats),
                (crate::specs::compact_scan_bound(old(self).width,coordinate.1,coordinate.3,coordinate.0)+4+2*coordinate.2) as nat),
            if context.0 is MagnitudeRefinement{
                crate::specs::compact_refinement_pending(old(self).width,old(self).height,old(self).entries@,
                    super::legacy_bitplane_view(old(state)),coordinate.1,coordinate.3,coordinate.0,coordinate.2)
            }else{crate::specs::compact_before_frontier(old(self).entries@,super::legacy_bitplane_view(old(state)),context.0 is Cleanup)},
        ensures final(self).ready(final(state)),final(self).width==old(self).width,final(self).height==old(self).height,
            crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(final(state))),
            (result,final(self).frame(final(state),final(decoder),*final(stats)))==crate::specs::compact_rows_model(
                old(self).frame(old(state),old(decoder),*old(stats)),context.0,context.1,context.2,
                coordinate.0,coordinate.1,coordinate.2,coordinate.3,coordinate.4),
            crate::specs::compact_statistics_le(*final(stats),
                (crate::specs::compact_scan_bound(old(self).width,coordinate.1,coordinate.3,coordinate.0)+4+2*coordinate.3) as nat),
            if context.0 is MagnitudeRefinement{
                result.is_ok() ==> crate::specs::compact_refinement_pending(final(self).width,final(self).height,final(self).entries@,
                    super::legacy_bitplane_view(final(state)),coordinate.1,coordinate.3,coordinate.0,coordinate.3)
            }else{crate::specs::compact_before_frontier(final(self).entries@,super::legacy_bitplane_view(final(state)),context.0 is Cleanup)},
    ))]
    fn rows(
        &mut self,
        state: &mut Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        context: (Tier1PassKind, SubbandOrientation, bool),
        coordinate: (usize, usize, usize, usize, bool),
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        let (x, stripe, mut row, rows, scan) = coordinate;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial=self.frame(state,decoder,*stats);
            let ghost goal=crate::specs::compact_rows_model(initial,context.0,context.1,context.2,x,stripe,row,rows,scan);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::compact_membership);
            crate::specs::compact_column_geometry(self.width,self.height,self.entries@,x,stripe,rows);
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant coordinate.2<=row<=rows,rows>0,rows<=4,stripe+rows<=self.height,x<self.width,
                x==coordinate.0,stripe==coordinate.1,rows==coordinate.3,scan==coordinate.4,
                !scan ==> context.0 is Cleanup,
                self.ready(state),self.width==old(self).width,self.height==old(self).height,
                crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(state)),
                initial==old(self).frame(old(state),old(decoder),*old(stats)),
                goal==crate::specs::compact_rows_model(initial,context.0,context.1,context.2,
                    coordinate.0,coordinate.1,coordinate.2,coordinate.3,coordinate.4),
                goal==crate::specs::compact_rows_model(self.frame(state,decoder,*stats),context.0,context.1,context.2,x,stripe,row,rows,scan),
                crate::specs::compact_statistics_le(*stats,(crate::specs::compact_scan_bound(self.width,stripe,rows,x)+4+2*row) as nat),
                if context.0 is MagnitudeRefinement{
                    crate::specs::compact_refinement_pending(self.width,self.height,self.entries@,super::legacy_bitplane_view(state),stripe,rows,x,row)
                }else{crate::specs::compact_before_frontier(self.entries@,super::legacy_bitplane_view(state),context.0 is Cleanup)},
            decreases rows-row,
        ))]
        while row < rows {
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before_words=self.entries@;let ghost before_state=super::legacy_bitplane_view(state);let ghost prior_statistics=*stats;}
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part1_legacy_rows);reveal(crate::specs::part1_legacy_cleanup_rows);
                reveal(crate::specs::compact_membership);
                reveal(super::legacy_bitplane_view);
                crate::specs::compact_column_geometry(self.width,self.height,self.entries@,x,stripe,rows);
                crate::specs::compact_index(self.width,self.height,self.entries@,x,(stripe+row) as usize);
                if context.0 is MagnitudeRefinement{
                    assert(!crate::specs::compact_processed(stripe,rows,x,row,x as int,(stripe+row) as int));
                    if state.significant_before@[((stripe+row)*self.width+x) as int]{
                        assert(((self.entries@[((stripe+row)*self.width+x) as int]>>32)&63)>state.bitplane);
                        assert(crate::specs::compact_refinement_frontier(self.entries@[((stripe+row)*self.width+x) as int],state.bitplane));
                    }
                }
            }
            let decoded = match context.0 {
                Tier1PassKind::SignificancePropagation => self.sig_cell(
                    (x, stripe + row),
                    state,
                    decoder,
                    context.1,
                    context.2,
                    stats,
                ),
                Tier1PassKind::MagnitudeRefinement => {
                    self.refine_cell(x, stripe + row, state, decoder, context.2, stats)
                }
                Tier1PassKind::Cleanup => {
                    if scan {
                        stats.coefficients_scanned += 1;
                    }
                    self.cleanup_cell(
                        (x, stripe + row),
                        state,
                        decoder,
                        context.1,
                        context.2,
                        stats,
                    )
                }
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::compact_statistics_delta(prior_statistics,*stats,2));
                assert(crate::specs::compact_statistics_le(*stats,(crate::specs::compact_scan_bound(self.width,stripe,rows,x)+4+2*(row+1)) as nat));
                assert(crate::specs::compact_statistics_le(*stats,(crate::specs::compact_scan_bound(old(self).width,coordinate.1,coordinate.3,coordinate.0)+4+2*coordinate.3) as nat));
                if context.0 is MagnitudeRefinement{
                    if decoded.is_ok(){
                        crate::specs::compact_frontier_row_step(self.width,self.height,before_words,self.entries@,
                            super::legacy_bitplane_view(state),stripe,rows,x,row);
                    }
                }else{
                    crate::specs::compact_before_frontier_preserved(before_words,self.entries@,before_state,
                        super::legacy_bitplane_view(state),context.0 is Cleanup);
                }
            }
            decoded?;
            row += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_legacy_rows);reveal(crate::specs::part1_legacy_cleanup_rows);}
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(old(state)),coordinate.0<old(self).width,
            0<coordinate.2<=4,coordinate.1+coordinate.2<=old(self).height,
            crate::specs::compact_statistics_le(*old(stats),crate::specs::compact_scan_bound(old(self).width,coordinate.1,coordinate.2,coordinate.0)),
            if context.0 is MagnitudeRefinement{
                crate::specs::compact_refinement_pending(old(self).width,old(self).height,old(self).entries@,
                    super::legacy_bitplane_view(old(state)),coordinate.1,coordinate.2,coordinate.0,0)
            }else{crate::specs::compact_before_frontier(old(self).entries@,super::legacy_bitplane_view(old(state)),context.0 is Cleanup)},
        ensures final(self).ready(final(state)),final(self).width==old(self).width,final(self).height==old(self).height,
            crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(final(state))),
            (result,final(self).frame(final(state),final(decoder),*final(stats)))==crate::specs::compact_column_model(
                old(self).frame(old(state),old(decoder),*old(stats)),context.0,context.1,context.2,coordinate.0,coordinate.1,coordinate.2),
            crate::specs::compact_statistics_le(*final(stats),crate::specs::compact_scan_bound(old(self).width,coordinate.1,coordinate.2,(coordinate.0+1) as usize)),
            if context.0 is MagnitudeRefinement{
                result.is_ok() ==> crate::specs::compact_refinement_pending(final(self).width,final(self).height,final(self).entries@,
                    super::legacy_bitplane_view(final(state)),coordinate.1,coordinate.2,coordinate.0,coordinate.2)
            }else{crate::specs::compact_before_frontier(final(self).entries@,super::legacy_bitplane_view(final(state)),context.0 is Cleanup)},
    ))]
    fn column(
        &mut self,
        state: &mut Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        context: (Tier1PassKind, SubbandOrientation, bool),
        coordinate: (usize, usize, usize),
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        let (x, stripe, rows) = coordinate;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::compact_membership);
            crate::specs::compact_column_geometry(self.width,self.height,self.entries@,x,stripe,rows);
            crate::specs::compact_counter_algebra(self.width,stripe,rows,x);
        }
        if !matches!(context.0, Tier1PassKind::Cleanup) {
            return self.rows(state, decoder, context, (x, stripe, 0, rows, true), stats);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_cleanup_column);
            reveal(crate::specs::part1_legacy_cleanup_run);
            reveal(crate::specs::part1_legacy_symbol);
        }
        let run = rows == 4
            && self.run_candidate(x, stripe, state, context.2)
            && self.run_candidate(x, stripe + 1, state, context.2)
            && self.run_candidate(x, stripe + 2, state, context.2)
            && self.run_candidate(x, stripe + 3, state, context.2);
        if !run {
            return self.rows(state, decoder, context, (x, stripe, 0, rows, true), stats);
        }
        stats.coefficients_scanned += 4;
        stats.run_mode_columns += 1;
        let interrupted = decoder.decode(RUN_LENGTH_CONTEXT)?;
        stats.coding_symbols += 1;
        if interrupted {
            #[cfg(verus_keep_ghost)]
            proof! {reveal(crate::specs::part1_legacy_cleanup_interrupt);}
            let high = decoder.decode(UNIFORM_CONTEXT)?;
            let low = decoder.decode(UNIFORM_CONTEXT)?;
            stats.coding_symbols += 2;
            let row = if high {
                if low { 3 } else { 2 }
            } else if low {
                1
            } else {
                0
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(row==0 || row==1 || row==2 || row==3);
                assert(self.entries@[((stripe+row)*self.width+x) as int] & SIG==0);
            }
            let summary = self.summary(x, stripe + row, context.2);
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before_words=self.entries@;let ghost before_state=super::legacy_bitplane_view(state);}
            let marked = self.run_sign(state, decoder, (x, stripe + row), summary, stats);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::compact_before_frontier_preserved(before_words,self.entries@,before_state,super::legacy_bitplane_view(state),true);}
            marked?;
            self.rows(
                state,
                decoder,
                context,
                (x, stripe, row + 1, rows, false),
                stats,
            )?;
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(old(state)),crate::specs::compact_pass_order(super::legacy_bitplane_view(old(state)),kind),
            crate::specs::compact_before_frontier(old(self).entries@,super::legacy_bitplane_view(old(state)),kind is Cleanup),
        ensures final(self).ready(final(state)),final(self).width==old(self).width,final(self).height==old(self).height,
            (result,final(self).view(),super::legacy_bitplane_view(final(state)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
                ==crate::specs::compact_pass_model(old(self).view(),super::legacy_bitplane_view(old(state)),
                    crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),kind,orientation,causal),
            crate::specs::compact_pass_flags(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(final(state)),kind,result.is_ok()),
            match result{Err(_)=>true,Ok(statistics)=>crate::specs::compact_statistics_le(statistics,crate::specs::compact_stripe_bound(old(self).width,old(self).height))
                && crate::specs::compact_before_frontier(final(self).entries@,super::legacy_bitplane_view(final(state)),!(kind is SignificancePropagation))},
    ))]
    fn pass(
        &mut self,
        state: &mut Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        kind: Tier1PassKind,
        orientation: SubbandOrientation,
        causal: bool,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        let mut stats = ht_statistics_zero();
        let mut stripe = 0;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial=self.frame(state,decoder,stats);
            let ghost goal=crate::specs::compact_pass_model(initial.plane,initial.state,initial.symbols,kind,orientation,causal);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::legacy_bitplane_view);
            reveal(crate::specs::compact_pass_model);
            reveal(crate::specs::compact_membership);reveal(crate::specs::compact_before_frontier);
            if kind is MagnitudeRefinement{crate::specs::compact_frontier_initial(self.width,self.height,self.entries@,
                super::legacy_bitplane_view(state),if self.height<4{self.height}else{4});}
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant stripe<=self.height,self.ready(state),self.width==old(self).width,self.height==old(self).height,
                crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(state)),
                initial==old(self).frame(old(state),old(decoder),crate::specs::tier1_statistics_zero()),
                goal==crate::specs::compact_pass_model(initial.plane,initial.state,initial.symbols,kind,orientation,causal),
                goal==crate::specs::compact_pass_suffix(self.frame(state,decoder,stats),stripe,kind,orientation,causal),
                crate::specs::compact_statistics_le(stats,crate::specs::compact_stripe_bound(self.width,stripe)),
                if kind is MagnitudeRefinement{
                    crate::specs::compact_refinement_pending(self.width,self.height,self.entries@,super::legacy_bitplane_view(state),
                        stripe,if self.height-stripe<4{(self.height-stripe) as usize}else{4},0,0)
                }else{crate::specs::compact_before_frontier(self.entries@,super::legacy_bitplane_view(state),kind is Cleanup)},
            decreases self.height-stripe,
        ))]
        while stripe < self.height {
            #[cfg(feature = "cooperative-deadlines")]
            crate::deadline::checkpoint()?;
            #[cfg(verus_keep_ghost)]
            proof! {reveal(crate::specs::part1_legacy_stripes);}
            let rows = (self.height - stripe).min(4);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::compact_counter_algebra(self.width,stripe,rows,0);}
            let mut x = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant x<=self.width,stripe<self.height,0<rows<=4,stripe+rows<=self.height,
                    self.ready(state),self.width==old(self).width,self.height==old(self).height,
                    crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(state)),
                    initial==old(self).frame(old(state),old(decoder),crate::specs::tier1_statistics_zero()),
                    goal==crate::specs::compact_pass_model(initial.plane,initial.state,initial.symbols,kind,orientation,causal),
                    goal==crate::specs::compact_column_suffix(self.frame(state,decoder,stats),x,stripe,rows,kind,orientation,causal),
                    crate::specs::compact_statistics_le(stats,crate::specs::compact_scan_bound(self.width,stripe,rows,x)),
                    if kind is MagnitudeRefinement{
                        crate::specs::compact_refinement_pending(self.width,self.height,self.entries@,super::legacy_bitplane_view(state),stripe,rows,x,0)
                    }else{crate::specs::compact_before_frontier(self.entries@,super::legacy_bitplane_view(state),kind is Cleanup)},
                decreases self.width-x,
            ))]
            while x < self.width {
                #[cfg(verus_keep_ghost)]
                proof! {reveal(crate::specs::part1_legacy_columns);}
                self.column(
                    state,
                    decoder,
                    (kind, orientation, causal),
                    (x, stripe, rows),
                    &mut stats,
                )?;
                #[cfg(verus_keep_ghost)]
                proof! {if kind is MagnitudeRefinement{
                    crate::specs::compact_frontier_column_end(self.width,self.height,self.entries@,super::legacy_bitplane_view(state),stripe,rows,x);
                }}
                x += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part1_legacy_columns);
                crate::specs::compact_counter_algebra(self.width,stripe,rows,0);
                if kind is MagnitudeRefinement{
                    crate::specs::compact_frontier_stripe_end(self.width,self.height,self.entries@,super::legacy_bitplane_view(state),stripe,rows,
                        if self.height-stripe-rows<4{(self.height-stripe-rows) as usize}else{4});
                }
            }
            stripe += rows;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_stripes);
            if kind is MagnitudeRefinement{crate::specs::compact_frontier_finished(self.width,self.height,self.entries@,super::legacy_bitplane_view(state));}
        }
        match kind {
            Tier1PassKind::SignificancePropagation => {
                state.significance_propagation_complete = true
            }
            Tier1PassKind::MagnitudeRefinement => state.magnitude_refinement_complete = true,
            Tier1PassKind::Cleanup => state.cleanup_complete = true,
        }
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::compact_membership);reveal(crate::specs::compact_before_frontier);}
        Ok(stats)
    }
}

impl Tier1CodeBlockDecoder {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result==crate::specs::compact_eligible(super::tier1_decoder_state(self),passes,decoded,wide_bytes),
    ))]
    fn compact_eligible(&self, passes: u32, decoded: u64, wide_bytes: usize) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(super::tier1_decoder_state);reveal(super::code_block_plane_view);}
        let width = usize::from(self.plane.width);
        let height = usize::from(self.plane.height);
        #[cfg(verus_keep_ghost)]
        proof! {assert(width*height<=usize::MAX) by(nonlinear_arith) requires width<=65535,height<=65535;}
        let count = width * height;
        if self.next_pass != 0
            || self.decoded_segments != 0
            || self.bitplane >= 31
            || self.bitplane_state.is_some()
            || self.legacy_segment.is_some()
            || passes != self.maximum_passes
            || passes != 3 * (u32::from(self.bitplane) + 1) - 2
            || count == 0
            || count > 4096
            || self.plane.coefficients.len() != count
            || !matches!(self.style.block_coding, Tier1BlockCoding::Legacy)
            || self.style.force_high_throughput
            || self.style.selective_arithmetic_coding_bypass
            || self.style.reset_contexts
            || self.style.terminate_all_passes
            || self.style.segmentation_symbols
        {
            return false;
        }
        let Some(per_cell) = (wide_bytes as u64).checked_add(10) else {
            #[cfg(verus_keep_ghost)]
            proof! {assert(count*(wide_bytes+10)>decoded) by(nonlinear_arith)
            requires count>0,wide_bytes+10>u64::MAX,decoded<=u64::MAX;}
            return false;
        };
        let Some(bytes) = (count as u64).checked_mul(per_cell) else {
            return false;
        };
        if bytes > decoded {
            return false;
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index<=count,count==self.plane.coefficients.len(),
                crate::specs::compact_admission(super::tier1_decoder_state(self),passes,decoded,wide_bytes),
                forall|i:int|0<=i<index ==> super::coefficient_raw_view(self.plane.coefficients@[i])==crate::specs::tier1_empty_coefficient(),
            decreases count-index,
        ))]
        while index < count {
            let c = self.plane.coefficients[index];
            if c.magnitude != 0
                || c.magnitude_high[0] != 0
                || c.magnitude_high[1] != 0
                || c.magnitude_high[2] != 0
                || c.magnitude_high[3] != 0
                || c.magnitude_high[4] != 0
                || c.legacy_bitplane.is_some()
                || c.significant
                || c.negative
                || c.refined
            {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(super::coefficient_raw_view);
                    reveal(super::code_block_plane_view);
                    let raw=super::coefficient_raw_view(c);
                    assert(raw.limbs[0]==c.magnitude);
                    assert(raw.limbs[1]==c.magnitude_high[0]);
                    assert(raw.limbs[2]==c.magnitude_high[1]);
                    assert(raw.limbs[3]==c.magnitude_high[2]);
                    assert(raw.limbs[4]==c.magnitude_high[3]);
                    assert(raw.limbs[5]==c.magnitude_high[4]);
                    assert(crate::specs::tier1_empty_coefficient().limbs==seq![0u64,0u64,0u64,0u64,0u64,0u64]) by(compute);
                    assert(super::coefficient_raw_view(c)!=crate::specs::tier1_empty_coefficient());
                    assert(super::code_block_plane_view(&self.plane).coefficients[index as int]==super::coefficient_raw_view(c));
                    assert(!crate::specs::compact_pristine(super::code_block_plane_view(&self.plane)));
                }
                return false;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(super::coefficient_raw_view(c).limbs =~= crate::specs::tier1_empty_coefficient().limbs);
                assert(super::coefficient_raw_view(c)==crate::specs::tier1_empty_coefficient());
            }
            index += 1;
        }
        true
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures match result{
            None=>super::tier1_decoder_state(final(self))==super::tier1_decoder_state(old(self))
                && crate::mq::mq_decoder_view(final(decoder))==crate::mq::mq_decoder_view(old(decoder))
                && !crate::specs::compact_eligible(super::tier1_decoder_state(old(self)),passes,
                    crate::limits::resource_decoded_bytes_limit(limits),core::mem::size_of::<CoefficientState>()),
            Some(value)=>crate::specs::compact_eligible(super::tier1_decoder_state(old(self)),passes,
                    crate::limits::resource_decoded_bytes_limit(limits),core::mem::size_of::<CoefficientState>())
                && crate::specs::compact_inner_result(crate::specs::Part1LegacySegmentRun {
                    decoder:super::tier1_decoder_state(old(self)),
                    symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                    statistics:crate::specs::tier1_statistics_zero(),
                },passes,(value,super::tier1_decoder_state(final(self)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder)))))
                && crate::specs::part2_legacy_inner_body_result(crate::specs::Part1LegacySegmentRun {
                    decoder:super::tier1_decoder_state(old(self)),
                    symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                    statistics:crate::specs::tier1_statistics_zero(),
                },passes,(value,super::tier1_decoder_state(final(self)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))),
        },
    ))]
    pub(super) fn try_compact_legacy(
        &mut self,
        decoder: &mut MqDecoder<'_>,
        passes: u32,
        limits: &ResourceLimits,
    ) -> Option<Result<Tier1PassStatistics, DecodeError>> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial=crate::specs::Part1LegacySegmentRun {
                decoder:super::tier1_decoder_state(self),
                symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),
                statistics:crate::specs::tier1_statistics_zero(),
            };
        }
        if !self.compact_eligible(
            passes,
            limits.maximum_decoded_bytes(),
            core::mem::size_of::<CoefficientState>(),
        ) {
            return None;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::tier1_decoder_state);reveal(super::code_block_plane_view);
            assert(self.plane.width>0 && self.plane.height>0
                && self.plane.width<=4096 && self.plane.height<=4096) by(nonlinear_arith)
                requires self.plane.width as nat*self.plane.height as nat>0,
                    self.plane.width as nat*self.plane.height as nat<=4096;
        }
        let mut packed = match new_compact_plane(
            usize::from(self.plane.width),
            usize::from(self.plane.height),
        ) {
            Ok(v) => v,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::compact_inner_first_error(initial,passes,error);
                    crate::specs::compact_original_first_error(initial,passes);
                }
                return Some(Err(error));
            }
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_empty_word();
            assert(initial.decoder==super::tier1_decoder_state(self));
            assert(EMPTY==0x3f_0000_0000u64) by(compute);
            crate::specs::compact_fresh_projection(packed.width,packed.height,packed.entries@,initial.decoder.plane);
            crate::specs::compact_budget_monotone(initial.decoder,passes,crate::limits::resource_decoded_bytes_limit(limits),
                core::mem::size_of::<CoefficientState>());
            assert forall|i:int|0<=i<packed.entries.len() implies !crate::specs::compact_coefficient(packed.entries@[i]).significant by{
                assert(packed.entries@[i]==EMPTY);
            }
            crate::specs::compact_phase_initial(self.bitplane,packed.width,packed.height,packed.entries@);
        }
        let result = self.compact_passes(&mut packed, decoder, passes);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_inner_observed(initial,passes,(result,self.compact_view(&packed),
                crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder))));
        }
        packed.commit(&mut self.plane);
        Some(result)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).bitplane<31,
            crate::specs::compact_block_phase(ghost_top@,ghost_decoded@,packed.width,packed.height,packed.entries@,
                old(self).bitplane,super::legacy_bitplane_option_view(&old(self).bitplane_state)),
            ghost_decoded@<3*(ghost_top@ as nat+1)-2,
        ensures super::tier1_decoder_state(final(self))==(crate::specs::Tier1DecoderState {
                bitplane_state:super::legacy_bitplane_option_view(&final(self).bitplane_state),
                ..super::tier1_decoder_state(old(self))}),
            crate::specs::part2_legacy_ensure_result(old(self).compact_view(packed),(result,final(self).compact_view(packed))),
            match result {
                Err(error)=>error==DecodeError::AllocationFailed && final(self).compact_view(packed)==old(self).compact_view(packed),
                Ok(())=>final(self).bitplane_state.is_some()
                    && crate::specs::part1_legacy_ensure_bitplane(old(self).compact_view(packed))==(Ok(()),final(self).compact_view(packed))
                    && crate::specs::compact_membership(packed.width,packed.height,packed.entries@,
                        super::legacy_bitplane_option_view(&final(self).bitplane_state)->Some_0)
                    && (super::legacy_bitplane_option_view(&final(self).bitplane_state)->Some_0).bitplane==old(self).bitplane
                    && crate::specs::compact_pass_order(
                        super::legacy_bitplane_option_view(&final(self).bitplane_state)->Some_0,
                        crate::specs::part1_legacy_pass_kind(ghost_decoded@))
                    && crate::specs::compact_before_frontier(packed.entries@,
                        super::legacy_bitplane_option_view(&final(self).bitplane_state)->Some_0,
                        crate::specs::part1_legacy_pass_kind(ghost_decoded@) is Cleanup),
            },
    ))]
    fn compact_prepare_bitplane(
        &mut self,
        packed: &CompactPlane,
        #[cfg(verus_keep_ghost)] ghost_top: Ghost<u16>,
        #[cfg(verus_keep_ghost)] ghost_decoded: Ghost<u32>,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=self.compact_view(packed);let ghost native_before=*self;}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(Tier1CodeBlockDecoder::compact_view);
            self.compact_metadata();
            crate::specs::compact_phase_shape(ghost_top@,ghost_decoded@,packed.width,packed.height,packed.entries@,
                self.bitplane,super::legacy_bitplane_option_view(&self.bitplane_state));
        }
        if self.bitplane_state.is_none() {
            let constructed = packed.initial_state(self.bitplane);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_legacy_ensure_observed(before,super::legacy_bitplane_outcome(constructed));}
            let new_state = constructed?;
            #[cfg(verus_keep_ghost)]
            proof! {
                let state=super::legacy_bitplane_view(&new_state);
                assert(crate::specs::part1_legacy_bitplane_initial(before.plane,before.bitplane)==Ok(state));
                crate::specs::compact_phase_prepare(ghost_top@,ghost_decoded@,packed.width,packed.height,packed.entries@,
                    self.bitplane,before.bitplane_state,state);
            }
            self.bitplane_state = Some(new_state);
            #[cfg(verus_keep_ghost)]
            proof! {
                Self::compact_native_store(native_before,*self);
                reveal(super::legacy_bitplane_option_view);
            }
            return Ok(());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_legacy_ensure_present(before);
            crate::specs::compact_phase_prepare(ghost_top@,ghost_decoded@,packed.width,packed.height,packed.entries@,
                self.bitplane,before.bitplane_state,before.bitplane_state->Some_0);
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).next_pass==0,old(self).bitplane_state.is_none(),old(self).bitplane<31,
            passes==old(self).maximum_passes,passes==3*(old(self).bitplane as nat+1)-2,
            !old(self).style.selective_arithmetic_coding_bypass,!old(self).style.reset_contexts,!old(self).style.segmentation_symbols,
            old(packed).view()==super::code_block_plane_view(&old(self).plane),
            crate::specs::compact_block_phase(old(self).bitplane,0,old(packed).width,old(packed).height,old(packed).entries@,old(self).bitplane,None),
        ensures final(packed).shape(),final(packed).width==old(packed).width,final(packed).height==old(packed).height,
            super::code_block_plane_view(&final(self).plane)==super::code_block_plane_view(&old(self).plane),
            crate::specs::part2_legacy_inner_body_result(crate::specs::Part1LegacySegmentRun {
                decoder:super::tier1_decoder_state(old(self)),
                symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                statistics:crate::specs::tier1_statistics_zero(),
            },passes,(result,final(self).compact_view(final(packed)),
                crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))),
            result!=Err(DecodeError::AllocationFailed) ==>
                (result,final(self).compact_view(final(packed)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
                    ==crate::specs::part1_legacy_segment_finish(crate::specs::part1_legacy_segment_run(crate::specs::Part1LegacySegmentRun {
                        decoder:super::tier1_decoder_state(old(self)),
                        symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                        statistics:crate::specs::tier1_statistics_zero(),
                    },passes as nat)),
    ))]
    fn compact_passes(
        &mut self,
        packed: &mut CompactPlane,
        decoder: &mut MqDecoder<'_>,
        passes: u32,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        let mut total = ht_statistics_zero();
        let mut decoded = 0;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial=crate::specs::Part1LegacySegmentRun {
                decoder:super::tier1_decoder_state(self),
                symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics:total,
            };
            let ghost mut prefix=Seq::<crate::specs::Part2Tier1StorageEvent>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            self.compact_metadata();self.compact_views(packed,decoder,total);
            reveal(super::legacy_bitplane_option_view);
            crate::specs::compact_phase_shape(initial.decoder.bitplane,0,packed.width,packed.height,packed.entries@,self.bitplane,None);
            crate::specs::compact_physical_start(initial.decoder);
            crate::specs::compact_progress_start(initial,passes);
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant decoded<=passes,passes==initial.decoder.maximum_passes,self.maximum_passes==passes,
                initial.decoder.bitplane<31,passes==3*(initial.decoder.bitplane as nat+1)-2,
                !initial.decoder.style.selective_arithmetic_coding_bypass,
                !initial.decoder.style.reset_contexts,!initial.decoder.style.segmentation_symbols,
                packed.shape(),self.bitplane<31,packed.width==old(packed).width,packed.height==old(packed).height,
                super::code_block_plane_view(&self.plane)==initial.decoder.plane,
                self.next_pass==decoded,self.style==initial.decoder.style,self.orientation==initial.decoder.orientation,
                crate::specs::compact_physical_frame(initial.decoder,super::tier1_decoder_state(self)),
                crate::specs::compact_block_phase(initial.decoder.bitplane,decoded,packed.width,packed.height,packed.entries@,
                    self.bitplane,super::legacy_bitplane_option_view(&self.bitplane_state)),
                crate::specs::compact_statistics_le(total,(16*packed.entries.len()*decoded) as nat),
                initial==(crate::specs::Part1LegacySegmentRun {
                    decoder:super::tier1_decoder_state(old(self)),
                    symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                    statistics:crate::specs::tier1_statistics_zero()}),
                crate::specs::compact_loop_progress(initial,passes,prefix,self.compact_run(packed,decoder,total),(passes-decoded) as nat),
            decreases passes-decoded,
        ))]
        while decoded < passes {
            total = self.compact_scheduled_pass(
                packed,
                decoder,
                total,
                #[cfg(verus_keep_ghost)]
                verus_exec_expr!(Ghost(initial)),
                #[cfg(verus_keep_ghost)]
                verus_exec_expr!(Ghost(passes)),
                #[cfg(verus_keep_ghost)]
                verus_exec_expr!(Ghost(decoded)),
                #[cfg(verus_keep_ghost)]
                verus_exec_expr!(Ghost(prefix)),
            )?;
            #[cfg(verus_keep_ghost)]
            proof! {
                prefix=choose|joined:Seq<crate::specs::Part2Tier1StorageEvent>|
                    #[trigger] crate::specs::compact_loop_progress(initial,passes,joined,self.compact_run(packed,decoder,total),
                        (passes-decoded-1) as nat);
            }
            decoded += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_progress_finish(initial,passes,prefix,self.compact_run(packed,decoder,total));
        }
        Ok(total)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires {
            let initial=ghost_initial@;let passes=ghost_passes@;let decoded=ghost_decoded@;let prefix=ghost_prefix@;
            decoded<passes && passes==initial.decoder.maximum_passes && old(self).maximum_passes==passes
            && initial.decoder.bitplane<31 && passes==3*(initial.decoder.bitplane as nat+1)-2
            && !initial.decoder.style.selective_arithmetic_coding_bypass
            && !initial.decoder.style.reset_contexts && !initial.decoder.style.segmentation_symbols
            && old(packed).shape() && old(self).bitplane<31
            && super::code_block_plane_view(&old(self).plane)==initial.decoder.plane
            && old(self).next_pass==decoded && old(self).style==initial.decoder.style && old(self).orientation==initial.decoder.orientation
            && crate::specs::compact_physical_frame(initial.decoder,super::tier1_decoder_state(old(self)))
            && crate::specs::compact_block_phase(initial.decoder.bitplane,decoded,old(packed).width,old(packed).height,old(packed).entries@,
                old(self).bitplane,super::legacy_bitplane_option_view(&old(self).bitplane_state))
            && crate::specs::compact_statistics_le(total,(16*old(packed).entries.len()*decoded) as nat)
            && crate::specs::compact_loop_progress(initial,passes,prefix,old(self).compact_run(old(packed),old(decoder),total),
                (passes-decoded) as nat)
        },
        ensures {
            let initial=ghost_initial@;let passes=ghost_passes@;let decoded=ghost_decoded@;
            final(packed).shape() && final(packed).width==old(packed).width && final(packed).height==old(packed).height
            && super::code_block_plane_view(&final(self).plane)==initial.decoder.plane
            && final(self).maximum_passes==passes && final(self).style==initial.decoder.style
            && final(self).orientation==initial.decoder.orientation
            && crate::specs::compact_physical_frame(initial.decoder,super::tier1_decoder_state(final(self)))
            && match result {
                Err(error)=>crate::specs::part2_legacy_inner_body_result(initial,passes,
                    (Err(error),final(self).compact_view(final(packed)),
                        crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder)))))
                    && (error!=DecodeError::AllocationFailed ==>
                        (Err(error),final(self).compact_view(final(packed)),
                            crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
                            ==crate::specs::part1_legacy_segment_finish(crate::specs::part1_legacy_segment_run(initial,passes as nat))),
                Ok(statistics)=>final(self).next_pass==decoded+1 && final(self).bitplane<31
                    && crate::specs::compact_block_phase(initial.decoder.bitplane,(decoded+1) as u32,
                        final(packed).width,final(packed).height,final(packed).entries@,final(self).bitplane,
                        super::legacy_bitplane_option_view(&final(self).bitplane_state))
                    && crate::specs::compact_statistics_le(statistics,(16*final(packed).entries.len()*(decoded+1)) as nat)
                    && exists|joined:Seq<crate::specs::Part2Tier1StorageEvent>|
                        #[trigger] crate::specs::compact_loop_progress(initial,passes,joined,
                            final(self).compact_run(final(packed),final(decoder),statistics),(passes-decoded-1) as nat),
            }
        },
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    fn compact_scheduled_pass(
        &mut self,
        packed: &mut CompactPlane,
        decoder: &mut MqDecoder<'_>,
        mut total: Tier1PassStatistics,
        #[cfg(verus_keep_ghost)] ghost_initial: Ghost<crate::specs::Part1LegacySegmentRun>,
        #[cfg(verus_keep_ghost)] ghost_passes: Ghost<u32>,
        #[cfg(verus_keep_ghost)] ghost_decoded: Ghost<u32>,
        #[cfg(verus_keep_ghost)] ghost_prefix: Ghost<Seq<crate::specs::Part2Tier1StorageEvent>>,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial=ghost_initial@;let ghost passes=ghost_passes@;
            let ghost decoded=ghost_decoded@;let ghost prefix=ghost_prefix@;
        }
        #[cfg(feature = "cooperative-deadlines")]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before_step=self.compact_run(packed,decoder,total);
            let ghost before_words=packed.entries@;
            let ghost remaining=(passes-decoded) as nat;
            let ghost physical_before=super::tier1_decoder_state(self);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            self.compact_metadata();self.compact_views(packed,decoder,total);
            crate::specs::compact_block_schedule(initial.decoder.bitplane,decoded);
            crate::specs::compact_phase_shape(initial.decoder.bitplane,decoded,packed.width,packed.height,packed.entries@,
                self.bitplane,super::legacy_bitplane_option_view(&self.bitplane_state));
            reveal(super::legacy_bitplane_option_view);
        }
        let kind = self.style.pass_plan(self.next_pass).kind;
        let prepared = self.compact_prepare_bitplane(
            packed,
            #[cfg(verus_keep_ghost)]
            verus_exec_expr!(Ghost(initial.decoder.bitplane)),
            #[cfg(verus_keep_ghost)]
            verus_exec_expr!(Ghost(decoded)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            self.compact_metadata();self.compact_views(packed,decoder,total);
            crate::specs::compact_physical_updated(initial.decoder,physical_before,super::tier1_decoder_state(self));
            crate::specs::compact_physical_fields(initial.decoder,super::tier1_decoder_state(self));
            if let Err(error)=prepared {
                crate::specs::compact_allocation_error_exit(initial,passes,before_step,remaining,prefix,kind,error);
            }
        }
        prepared?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost ready=self.compact_view(packed);let ghost ready_state=ready.bitplane_state->Some_0;
        let ghost physical_ready=super::tier1_decoder_state(self);}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::tier1_decoder_state);
            self.compact_views(packed,decoder,total);
            assert(crate::specs::compact_physical_frame(initial.decoder,physical_ready)) by{
                assert(physical_ready==(crate::specs::Tier1DecoderState {
                    next_pass:physical_ready.next_pass,bitplane:physical_ready.bitplane,bitplane_state:physical_ready.bitplane_state,..physical_before}));
                crate::specs::compact_physical_updated(initial.decoder,physical_before,physical_ready);
            }
            self.compact_metadata();self.compact_views(packed,decoder,total);
            assert(self.bitplane_state.is_some());
        }
        let pass = packed.pass(
            self.bitplane_state
                .as_mut()
                .ok_or_else(invalid_code_block)?,
            decoder,
            kind,
            self.orientation,
            self.style.vertical_causal_context,
        );
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost pass_effect=(pass,self.compact_view(packed),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)));
            let ghost expected=crate::specs::part2_legacy_step_after_pass(before_step,kind,pass_effect);
            let ghost after_state=self.compact_view(packed).bitplane_state->Some_0;
            let ghost physical_pass=super::tier1_decoder_state(self);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::tier1_decoder_state);
            self.compact_metadata();
            assert(physical_pass==(crate::specs::Tier1DecoderState {bitplane_state:physical_pass.bitplane_state,..physical_ready}));
            crate::specs::compact_physical_updated(initial.decoder,physical_ready,physical_pass);
            crate::specs::compact_pass_store_frame(physical_ready,physical_pass,ready.plane,packed.view());
            self.compact_metadata();self.compact_views(packed,decoder,total);
            crate::specs::compact_physical_fields(initial.decoder,physical_pass);
            let effect=(pass,packed.view(),after_state,crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)));
            crate::specs::compact_pass_observed(before_step.decoder,before_step.symbols->Mq_0,kind,ready,effect);
            assert(self.compact_view(packed)==(crate::specs::Tier1DecoderState {plane:effect.1,bitplane_state:Some(effect.2),..ready}));
            if pass.is_err(){
                assert(crate::specs::part2_legacy_inner_body_result(initial,passes,pass_effect)
                    && (pass!=Err(DecodeError::AllocationFailed) ==> pass_effect==crate::specs::part1_legacy_segment_finish(
                        crate::specs::part1_legacy_segment_run(initial,passes as nat)))) by{
                    crate::specs::compact_pass_error_exit(initial,passes,before_step,remaining,prefix,kind,pass_effect);
                }
            }
        }
        let stats = pass?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_area_bound(packed.width,packed.height,packed.entries@);
            crate::specs::compact_phase_after_pass(initial.decoder.bitplane,decoded,packed.width,packed.height,before_words,packed.entries@,
                before_step.decoder.bitplane,before_step.decoder.bitplane_state,ready_state,after_state);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost merged=crate::specs::tier1_statistics_merge(total,stats);}
        total = compact_merge_statistics(
            total,
            stats,
            #[cfg(verus_keep_ghost)]
            verus_exec_expr!(Ghost(packed.entries@.len())),
            #[cfg(verus_keep_ghost)]
            verus_exec_expr!(Ghost(decoded)),
        );
        self.next_pass += 1;
        if matches!(kind, Tier1PassKind::Cleanup) {
            self.bitplane_state = None;
            if self.next_pass < self.maximum_passes {
                self.bitplane -= 1;
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(total==merged.1);
            let physical_after=super::tier1_decoder_state(self);
            reveal(super::tier1_decoder_state);
            self.compact_metadata();
            assert(crate::specs::compact_advance_frame(physical_pass,physical_after,kind)) by{
                reveal(crate::specs::compact_advance_frame);
                reveal(super::legacy_bitplane_option_view);
            }
            crate::specs::compact_advance_fields(physical_pass,physical_after,kind);
            crate::specs::compact_physical_updated(initial.decoder,physical_pass,physical_after);
            crate::specs::compact_physical_fields(initial.decoder,physical_after);
            self.compact_metadata();self.compact_views(packed,decoder,total);
            assert(self.bitplane==crate::specs::compact_block_bitplane(initial.decoder.bitplane,(decoded+1) as u32));
            assert(super::legacy_bitplane_option_view(&self.bitplane_state)==if kind is Cleanup{None}else{Some(after_state)});
            crate::specs::compact_phase_shape(initial.decoder.bitplane,(decoded+1) as u32,packed.width,packed.height,packed.entries@,
                self.bitplane,super::legacy_bitplane_option_view(&self.bitplane_state));
            assert(expected==(Ok(()),self.compact_run(packed,decoder,total))) by{
                crate::specs::compact_success_store_frame(before_step,kind,pass_effect,stats,physical_pass,physical_after,
                    packed.view(),total,self.compact_run(packed,decoder,total));
            }
            let joined=crate::specs::compact_progress_continue(initial,passes,before_step,remaining,prefix,kind,pass_effect,self.compact_run(packed,decoder,total));
            assert(exists|next:Seq<crate::specs::Part2Tier1StorageEvent>|
                #[trigger] crate::specs::compact_loop_progress(initial,passes,next,self.compact_run(packed,decoder,total),(passes-decoded-1) as nat));
        }
        Ok(total)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires ghost_cells@<=4096,ghost_completed@<91,
        crate::specs::compact_statistics_le(total,(16*ghost_cells@*ghost_completed@) as nat),
        crate::specs::compact_statistics_le(pass,(16*ghost_cells@) as nat),
    ensures crate::specs::tier1_statistics_merge(total,pass)==(Ok(()),result),
        crate::specs::compact_statistics_le(result,(16*ghost_cells@*(ghost_completed@+1)) as nat),
))]
fn compact_merge_statistics(
    total: Tier1PassStatistics,
    pass: Tier1PassStatistics,
    #[cfg(verus_keep_ghost)] ghost_cells: Ghost<nat>,
    #[cfg(verus_keep_ghost)] ghost_completed: Ghost<u32>,
) -> Tier1PassStatistics {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::compact_total_merge(total,pass,ghost_cells@,ghost_completed@);}
    Tier1PassStatistics {
        coefficients_scanned: total.coefficients_scanned + pass.coefficients_scanned,
        coding_symbols: total.coding_symbols + pass.coding_symbols,
        newly_significant: total.newly_significant + pass.newly_significant,
        refined_coefficients: total.refined_coefficients + pass.refined_coefficients,
        run_mode_columns: total.run_mode_columns + pass.run_mode_columns,
    }
}

#[cfg(test)]
mod tests {
    use super::super::{CodeBlockPlane, Tier1CodingStyle};
    use super::*;

    #[test]
    fn scratch_is_one_real_owner_before_the_original_bitplane_owners() {
        let limits = ResourceLimits::default();
        let input = [0x84, 0x3f, 0x00, 0xff, 0x7f];
        for refusal in 0..18 {
            let mut actual = block(5, 7, 8, false);
            let mut expected = actual.clone();
            let mut mq =
                crate::mq::mq_from_input(&input, 100, limits.maximum_work_units()).unwrap();
            super::super::state::initialize_tier1_contexts(&mut mq).unwrap();
            let mut reference =
                crate::mq::mq_from_input(&input, 100, limits.maximum_work_units()).unwrap();
            super::super::state::initialize_tier1_contexts(&mut reference).unwrap();
            let passes = actual.maximum_passes;
            let result = crate::allocation::with_refusal(refusal, || {
                actual.try_compact_legacy(&mut mq, passes, &limits)
            })
            .unwrap();
            if refusal == 0 {
                assert_eq!(result, Err(DecodeError::AllocationFailed));
            } else {
                let expected_result = crate::allocation::with_refusal(refusal - 1, || {
                    expected.decode_mq_segment_passes(&mut reference, passes)
                });
                assert_eq!(result, expected_result, "refusal {refusal}");
            }
            assert_eq!(
                format!("{actual:?}"),
                format!("{expected:?}"),
                "refusal {refusal}"
            );
            assert_eq!(
                format!("{mq:?}"),
                format!("{reference:?}"),
                "refusal {refusal}"
            );
        }
    }

    #[test]
    fn compact_admission_uses_coded_bitplanes_exact_capacity_and_pristine_state() {
        let original = block(5, 7, 31, false);
        let bytes = 5 * 7 * 66;
        assert!(original.compact_eligible(
            original.maximum_passes,
            bytes,
            core::mem::size_of::<CoefficientState>()
        ));
        assert!(!original.compact_eligible(
            original.maximum_passes,
            bytes - 1,
            core::mem::size_of::<CoefficientState>()
        ));
        assert!(!original.compact_eligible(
            original.maximum_passes - 1,
            bytes,
            core::mem::size_of::<CoefficientState>()
        ));
        let wide = block(5, 7, 32, false);
        assert!(!wide.compact_eligible(wide.maximum_passes, u64::MAX, 56));
        let maximum = block(64, 64, 31, false);
        assert!(maximum.compact_eligible(
            maximum.maximum_passes,
            4096 * 66,
            core::mem::size_of::<CoefficientState>()
        ));
        for field in 0..20 {
            let mut candidate = original.clone();
            match field {
                0 => candidate.next_pass = 1,
                1 => candidate.decoded_segments = 1,
                2 => {
                    candidate.bitplane_state =
                        Some(Tier1BitplaneState::new_at_bitplane(&candidate.plane, 30).unwrap())
                }
                3 => candidate.legacy_segment = Some(candidate.legacy_segment_snapshot().unwrap()),
                4 => candidate.style.selective_arithmetic_coding_bypass = true,
                5 => candidate.style.reset_contexts = true,
                6 => candidate.style.terminate_all_passes = true,
                7 => candidate.style.segmentation_symbols = true,
                8 => candidate.style.force_high_throughput = true,
                9 => candidate.plane.coefficients[0].magnitude = 1,
                10 => candidate.plane.coefficients[0].magnitude_high[4] = 1,
                11 => candidate.plane.coefficients[0].legacy_bitplane = Some(0),
                12 => candidate.plane.coefficients[0].significant = true,
                13 => candidate.plane.coefficients[0].negative = true,
                14 => candidate.plane.coefficients[0].refined = true,
                15 => {
                    candidate.plane.coefficients.pop();
                }
                16 => candidate.style.block_coding = Tier1BlockCoding::Mixed,
                17 => candidate.style.block_coding = Tier1BlockCoding::HighThroughput,
                18 => candidate.plane.width = 0,
                _ => candidate.plane.width = 4096,
            }
            let before = format!("{candidate:?}");
            let input = [0x84];
            let mut mq = crate::mq::mq_from_input(&input, 100, 100).unwrap();
            super::super::state::initialize_tier1_contexts(&mut mq).unwrap();
            let mq_before = format!("{mq:?}");
            let passes = candidate.maximum_passes;
            assert!(
                crate::allocation::with_refusal(0, || candidate.try_compact_legacy(
                    &mut mq,
                    passes,
                    &ResourceLimits::default()
                ))
                .is_none(),
                "field {field}"
            );
            assert_eq!(format!("{candidate:?}"), before, "field {field}");
            assert_eq!(format!("{mq:?}"), mq_before, "field {field}");
        }
    }

    #[test]
    fn inherited_replay_keeps_checked_allocation_and_error_frontiers() {
        let limits = ResourceLimits::default();
        let wide_limits = limits.with_maximum_decoded_bytes(5 * 7 * 56).unwrap();
        let mut partial = block(5, 7, 8, false);
        partial
            .decode_legacy_contribution(&[0x84], 1, &limits)
            .unwrap();
        assert!(partial.legacy_segment.is_some());
        let remaining = (partial.maximum_passes - partial.next_pass) as u8;
        for refusal in 0..24 {
            let mut actual = partial.clone();
            let mut expected = partial.clone();
            let actual_result = crate::allocation::with_refusal(refusal, || {
                actual.decode_legacy_contribution(&[0x3f, 0x00, 0xff, 0x7f], remaining, &limits)
            });
            let expected_result = crate::allocation::with_refusal(refusal, || {
                expected.decode_legacy_contribution(
                    &[0x3f, 0x00, 0xff, 0x7f],
                    remaining,
                    &wide_limits,
                )
            });
            assert_eq!(actual_result, expected_result, "refusal {refusal}");
            assert_eq!(
                format!("{actual:?}"),
                format!("{expected:?}"),
                "refusal {refusal}"
            );
        }
    }

    fn block(width: u16, height: u16, planes: u16, causal: bool) -> Tier1CodeBlockDecoder {
        Tier1CodeBlockDecoder::new(
            width,
            height,
            planes,
            SubbandOrientation::Hh,
            Tier1CodingStyle {
                vertical_causal_context: causal,
                ..Tier1CodingStyle::default()
            },
        )
        .unwrap()
    }

    #[test]
    fn incremental_flags_match_checked_neighbors_after_every_mark() {
        let mut wide = CodeBlockPlane::new(7, 9).unwrap();
        let mut compact = new_compact_plane(7, 9).unwrap();
        for index in (0..63).map(|i| i * 17 % 63) {
            let (x, y) = (index % 7, index / 7);
            compact.mark(x, y, 4, index % 3 == 0);
            wide.mark_significant_at_bitplane(x as u16, y as u16, 4, index % 3 == 0)
                .unwrap();
            for causal in [false, true] {
                for yy in 0..9 {
                    for xx in 0..7 {
                        assert_eq!(
                            compact.summary(xx, yy, causal),
                            wide.neighbor_summary_with_causality(xx as u16, yy as u16, causal)
                                .unwrap()
                        );
                    }
                }
            }
        }
        compact.commit(&mut wide);
        assert!(
            wide.coefficients
                .iter()
                .all(|c| c.magnitude == 16 && c.legacy_bitplane == Some(4))
        );
    }

    #[test]
    fn bounded_complete_mq_block_reaches_compact_kernel() {
        let mut block = block(4, 4, 8, false);
        block.orientation = SubbandOrientation::Ll;
        let limits = ResourceLimits::default();
        let mut mq = crate::mq::mq_from_input(
            &[0x84, 0x3f, 0x00, 0xff, 0x7f],
            100,
            limits.maximum_work_units(),
        )
        .unwrap();
        super::super::state::initialize_tier1_contexts(&mut mq).unwrap();
        let passes = block.maximum_passes;
        assert!(block.try_compact_legacy(&mut mq, passes, &limits).is_some());
    }

    #[test]
    fn compact_matches_checked_result_and_every_visible_error_prefix() {
        for (width, height) in [(1, 1), (3, 5), (16, 16)] {
            for planes in [1, 8, 31] {
                for causal in [false, true] {
                    for input in [
                        &[0x84][..],
                        &[0xff, 0x90][..],
                        &[0x84, 0x3f, 0x00, 0xff, 0x7f][..],
                    ] {
                        for work in [1, 2, 7, 128, 100_000] {
                            let mut compact = block(width, height, planes, causal);
                            let mut scalar = compact.clone();
                            let limits = ResourceLimits::default()
                                .with_maximum_work_units(work)
                                .unwrap();
                            let scalar_limits = limits
                                .with_maximum_decoded_bytes(
                                    u64::from(width) * u64::from(height) * 56,
                                )
                                .unwrap();
                            let passes = compact.maximum_passes as u8;
                            assert_eq!(
                                compact.decode_segment(input, passes, &limits),
                                scalar.decode_segment(input, passes, &scalar_limits)
                            );
                            assert_eq!(format!("{compact:?}"), format!("{scalar:?}"));
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn compact_preserves_actual_mq_register_context_and_work_error_state() {
        for planes in [1, 8, 31] {
            for causal in [false, true] {
                for work in [1, 2, 7, 128, 100_000] {
                    let mut compact = block(5, 7, planes, causal);
                    compact.orientation = SubbandOrientation::Hl;
                    let mut scalar = compact.clone();
                    let limits = ResourceLimits::default()
                        .with_maximum_work_units(work)
                        .unwrap();
                    let input = [0x84, 0x3f, 0x00, 0xff, 0x7f];
                    let mut mq = crate::mq::mq_from_input(&input, 100, work).unwrap();
                    super::super::state::initialize_tier1_contexts(&mut mq).unwrap();
                    let mut reference = crate::mq::mq_from_input(&input, 100, work).unwrap();
                    super::super::state::initialize_tier1_contexts(&mut reference).unwrap();
                    let passes = compact.maximum_passes;
                    assert_eq!(
                        compact
                            .try_compact_legacy(&mut mq, passes, &limits)
                            .unwrap(),
                        scalar.decode_mq_segment_passes(&mut reference, passes)
                    );
                    assert_eq!(format!("{compact:?}"), format!("{scalar:?}"));
                    assert_eq!(format!("{mq:?}"), format!("{reference:?}"));
                }
            }
        }
    }
}
