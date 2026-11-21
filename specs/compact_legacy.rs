//! Physical compact-word projection into the existing, unnormalized Tier-1 model.
use super::*;
verus! {
pub(crate) open spec fn compact_coefficient(word:u64)->Tier1RawCoefficient {
    let bp=((word>>32)&63) as u16;
    Tier1RawCoefficient {
        limbs:seq![word & 0xffff_ffff,0u64,0u64,0u64,0u64,0u64],
        legacy_bitplane:if bp==63{None}else{Some(bp)},
        significant:word & (1u64<<38)!=0,
        negative:word & (1u64<<39)!=0,
        refined:word & (1u64<<40)!=0,
    }
}
pub(crate) open spec fn compact_plane(width:usize,height:usize,words:Seq<u64>)->Tier1RawPlane {
    Tier1RawPlane {width:width as u16,height:height as u16,
        coefficients:words.map_values(|word:u64|compact_coefficient(word))}
}
pub(crate) open spec fn compact_shape(width:usize,height:usize,words:Seq<u64>)->bool {
    0<width<=4096 && 0<height<=4096 && width*height==words.len() && words.len()<=4096
}
pub(crate) open spec fn compact_word_valid(word:u64)->bool {
    word>>57==0
        && (word & (1u64<<38)==0 ==> word & 0x1ff_ffff_ffff==0x3f_0000_0000)
        && (word & (1u64<<38)!=0 ==> ((word>>32)&63)<31 && word & 0xffff_ffff!=0)
        && ((word>>49) as u8 & !((word>>41) as u8))==0
}
pub(crate) open spec fn compact_pristine(plane:Tier1RawPlane)->bool {
    forall|i:int|0<=i<plane.coefficients.len() ==> #[trigger] plane.coefficients[i]==tier1_empty_coefficient()
}
pub(crate) open spec fn compact_admission(before:Tier1DecoderState,passes:u32,decoded:u64,wide_bytes:usize)->bool {
    let count=before.plane.width as nat*before.plane.height as nat;
    before.next_pass==0 && before.decoded_segments==0 && before.bitplane<31
        && before.bitplane_state.is_none() && before.legacy_segment.is_none()
        && passes==before.maximum_passes && passes==3*(before.bitplane as nat+1)-2
        && 0<count<=4096 && before.plane.coefficients.len()==count
        && before.style.block_coding is Legacy && !before.style.force_high_throughput
        && !before.style.selective_arithmetic_coding_bypass && !before.style.reset_contexts
        && !before.style.terminate_all_passes && !before.style.segmentation_symbols
        && count*(wide_bytes as nat+10)<=decoded
}
pub(crate) open spec fn compact_eligible(before:Tier1DecoderState,passes:u32,decoded:u64,wide_bytes:usize)->bool {
    compact_admission(before,passes,decoded,wide_bytes) && compact_pristine(before.plane)
}
pub(crate) open spec fn compact_mark_word(word:u64,bp:u16,negative:bool)->u64 {
    (word & !0x1ff_ffff_ffffu64) | (1u64<<bp) | ((bp as u64)<<32)
        | (1u64<<38) | if negative{1u64<<39}else{0u64}
}
pub(crate) open spec fn compact_refine_word(word:u64,bp:u16,bit:bool)->u64 {
    let next=if bit{(word+(1u64<<bp)) as u64}else{word};
    (next & !(63u64<<32)) | ((bp as u64)<<32) | (1u64<<40)
}
pub(crate) open spec fn compact_neighbor_index(width:usize,height:usize,x:int,y:int,d:u32)->Option<int> {
    let dx=compact_dx(d);
    let dy=compact_dy(d);
    if 0<=x+dx<width && 0<=y+dy<height{Some((y+dy)*width+x+dx)}else{None}
}
pub(crate) open spec fn compact_cache(width:usize,height:usize,words:Seq<u64>)->bool {
    compact_shape(width,height,words)
        && forall|x:int,y:int,d:u32|0<=x<width && 0<=y<height && d<8
            ==> #[trigger] compact_cache_at(width,height,words,x,y,d,None)
}
pub(crate) open spec fn compact_flag_summary(sig:u8,neg:u8)->crate::tier1::NeighborSummary {
    let neg=neg & sig;
    let h=(((sig>>3)&1)+((sig>>4)&1)) as u8;
    let v=(((sig>>1)&1)+((sig>>6)&1)) as u8;
    crate::tier1::NeighborSummary {
        horizontal_significant:h,vertical_significant:v,
        diagonal_significant:((sig&1)+((sig>>2)&1)+((sig>>5)&1)+((sig>>7)&1)) as u8,
        horizontal_sign_balance:(h as int-2*(((neg>>3)&1)+((neg>>4)&1))) as i8,
        vertical_sign_balance:(v as int-2*(((neg>>1)&1)+((neg>>6)&1))) as i8,
    }
}
pub(crate) proof fn compact_index(width:usize,height:usize,words:Seq<u64>,x:usize,y:usize)
    requires compact_shape(width,height,words),x<width,y<height,
    ensures y*width+x<words.len(),y*width+x<4096,
{
    assert(y*width+x<width*height) by(nonlinear_arith)
        requires x<width,y<height,width>0;
}
pub(crate) proof fn compact_empty_word()
    ensures compact_coefficient(0x3f_0000_0000)==tier1_empty_coefficient(),
        compact_word_valid(0x3f_0000_0000),
{
    assert(compact_coefficient(0x3f_0000_0000)==(Tier1RawCoefficient {
        limbs:seq![0u64,0u64,0u64,0u64,0u64,0u64],legacy_bitplane:None,
        significant:false,negative:false,refined:false,
    })) by(compute);
    assert(compact_coefficient(0x3f_0000_0000).limbs =~= tier1_empty_coefficient().limbs);
    assert(compact_word_valid(0x3f_0000_0000)) by(compute);
}
pub(crate) proof fn compact_mark_coefficient(word:u64,bp:u16,negative:bool)
    requires bp<31,
    ensures compact_coefficient(compact_mark_word(word,bp,negative))==(Tier1RawCoefficient {
        limbs:part1_magnitude_bit(bp),legacy_bitplane:Some(bp),significant:true,negative,refined:false,
    }),
{
    let marked=compact_mark_word(word,bp,negative);
    assert(marked & 0xffff_ffffu64==1u64<<bp
        && ((marked>>32)&63)==bp as u64
        && marked & (1u64<<38)!=0
        && (marked & (1u64<<39)!=0)==negative
        && marked & (1u64<<40)==0) by(bit_vector)
        requires bp<31,marked==compact_mark_word(word,bp,negative);
    assert(compact_coefficient(marked).limbs =~= part1_magnitude_bit(bp));
}
}
