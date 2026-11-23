//! Numeric frontier of actual packed entries, not a repeated loose addition bound.
use super::*;
verus! {
pub(crate) open spec fn compact_precision_word(word:u64)->bool {
    let tag=(word>>32)&63;
    word & 0xffff_ffffu64<1u64<<31
        && if word & (1u64<<38)==0{
            word & 0x1ff_ffff_ffffu64==0x3f_0000_0000u64
        }else{
            tag<31 && word & 0xffff_ffffu64!=0
                && word & (((1u64<<tag)-1) as u64)==0
        }
}
pub(crate) open spec fn compact_refinement_frontier(word:u64,bp:u16)->bool {
    compact_precision_word(word) && word & (1u64<<38)!=0 && (bp as u64)<((word>>32)&63)
}
pub(crate) proof fn compact_precision_lower_frame(left:u64,right:u64)
    requires left & 0x1ff_ffff_ffffu64==right & 0x1ff_ffff_ffffu64,
    ensures compact_precision_word(left)==compact_precision_word(right),
{
    assert(compact_precision_word(left)==compact_precision_word(right)) by(bit_vector)
        requires left & 0x1ff_ffff_ffffu64==right & 0x1ff_ffff_ffffu64;
}
pub(crate) proof fn compact_precision_mark(word:u64,bp:u16,negative:bool)
    requires bp<31,
    ensures compact_precision_word(compact_mark_word(word,bp,negative)),
{
    let marked=compact_mark_word(word,bp,negative);
    assert(compact_precision_word(marked)) by(bit_vector)
        requires bp<31,marked==compact_mark_word(word,bp,negative);
}
pub(crate) proof fn compact_frontier_low_bits(word:u64,bp:u16)
    requires compact_refinement_frontier(word,bp),
    ensures bp<31,word & 0xffff_ffffu64<1u64<<31,
        word & (((1u64<<((bp+1) as u16))-1) as u64)==0,
{
    assert(bp<31 && word & 0xffff_ffffu64<1u64<<31
        && word & (((1u64<<((bp+1) as u16))-1) as u64)==0) by(bit_vector)
        requires compact_refinement_frontier(word,bp);
}
pub(crate) proof fn compact_precision_refine(word:u64,bp:u16,bit:bool)
    requires compact_refinement_frontier(word,bp),
    ensures compact_precision_word(compact_refine_word(word,bp,bit)),
        compact_coefficient(compact_refine_word(word,bp,bit)).limbs[0]==(word & 0xffff_ffffu64)+if bit{1u64<<bp}else{0u64},
        compact_coefficient(compact_refine_word(word,bp,bit)).legacy_bitplane==Some(bp),
        compact_coefficient(compact_refine_word(word,bp,bit)).significant,
        compact_coefficient(compact_refine_word(word,bp,bit)).negative==compact_coefficient(word).negative,
        compact_coefficient(compact_refine_word(word,bp,bit)).refined,
        compact_refine_word(word,bp,bit)>>41==word>>41,
{
    compact_frontier_low_bits(word,bp);
    let refined=compact_refine_word(word,bp,bit);
    assert(compact_precision_word(refined)
        && refined & 0xffff_ffffu64==(word & 0xffff_ffffu64)+if bit{1u64<<bp}else{0u64}
        && ((refined>>32)&63)==bp as u64
        && refined & (1u64<<38)!=0
        && refined & (1u64<<39)==word & (1u64<<39)
        && refined & (1u64<<40)!=0
        && refined>>41==word>>41) by(bit_vector)
        requires compact_refinement_frontier(word,bp),refined==compact_refine_word(word,bp,bit);
}
pub(crate) proof fn compact_magnitude_value(word:u64)
    ensures part1_magnitude_value(compact_coefficient(word).limbs)==((word & 0xffff_ffffu64) as nat),
{
    let low=word & 0xffff_ffffu64;
    let limbs=compact_coefficient(word).limbs;
    assert(part1_magnitude_u64(limbs)==Some(low));
    crate::proofs::production_impl::production_legacy_magnitude_u64(limbs);
}
pub(crate) proof fn compact_refinement_plane(width:usize,height:usize,words:Seq<u64>,x:usize,y:usize,bp:u16,bit:bool)
    requires compact_shape(width,height,words),x<width,y<height,
        compact_refinement_frontier(words[(y*width+x) as int],bp),
    ensures (Ok::<(),crate::DecodeError>(()),compact_plane(width,height,words.update((y*width+x) as int,
        compact_refine_word(words[(y*width+x) as int],bp,bit))))
            ==part1_legacy_refine(compact_plane(width,height,words),x as u16,y as u16,bp,bit),
{
    compact_index(width,height,words,x,y);
    let index=(y*width+x) as int;
    let word=words[index];
    let refined=compact_refine_word(word,bp,bit);
    compact_frontier_low_bits(word,bp);
    compact_precision_refine(word,bp,bit);
    compact_magnitude_value(word);
    compact_magnitude_value(refined);
    crate::proofs::production_impl::production_tier1_value_limbs(compact_coefficient(refined).limbs);
    crate::proofs::production_impl::production_magnitude_value_bound(compact_coefficient(refined).limbs);
    vstd::bits::lemma_u64_pow2_no_overflow(bp as nat);
    vstd::bits::lemma_u64_shl_is_mul(1,bp as u64);
    assert(1u64<<bp==1u64<<(bp as u64)) by(bit_vector);
    assert((1u64<<bp) as nat==pow2(bp as nat));
    assert(tier1_raw_plane_index(compact_plane(width,height,words),x as u16,y as u16)==Ok(index as usize));
    let expected=part1_legacy_refine(compact_plane(width,height,words),x as u16,y as u16,bp,bit);
    let after=compact_plane(width,height,words.update(index,refined));
    assert(expected.0==Ok(()));
    assert(expected.1.coefficients =~= after.coefficients);
}
}
