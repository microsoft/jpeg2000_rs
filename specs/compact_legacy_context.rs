//! Cached bytes yield the existing checked neighbor summary, in its actual order.
use super::*;
verus! {
pub(crate) open spec fn compact_neighbor_kind(d:u32)->u8 {
    if d==3 || d==4{0u8}else if d==1 || d==6{1u8}else{2u8}
}
pub(crate) open spec fn compact_flag_step(
    before:(Result<(),crate::DecodeError>,crate::tier1::NeighborSummary),word:u64,d:u32,trim:bool,
)->(Result<(),crate::DecodeError>,crate::tier1::NeighborSummary) {
    match before.0{
        Err(_)=>before,
        Ok(())=>if compact_flag(word,d,false) && !(trim && d>=5){
            ht_neighbor_update(before.1,compact_neighbor_kind(d),compact_flag(word,d,true))
        }else{(Ok(()),before.1)},
    }
}
pub(crate) open spec fn compact_flags_fold(word:u64,trim:bool)->(Result<(),crate::DecodeError>,crate::tier1::NeighborSummary) {
    let s=(Ok(()),ht_neighbor_zero());
    let s=compact_flag_step(s,word,3,trim);
    let s=compact_flag_step(s,word,4,trim);
    let s=compact_flag_step(s,word,1,trim);
    let s=compact_flag_step(s,word,0,trim);
    let s=compact_flag_step(s,word,2,trim);
    let s=compact_flag_step(s,word,6,trim);
    let s=compact_flag_step(s,word,5,trim);
    compact_flag_step(s,word,7,trim)
}
pub(crate) proof fn compact_flag_step_frame(before:(Result<(),crate::DecodeError>,crate::tier1::NeighborSummary),word:u64,d:u32,trim:bool)
    requires d<8,
    ensures compact_neighbor_kind(d)!=0 ==> (
        compact_flag_step(before,word,d,trim).1.horizontal_significant==before.1.horizontal_significant
        && compact_flag_step(before,word,d,trim).1.horizontal_sign_balance==before.1.horizontal_sign_balance),
        compact_neighbor_kind(d)!=1 ==> (
        compact_flag_step(before,word,d,trim).1.vertical_significant==before.1.vertical_significant
        && compact_flag_step(before,word,d,trim).1.vertical_sign_balance==before.1.vertical_sign_balance),
        compact_neighbor_kind(d)!=2 ==> compact_flag_step(before,word,d,trim).1.diagonal_significant==before.1.diagonal_significant,
{}
pub(crate) proof fn compact_flags_fold_summary(word:u64,trim:bool)
    ensures compact_flags_fold(word,trim)==(Ok(()),compact_flag_summary(
        ((word>>41) as u8) & if trim{0x1fu8}else{0xffu8},
        ((word>>49) as u8) & if trim{0x1fu8}else{0xffu8})),
{
    let sig=((word>>41) as u8) & if trim{0x1fu8}else{0xffu8};
    let neg=(((word>>49) as u8) & if trim{0x1fu8}else{0xffu8}) & sig;
    assert forall|d:u32|d<8 implies
        ((sig>>d)&1)==(if compact_flag(word,d,false) && !(trim && d>=5){1u8}else{0u8})
        && ((neg>>d)&1)==(if compact_flag(word,d,false) && compact_flag(word,d,true) && !(trim && d>=5){1u8}else{0u8}) by{
        assert(((sig>>d)&1)==(if word & (1u64<<(41+d))!=0 && !(trim && d>=5){1u8}else{0u8})
            && ((neg>>d)&1)==(if word & (1u64<<(41+d))!=0 && word & (1u64<<(49+d))!=0 && !(trim && d>=5){1u8}else{0u8})) by(bit_vector)
            requires d<8,sig==((word>>41) as u8) & if trim{0x1fu8}else{0xffu8},
                neg==(((word>>49) as u8) & if trim{0x1fu8}else{0xffu8}) & sig;
    }
    let a=compact_flag_step((Ok(()),ht_neighbor_zero()),word,3,trim);
    let b=compact_flag_step(a,word,4,trim);
    assert(b.0==Ok(()));
    assert(b.1.diagonal_significant==0);
    assert(b.1.horizontal_significant==((sig>>3)&1)+((sig>>4)&1));
    assert(b.1.horizontal_sign_balance as int==((sig>>3)&1)+((sig>>4)&1)-2*(((neg>>3)&1)+((neg>>4)&1)));
    let c=compact_flag_step(b,word,1,trim);
    compact_flag_step_frame(b,word,1,trim);
    assert(c.1.diagonal_significant==0);
    let d=compact_flag_step(c,word,0,trim);
    compact_flag_step_frame(c,word,0,trim);
    assert(((sig>>0)&1)==(if compact_flag(word,0,false){1u8}else{0u8}));
    assert(sig & 1==(sig>>0)&1) by(bit_vector);
    assert(d.1.diagonal_significant==sig&1);
    let e=compact_flag_step(d,word,2,trim);
    compact_flag_step_frame(d,word,2,trim);
    assert(e.1.diagonal_significant==(sig&1)+((sig>>2)&1));
    let f=compact_flag_step(e,word,6,trim);
    compact_flag_step_frame(e,word,6,trim);
    assert(f.0==Ok(()));
    assert(f.1.vertical_significant==((sig>>1)&1)+((sig>>6)&1));
    assert(f.1.vertical_sign_balance as int==((sig>>1)&1)+((sig>>6)&1)-2*(((neg>>1)&1)+((neg>>6)&1)));
    let g=compact_flag_step(f,word,5,trim);
    compact_flag_step_frame(f,word,5,trim);
    assert(g.1.diagonal_significant==(sig&1)+((sig>>2)&1)+((sig>>5)&1));
    let h=compact_flag_step(g,word,7,trim);
    compact_flag_step_frame(g,word,7,trim);
    assert(h.0==Ok(()));
    assert(h.1.diagonal_significant==(sig&1)+((sig>>2)&1)+((sig>>5)&1)+((sig>>7)&1));
}
pub(crate) proof fn compact_flag_step_success(summary:crate::tier1::NeighborSummary,word:u64,d:u32)
    ensures compact_flag_step((Ok(()),summary),word,d,false)==if compact_flag(word,d,false){
        ht_neighbor_update(summary,compact_neighbor_kind(d),compact_flag(word,d,true))
    }else{(Ok(()),summary)},
{}
pub(crate) proof fn compact_cached_neighbor_step(
    width:usize,height:usize,words:Seq<u64>,x:usize,y:usize,d:u32,
    before:(Result<(),crate::DecodeError>,crate::tier1::NeighborSummary),
)
    requires compact_cache(width,height,words),x<width,y<height,d<8,
    ensures ht_neighbor_then(before,compact_plane(width,height,words),x as u16,y as u16,
        compact_dx(d) as i8,compact_dy(d) as i8,compact_neighbor_kind(d))
        ==compact_flag_step(before,words[(y*width+x) as int],d,false),
{
    reveal(ht_neighbor_then);reveal(ht_accumulate_neighbor);reveal(compact_flag_step);
    compact_index(width,height,words,x,y);
    assert(compact_cache_at(width,height,words,x as int,y as int,d,None));
    let nx=x as int+compact_dx(d);
    let ny=y as int+compact_dy(d);
    let word=words[(y*width+x) as int];
    assert(x as u16 as int==x && y as u16 as int==y);
    assert(compact_dx(d) as i8 as int==compact_dx(d) && compact_dy(d) as i8 as int==compact_dy(d));
    if 0<=nx<width && 0<=ny<height{
        compact_index(width,height,words,nx as usize,ny as usize);
        let index=ny*width+nx;
        let coefficient=compact_coefficient(words[index]);
        assert(tier1_raw_plane_index(compact_plane(width,height,words),nx as u16,ny as u16)==Ok(index as usize));
        assert(tier1_raw_plane_coefficient(compact_plane(width,height,words),nx as u16,ny as u16)==Ok(coefficient));
        assert(compact_flag(word,d,false)==coefficient.significant);
        if coefficient.significant{assert(compact_flag(word,d,true)==coefficient.negative);}
        assert(ht_accumulate_neighbor(compact_plane(width,height,words),x as u16,y as u16,
            compact_dx(d) as i8,compact_dy(d) as i8,compact_neighbor_kind(d),before.1)
            ==if coefficient.significant{ht_neighbor_update(before.1,compact_neighbor_kind(d),coefficient.negative)}else{(Ok(()),before.1)});
    }else{
        assert(!compact_flag(word,d,false));
        assert(ht_accumulate_neighbor(compact_plane(width,height,words),x as u16,y as u16,
            compact_dx(d) as i8,compact_dy(d) as i8,compact_neighbor_kind(d),before.1)==(Ok(()),before.1));
    }
    let actual=ht_accumulate_neighbor(compact_plane(width,height,words),x as u16,y as u16,
        compact_dx(d) as i8,compact_dy(d) as i8,compact_neighbor_kind(d),before.1);
    let expected=if compact_flag(word,d,false){
        ht_neighbor_update(before.1,compact_neighbor_kind(d),compact_flag(word,d,true))
    }else{(Ok(()),before.1)};
    assert(actual==expected);
    match before.0{
        Err(_)=>{
            assert(ht_neighbor_then(before,compact_plane(width,height,words),x as u16,y as u16,
                compact_dx(d) as i8,compact_dy(d) as i8,compact_neighbor_kind(d))==before);
            assert(compact_flag_step(before,word,d,false)==before);
        },
        Ok(())=>{
            assert(ht_neighbor_then(before,compact_plane(width,height,words),x as u16,y as u16,
                compact_dx(d) as i8,compact_dy(d) as i8,compact_neighbor_kind(d))==actual);
            assert(compact_flag_step(before,word,d,false)==expected);
        },
    }
}
pub(crate) proof fn compact_cached_summary(width:usize,height:usize,words:Seq<u64>,x:usize,y:usize,causal:bool)
    requires compact_cache(width,height,words),x<width,y<height,
    ensures ht_neighbors(compact_plane(width,height,words),x as u16,y as u16,causal)==Ok(compact_flag_summary(
        ((words[(y*width+x) as int]>>41) as u8) & if causal && y%4==3{0x1fu8}else{0xffu8},
        ((words[(y*width+x) as int]>>49) as u8) & if causal && y%4==3{0x1fu8}else{0xffu8})),
{
    compact_index(width,height,words,x,y);
    let plane=compact_plane(width,height,words);
    let word=words[(y*width+x) as int];
    let trim=causal && y%4==3;
    compact_flags_fold_summary(word,trim);
    assert(tier1_raw_plane_index(plane,x as u16,y as u16)==Ok((y*width+x) as usize));
    let a=(Ok(()),ht_neighbor_zero());
    compact_cached_neighbor_step(width,height,words,x,y,3,a);
    let b=compact_flag_step(a,word,3,trim);
    compact_cached_neighbor_step(width,height,words,x,y,4,b);
    let c=compact_flag_step(b,word,4,trim);
    compact_cached_neighbor_step(width,height,words,x,y,1,c);
    let d=compact_flag_step(c,word,1,trim);
    compact_cached_neighbor_step(width,height,words,x,y,0,d);
    let e=compact_flag_step(d,word,0,trim);
    compact_cached_neighbor_step(width,height,words,x,y,2,e);
    let f=compact_flag_step(e,word,2,trim);
    if !trim{
        compact_cached_neighbor_step(width,height,words,x,y,6,f);
        let g=compact_flag_step(f,word,6,false);
        compact_cached_neighbor_step(width,height,words,x,y,5,g);
        let h=compact_flag_step(g,word,5,false);
        compact_cached_neighbor_step(width,height,words,x,y,7,h);
    }
}
}
