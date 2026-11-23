//! Directional cache preservation over the physical words, including clipped edges.
use super::*;
verus! {
pub(crate) open spec fn compact_dx(d:u32)->int {
    if d==0 || d==3 || d==5{-1int}else if d==2 || d==4 || d==7{1int}else{0int}
}
pub(crate) open spec fn compact_dy(d:u32)->int {
    if d<3{-1int}else if d>=5{1int}else{0int}
}
pub(crate) open spec fn compact_flag(word:u64,d:u32,negative:bool)->bool {
    word & (1u64 << (if negative{49+d}else{41+d})) != 0
}
pub(crate) open spec fn compact_add_neighbor(word:u64,d:u32,negative:bool)->u64 {
    word | (1u64<<(41+d)) | if negative{1u64<<(49+d)}else{0u64}
}
pub(crate) open spec fn compact_cache_at(width:usize,height:usize,words:Seq<u64>,x:int,y:int,d:u32,pending:Option<(int,int,u32)>)->bool {
    let neighbor=compact_neighbor_index(width,height,x,y,d);
    let withheld=match pending{
        None=>false,
        Some((sx,sy,completed))=>neighbor==Some(sy*width+sx) && d+completed<8,
    };
    let significant=match neighbor{None=>false,Some(j)=>compact_coefficient(words[j]).significant};
    let negative=match neighbor{None=>false,Some(j)=>compact_coefficient(words[j]).significant && compact_coefficient(words[j]).negative};
    compact_flag(words[y*width+x],d,false)==(!withheld && significant)
        && compact_flag(words[y*width+x],d,true)==(!withheld && negative)
}
pub(crate) open spec fn compact_pending_cache(width:usize,height:usize,words:Seq<u64>,sx:int,sy:int,completed:u32)->bool {
    compact_shape(width,height,words) && completed<=8
        && forall|x:int,y:int,d:u32|0<=x<width && 0<=y<height && d<8
            ==> #[trigger] compact_cache_at(width,height,words,x,y,d,Some((sx,sy,completed)))
}
pub(crate) proof fn compact_opposite(d:u32)
    requires d<8,
    ensures compact_dx((7-d) as u32)==-compact_dx(d),compact_dy((7-d) as u32)==-compact_dy(d),
        compact_dx(d)!=0 || compact_dy(d)!=0,
{
    assert(d==0 || d==1 || d==2 || d==3 || d==4 || d==5 || d==6 || d==7);
}
pub(crate) proof fn compact_coordinate_injective(width:usize,x:int,y:int,nx:int,ny:int)
    requires width>0,0<=x<width,0<=nx<width,y>=0,ny>=0,y*width+x==ny*width+nx,
    ensures x==nx,y==ny,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(y*width+x,width as int,y,x);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(ny*width+nx,width as int,ny,nx);
}
pub(crate) proof fn compact_neighbor_reverse(width:usize,height:usize,x:int,y:int,tx:int,ty:int,d:u32)
    requires width>0,0<=x<width,0<=y<height,0<=tx<width,0<=ty<height,d<8,
    ensures (compact_neighbor_index(width,height,tx,ty,d)==Some(y*width+x))
        ==(compact_neighbor_index(width,height,x,y,(7-d) as u32)==Some(ty*width+tx)),
{
    compact_opposite(d);
    let opposite=(7-d) as u32;
    if compact_neighbor_index(width,height,tx,ty,d)==Some(y*width+x){
        compact_coordinate_injective(width,tx+compact_dx(d),ty+compact_dy(d),x,y);
    }
    if compact_neighbor_index(width,height,x,y,opposite)==Some(ty*width+tx){
        compact_coordinate_injective(width,x+compact_dx(opposite),y+compact_dy(opposite),tx,ty);
    }
}
pub(crate) proof fn compact_neighbor_not_self(width:usize,height:usize,x:int,y:int,d:u32)
    requires width>0,0<=x<width,0<=y<height,d<8,
    ensures compact_neighbor_index(width,height,x,y,d)!=Some(y*width+x),
{
    compact_opposite(d);
    if compact_neighbor_index(width,height,x,y,d)==Some(y*width+x){
        compact_coordinate_injective(width,x+compact_dx(d),y+compact_dy(d),x,y);
    }
}
pub(crate) proof fn compact_neighbor_bounds(width:usize,height:usize,words:Seq<u64>,x:int,y:int,d:u32)
    requires compact_shape(width,height,words),0<=x<width,0<=y<height,d<8,
    ensures match compact_neighbor_index(width,height,x,y,d){None=>true,Some(j)=>0<=j<words.len()},
{
    let nx=x+compact_dx(d);
    let ny=y+compact_dy(d);
    if 0<=nx<width && 0<=ny<height{
        compact_index(width,height,words,nx as usize,ny as usize);
    }
}
pub(crate) proof fn compact_add_neighbor_flags(word:u64,d:u32,negative:bool,other:u32)
    requires d<8,other<8,
    ensures compact_flag(compact_add_neighbor(word,d,negative),other,false)==(other==d || compact_flag(word,other,false)),
        compact_flag(compact_add_neighbor(word,d,negative),other,true)==((other==d && negative) || compact_flag(word,other,true)),
        compact_coefficient(compact_add_neighbor(word,d,negative))==compact_coefficient(word),
{
    let updated=compact_add_neighbor(word,d,negative);
    assert((updated & (1u64<<(41+other))!=0)==(other==d || (word & (1u64<<(41+other))!=0))
        && (updated & (1u64<<(49+other))!=0)==((other==d && negative) || (word & (1u64<<(49+other))!=0))
        && updated & 0xffff_ffffu64==word & 0xffff_ffffu64
        && ((updated>>32)&63)==((word>>32)&63)
        && updated & (1u64<<38)==word & (1u64<<38)
        && updated & (1u64<<39)==word & (1u64<<39)
        && updated & (1u64<<40)==word & (1u64<<40)) by(bit_vector)
        requires d<8,other<8,updated==word | (1u64<<(41+d)) | if negative{1u64<<(49+d)}else{0u64};
}
pub(crate) proof fn compact_mark_flags(word:u64,bp:u16,negative:bool,d:u32)
    requires bp<31,d<8,
    ensures compact_flag(compact_mark_word(word,bp,negative),d,false)==compact_flag(word,d,false),
        compact_flag(compact_mark_word(word,bp,negative),d,true)==compact_flag(word,d,true),
{
    let marked=compact_mark_word(word,bp,negative);
    assert((marked & (1u64<<(41+d))!=0)==(word & (1u64<<(41+d))!=0)
        && (marked & (1u64<<(49+d))!=0)==(word & (1u64<<(49+d))!=0)) by(bit_vector)
        requires bp<31,d<8,marked==compact_mark_word(word,bp,negative);
}
pub(crate) proof fn compact_cache_mark_start(width:usize,height:usize,words:Seq<u64>,x:usize,y:usize,bp:u16,negative:bool)
    requires compact_cache(width,height,words),x<width,y<height,bp<31,
        !compact_coefficient(words[(y*width+x) as int]).significant,
    ensures compact_pending_cache(width,height,
        words.update((y*width+x) as int,compact_mark_word(words[(y*width+x) as int],bp,negative)),x as int,y as int,0),
{
    compact_index(width,height,words,x,y);
    let source=(y*width+x) as int;
    let after=words.update(source,compact_mark_word(words[source],bp,negative));
    assert forall|tx:int,ty:int,d:u32|0<=tx<width && 0<=ty<height && d<8 implies
        #[trigger] compact_cache_at(width,height,after,tx,ty,d,Some((x as int,y as int,0u32))) by{
        let target=ty*width+tx;
        compact_mark_flags(words[source],bp,negative,d);
        compact_neighbor_not_self(width,height,tx,ty,d);
        assert(compact_cache_at(width,height,words,tx,ty,d,None));
        if target==source{
            compact_coordinate_injective(width,tx,ty,x as int,y as int);
        }
        match compact_neighbor_index(width,height,tx,ty,d){
            None=>{},
            Some(j)=>if j==source{}else{assert(after[j]==words[j]);},
        }
    }
}
pub(crate) proof fn compact_cache_mark_step(width:usize,height:usize,words:Seq<u64>,x:usize,y:usize,completed:u32,negative:bool)
    requires compact_pending_cache(width,height,words,x as int,y as int,completed),
        x<width,y<height,completed<8,
        compact_coefficient(words[(y*width+x) as int]).significant,
        compact_coefficient(words[(y*width+x) as int]).negative==negative,
    ensures compact_pending_cache(width,height,match compact_neighbor_index(width,height,x as int,y as int,completed){
        None=>words,
        Some(target)=>words.update(target,compact_add_neighbor(words[target],(7-completed) as u32,negative)),
    },x as int,y as int,(completed+1) as u32),
{
    let target=compact_neighbor_index(width,height,x as int,y as int,completed);
    compact_neighbor_bounds(width,height,words,x as int,y as int,completed);
    let after=match target{None=>words,Some(j)=>words.update(j,compact_add_neighbor(words[j],(7-completed) as u32,negative))};
    assert forall|tx:int,ty:int,d:u32|0<=tx<width && 0<=ty<height && d<8 implies
        #[trigger] compact_cache_at(width,height,after,tx,ty,d,Some((x as int,y as int,(completed+1) as u32))) by{
        let i=ty*width+tx;
        compact_index(width,height,words,tx as usize,ty as usize);
        compact_neighbor_bounds(width,height,words,tx,ty,d);
        let selected=(7-completed) as u32;
        let neighbor=compact_neighbor_index(width,height,tx,ty,d);
        assert(compact_cache_at(width,height,words,tx,ty,d,Some((x as int,y as int,completed))));
        compact_neighbor_reverse(width,height,x as int,y as int,tx,ty,d);
        assert((d+completed<8 && !(d+completed+1<8))==(d==selected));
        if d==selected{
            assert((target==Some(i))==(neighbor==Some(y*width+x)));
        }
        match target{
            None=>{},
            Some(j)=>{
                compact_add_neighbor_flags(words[j],selected,negative,d);
                if i==j{
                    assert(compact_flag(after[i],d,false)==(d==selected || compact_flag(words[i],d,false)));
                    assert(compact_flag(after[i],d,true)==((d==selected && negative) || compact_flag(words[i],d,true)));
                }else{assert(after[i]==words[i]);}
                match neighbor{
                    None=>{},
                    Some(n)=>{
                        if n==j{}else{assert(after[n]==words[n]);}
                        assert(compact_coefficient(after[n])==compact_coefficient(words[n]));
                    },
                }
            },
        }
    }
}
pub(crate) proof fn compact_empty_cache(width:usize,height:usize,words:Seq<u64>)
    requires compact_shape(width,height,words),
        forall|i:int|0<=i<words.len() ==> #[trigger] words[i]==0x3f_0000_0000u64,
    ensures compact_cache(width,height,words),
{
    compact_empty_word();
    assert forall|x:int,y:int,d:u32|0<=x<width && 0<=y<height && d<8 implies
        #[trigger] compact_cache_at(width,height,words,x,y,d,None) by{
        compact_index(width,height,words,x as usize,y as usize);
        compact_neighbor_bounds(width,height,words,x,y,d);
        assert(words[y*width+x]==0x3f_0000_0000u64);
        let word=words[y*width+x];
        assert(!compact_flag(word,d,false) && !compact_flag(word,d,true)) by(bit_vector)
            requires d<8,word==0x3f_0000_0000u64;
        match compact_neighbor_index(width,height,x,y,d){None=>{},Some(j)=>{assert(words[j]==0x3f_0000_0000u64);}}
    }
}
pub(crate) proof fn compact_high_flags_frame(left:u64,right:u64,d:u32)
    requires left>>41==right>>41,d<8,
    ensures compact_flag(left,d,false)==compact_flag(right,d,false),
        compact_flag(left,d,true)==compact_flag(right,d,true),
{
    assert(compact_flag(left,d,false)==compact_flag(right,d,false)
        && compact_flag(left,d,true)==compact_flag(right,d,true)) by(bit_vector)
        requires left>>41==right>>41,d<8;
}
pub(crate) proof fn compact_cache_value_frame(width:usize,height:usize,words:Seq<u64>,index:int,word:u64)
    requires compact_cache(width,height,words),0<=index<words.len(),
        word>>41==words[index]>>41,
        compact_coefficient(word).significant==compact_coefficient(words[index]).significant,
        compact_coefficient(word).negative==compact_coefficient(words[index]).negative,
    ensures compact_cache(width,height,words.update(index,word)),
{
    let after=words.update(index,word);
    assert forall|x:int,y:int,d:u32|0<=x<width && 0<=y<height && d<8 implies
        #[trigger] compact_cache_at(width,height,after,x,y,d,None) by{
        compact_index(width,height,words,x as usize,y as usize);
        compact_neighbor_bounds(width,height,words,x,y,d);
        assert(compact_cache_at(width,height,words,x,y,d,None));
        compact_high_flags_frame(word,words[index],d);
        if y*width+x==index{}else{assert(after[y*width+x]==words[y*width+x]);}
        match compact_neighbor_index(width,height,x,y,d){
            None=>{},
            Some(j)=>if j==index{}else{assert(after[j]==words[j]);},
        }
    }
}
pub(crate) proof fn compact_cache_mark_end(width:usize,height:usize,words:Seq<u64>,x:usize,y:usize)
    requires compact_pending_cache(width,height,words,x as int,y as int,8),
    ensures compact_cache(width,height,words),
{
    assert forall|tx:int,ty:int,d:u32|0<=tx<width && 0<=ty<height && d<8 implies
        #[trigger] compact_cache_at(width,height,words,tx,ty,d,None) by{
        assert(compact_cache_at(width,height,words,tx,ty,d,Some((x as int,y as int,8u32))));
    }
}
}
