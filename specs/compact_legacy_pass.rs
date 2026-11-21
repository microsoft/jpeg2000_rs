//! Reached bitplane membership and geometric pass-counter bounds.
use super::*;
verus! {
pub(crate) open spec fn compact_statistics_le(s:crate::tier1::Tier1PassStatistics,bound:nat)->bool {
    s.coefficients_scanned<=bound && s.coding_symbols<=bound && s.newly_significant<=bound
        && s.refined_coefficients<=bound && s.run_mode_columns<=bound
}
pub(crate) open spec fn compact_statistics_room(s:crate::tier1::Tier1PassStatistics)->bool {
    compact_statistics_le(s,(u32::MAX-4) as nat)
}
pub(crate) open spec fn compact_stripe_bound(width:usize,stripe:usize)->nat {
    16*(stripe as nat*width as nat)
}
pub(crate) open spec fn compact_scan_bound(width:usize,stripe:usize,rows:usize,x:usize)->nat {
    16*(stripe as nat*width as nat+x as nat*rows as nat)
}
pub(crate) proof fn compact_counter_algebra(width:usize,stripe:usize,rows:usize,x:usize)
    requires rows>0,x<usize::MAX,stripe+rows<=usize::MAX,
    ensures compact_scan_bound(width,stripe,rows,0)==compact_stripe_bound(width,stripe),
        compact_scan_bound(width,stripe,rows,width)==compact_stripe_bound(width,(stripe+rows) as usize),
        compact_scan_bound(width,stripe,rows,x)+4+2*rows<=compact_scan_bound(width,stripe,rows,(x+1) as usize),
{
    assert(compact_scan_bound(width,stripe,rows,width)==compact_stripe_bound(width,(stripe+rows) as usize)) by(nonlinear_arith)
        requires stripe+rows<=usize::MAX;
    assert(compact_scan_bound(width,stripe,rows,x)+4+2*rows<=compact_scan_bound(width,stripe,rows,(x+1) as usize)) by(nonlinear_arith)
        requires rows>0,x<usize::MAX;
}
pub(crate) open spec fn compact_statistics_delta(before:crate::tier1::Tier1PassStatistics,after:crate::tier1::Tier1PassStatistics,maximum:nat)->bool {
    before.coefficients_scanned<=after.coefficients_scanned<=before.coefficients_scanned+maximum
        && before.coding_symbols<=after.coding_symbols<=before.coding_symbols+maximum
        && before.newly_significant<=after.newly_significant<=before.newly_significant+maximum
        && before.refined_coefficients<=after.refined_coefficients<=before.refined_coefficients+maximum
        && before.run_mode_columns<=after.run_mode_columns<=before.run_mode_columns+maximum
}
pub(crate) open spec fn compact_bitplane_flags_frame(before:Part1LegacyBitplane,after:Part1LegacyBitplane)->bool {
    after==(Part1LegacyBitplane {significance_visited:after.significance_visited,..before})
        && after.significance_visited.len()==before.significance_visited.len()
}
pub(crate) open spec fn compact_membership(width:usize,height:usize,words:Seq<u64>,state:Part1LegacyBitplane)->bool {
    compact_cache(width,height,words) && state.width==width && state.height==height && state.bitplane<31
        && state.significant_before.len()==words.len() && state.significance_visited.len()==words.len()
        && (forall|i:int|0<=i<words.len() ==> #[trigger] compact_precision_word(words[i]))
        && forall|i:int|0<=i<words.len() ==> {
            let significant=compact_coefficient(words[i]).significant;
            let tag=(words[i]>>32)&63;
            if #[trigger] state.significant_before[i]{significant && tag>=state.bitplane}
            else{significant ==> tag==state.bitplane}
        }
}
pub(crate) proof fn compact_lower_fields(left:u64,right:u64)
    requires left & 0x1ff_ffff_ffffu64==right & 0x1ff_ffff_ffffu64,
    ensures compact_coefficient(left).significant==compact_coefficient(right).significant,
        compact_coefficient(left).negative==compact_coefficient(right).negative,
        ((left>>32)&63)==((right>>32)&63),
        left & 0xffff_ffffu64==right & 0xffff_ffffu64,
{
    assert((left & (1u64<<38)!=0)==(right & (1u64<<38)!=0)
        && (left & (1u64<<39)!=0)==(right & (1u64<<39)!=0)
        && ((left>>32)&63)==((right>>32)&63)
        && left & 0xffff_ffffu64==right & 0xffff_ffffu64) by(bit_vector)
        requires left & 0x1ff_ffff_ffffu64==right & 0x1ff_ffff_ffffu64;
}
pub(crate) proof fn compact_membership_cell(width:usize,height:usize,before:Seq<u64>,after:Seq<u64>,
    state:Part1LegacyBitplane,next:Part1LegacyBitplane,index:int)
    requires compact_membership(width,height,before,state),0<=index<before.len(),
        compact_cache(width,height,after),after.len()==before.len(),
        forall|i:int|0<=i<after.len() ==> #[trigger] compact_precision_word(after[i]),
        next.width==state.width,next.height==state.height,next.bitplane==state.bitplane,
        next.significant_before==state.significant_before,next.significance_visited.len()==state.significance_visited.len(),
        forall|i:int|0<=i<before.len() && i!=index ==> #[trigger] (after[i] & 0x1ff_ffff_ffffu64)==before[i] & 0x1ff_ffff_ffffu64,
        if state.significant_before[index]{
            compact_coefficient(after[index]).significant && ((after[index]>>32)&63)>=state.bitplane
        }else{compact_coefficient(after[index]).significant ==> ((after[index]>>32)&63)==state.bitplane},
    ensures compact_membership(width,height,after,next),
{
    assert forall|i:int|0<=i<after.len() implies {
        let significant=compact_coefficient(after[i]).significant;
        let tag=(after[i]>>32)&63;
        if #[trigger] next.significant_before[i]{significant && tag>=next.bitplane}
        else{significant ==> tag==next.bitplane}
    } by{
        if i!=index{
            compact_lower_fields(before[i],after[i]);
            assert(if state.significant_before[i]{compact_coefficient(before[i]).significant && ((before[i]>>32)&63)>=state.bitplane}
                else{compact_coefficient(before[i]).significant ==> ((before[i]>>32)&63)==state.bitplane});
        }
    }
}
pub(crate) open spec fn compact_processed(stripe:usize,rows:usize,x:usize,row:usize,tx:int,ty:int)->bool {
    ty<stripe || (stripe<=ty<stripe+rows && (tx<x || (tx==x && ty<stripe+row)))
}
pub(crate) open spec fn compact_refinement_pending(width:usize,height:usize,words:Seq<u64>,state:Part1LegacyBitplane,
    stripe:usize,rows:usize,x:usize,row:usize)->bool {
    compact_membership(width,height,words,state)
        && forall|tx:int,ty:int|0<=tx<width && 0<=ty<height && #[trigger] state.significant_before[ty*width+tx] ==> {
            let tag=(words[ty*width+tx]>>32)&63;
            if compact_processed(stripe,rows,x,row,tx,ty){tag==state.bitplane}else{tag>state.bitplane}
        }
}
pub(crate) open spec fn compact_before_frontier(words:Seq<u64>,state:Part1LegacyBitplane,refined:bool)->bool {
    forall|i:int|0<=i<words.len() && #[trigger] state.significant_before[i] ==>
        if refined{((words[i]>>32)&63)==state.bitplane}else{((words[i]>>32)&63)>state.bitplane}
}
pub(crate) proof fn compact_coordinates(width:usize,height:usize,words:Seq<u64>,index:int)
    requires compact_shape(width,height,words),0<=index<words.len(),
    ensures 0<=index%(width as int)<width,0<=index/(width as int)<height,
        (index/(width as int))*width+index%(width as int)==index,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(index,width as int);
    vstd::arithmetic::div_mod::lemma_mod_bound(index,width as int);
    let x=index%(width as int);
    let y=index/(width as int);
    assert(y>=0) by(nonlinear_arith)
        requires index>=0,index==y*width+x,0<=x<width,width>0;
    assert(y<height) by(nonlinear_arith)
        requires index<width*height,index==y*width+x,x>=0,width>0;
}
pub(crate) proof fn compact_frontier_row_step(width:usize,height:usize,before:Seq<u64>,after:Seq<u64>,state:Part1LegacyBitplane,
    stripe:usize,rows:usize,x:usize,row:usize)
    requires compact_refinement_pending(width,height,before,state,stripe,rows,x,row),
        stripe+rows<=height,rows>0,x<width,row<rows,compact_membership(width,height,after,state),
        forall|i:int|0<=i<before.len() && i!=((stripe+row)*width+x) as int
            ==> #[trigger] (after[i] & 0x1ff_ffff_ffffu64)==before[i] & 0x1ff_ffff_ffffu64,
        state.significant_before[((stripe+row)*width+x) as int] ==>
            ((after[((stripe+row)*width+x) as int]>>32)&63)==state.bitplane,
    ensures compact_refinement_pending(width,height,after,state,stripe,rows,x,(row+1) as usize),
{
    let source=((stripe+row)*width+x) as int;
    assert forall|tx:int,ty:int|0<=tx<width && 0<=ty<height && #[trigger] state.significant_before[ty*width+tx] implies {
        let tag=(after[ty*width+tx]>>32)&63;
        if compact_processed(stripe,rows,x,(row+1) as usize,tx,ty){tag==state.bitplane}else{tag>state.bitplane}
    } by{
        let i=ty*width+tx;
        compact_index(width,height,before,tx as usize,ty as usize);
        if i==source{
            compact_coordinate_injective(width,tx,ty,x as int,(stripe+row) as int);
        }else{
            compact_lower_fields(before[i],after[i]);
            assert(compact_processed(stripe,rows,x,(row+1) as usize,tx,ty)==compact_processed(stripe,rows,x,row,tx,ty));
            assert(if compact_processed(stripe,rows,x,row,tx,ty){((before[i]>>32)&63)==state.bitplane}
                else{((before[i]>>32)&63)>state.bitplane});
        }
    }
}
pub(crate) proof fn compact_frontier_column_end(width:usize,height:usize,words:Seq<u64>,state:Part1LegacyBitplane,
    stripe:usize,rows:usize,x:usize)
    requires compact_refinement_pending(width,height,words,state,stripe,rows,x,rows),x<width,
    ensures compact_refinement_pending(width,height,words,state,stripe,rows,(x+1) as usize,0),
{
    assert forall|tx:int,ty:int|0<=tx<width && 0<=ty<height && #[trigger] state.significant_before[ty*width+tx] implies {
        let tag=(words[ty*width+tx]>>32)&63;
        if compact_processed(stripe,rows,(x+1) as usize,0,tx,ty){tag==state.bitplane}else{tag>state.bitplane}
    } by{
        assert(compact_processed(stripe,rows,(x+1) as usize,0,tx,ty)==compact_processed(stripe,rows,x,rows,tx,ty));
    }
}
pub(crate) proof fn compact_frontier_stripe_end(width:usize,height:usize,words:Seq<u64>,state:Part1LegacyBitplane,
    stripe:usize,rows:usize,next_rows:usize)
    requires compact_refinement_pending(width,height,words,state,stripe,rows,width,0),stripe+rows<=height,
    ensures compact_refinement_pending(width,height,words,state,(stripe+rows) as usize,next_rows,0,0),
{
    assert forall|tx:int,ty:int|0<=tx<width && 0<=ty<height && #[trigger] state.significant_before[ty*width+tx] implies {
        let tag=(words[ty*width+tx]>>32)&63;
        if compact_processed((stripe+rows) as usize,next_rows,0,0,tx,ty){tag==state.bitplane}else{tag>state.bitplane}
    } by{
        assert(compact_processed((stripe+rows) as usize,next_rows,0,0,tx,ty)==compact_processed(stripe,rows,width,0,tx,ty));
    }
}
pub(crate) proof fn compact_frontier_initial(width:usize,height:usize,words:Seq<u64>,state:Part1LegacyBitplane,rows:usize)
    requires compact_membership(width,height,words,state),compact_before_frontier(words,state,false),
    ensures compact_refinement_pending(width,height,words,state,0,rows,0,0),
{
    assert forall|tx:int,ty:int|0<=tx<width && 0<=ty<height && #[trigger] state.significant_before[ty*width+tx] implies {
        let tag=(words[ty*width+tx]>>32)&63;
        if compact_processed(0,rows,0,0,tx,ty){tag==state.bitplane}else{tag>state.bitplane}
    } by{
        compact_index(width,height,words,tx as usize,ty as usize);
        assert(!compact_processed(0,rows,0,0,tx,ty));
        assert(((words[ty*width+tx]>>32)&63)>state.bitplane);
    }
}
pub(crate) proof fn compact_frontier_finished(width:usize,height:usize,words:Seq<u64>,state:Part1LegacyBitplane)
    requires compact_refinement_pending(width,height,words,state,height,0,0,0),
    ensures compact_before_frontier(words,state,true),
{
    assert forall|i:int|0<=i<words.len() && #[trigger] state.significant_before[i] implies ((words[i]>>32)&63)==state.bitplane by{
        compact_coordinates(width,height,words,i);
        let tx=i%(width as int);
        let ty=i/(width as int);
        assert(compact_processed(height,0,0,0,tx,ty));
        assert(state.significant_before[ty*width+tx]);
    }
}
pub(crate) proof fn compact_before_frontier_preserved(before:Seq<u64>,after:Seq<u64>,state:Part1LegacyBitplane,next:Part1LegacyBitplane,refined:bool)
    requires compact_before_frontier(before,state,refined),after.len()==before.len(),
        next.significant_before==state.significant_before,next.bitplane==state.bitplane,
        forall|i:int|0<=i<before.len() && #[trigger] state.significant_before[i] ==>
            after[i] & 0x1ff_ffff_ffffu64==before[i] & 0x1ff_ffff_ffffu64,
    ensures compact_before_frontier(after,next,refined),
{
    assert forall|i:int|0<=i<after.len() && #[trigger] next.significant_before[i] implies
        if refined{((after[i]>>32)&63)==next.bitplane}else{((after[i]>>32)&63)>next.bitplane} by{
        compact_lower_fields(before[i],after[i]);
    }
}
pub(crate) open spec fn compact_pass_tag(kind:crate::tier1::Tier1PassKind)->u8 {
    if kind is SignificancePropagation{0u8}else if kind is MagnitudeRefinement{1u8}else{2u8}
}
pub(crate) open spec fn compact_pass_orientation(kind:crate::tier1::Tier1PassKind,orientation:crate::tier1::SubbandOrientation)->crate::tier1::SubbandOrientation {
    if kind is MagnitudeRefinement{crate::tier1::SubbandOrientation::Ll}else{orientation}
}
pub(crate) open spec fn compact_rows_model(before:Part1LegacyFrame,kind:crate::tier1::Tier1PassKind,orientation:crate::tier1::SubbandOrientation,
    causal:bool,x:usize,stripe:usize,row:usize,rows:usize,scan:bool)->Part1LegacyEffect {
    if !scan{part1_legacy_cleanup_rows(before,x as u16,stripe as u16,row as nat,rows as nat,orientation,causal)}
    else{part1_legacy_rows(before,x as u16,stripe as u16,row as nat,rows as nat,compact_pass_orientation(kind,orientation),causal,compact_pass_tag(kind))}
}
pub(crate) open spec fn compact_column_model(before:Part1LegacyFrame,kind:crate::tier1::Tier1PassKind,orientation:crate::tier1::SubbandOrientation,
    causal:bool,x:usize,stripe:usize,rows:usize)->Part1LegacyEffect {
    if kind is Cleanup{part1_legacy_cleanup_column(before,x as u16,stripe as u16,rows as u16,orientation,causal)}
    else{compact_rows_model(before,kind,orientation,causal,x,stripe,0,rows,true)}
}
pub(crate) open spec fn compact_pass_model(plane:Tier1RawPlane,state:Part1LegacyBitplane,symbols:Part1LegacySymbols,
    kind:crate::tier1::Tier1PassKind,orientation:crate::tier1::SubbandOrientation,causal:bool)->Part1LegacyPassEffect {
    if kind is Cleanup{part1_legacy_cleanup_pass(plane,state,symbols,orientation,causal,false)}
    else{part1_legacy_pass(plane,state,symbols,compact_pass_orientation(kind,orientation),causal,compact_pass_tag(kind))}
}
pub(crate) proof fn compact_column_geometry(width:usize,height:usize,words:Seq<u64>,x:usize,stripe:usize,rows:usize)
    requires compact_shape(width,height,words),x<width,rows>0,rows<=4,stripe+rows<=height,
    ensures stripe*width+x*rows+rows<=words.len(),stripe*width+x*rows<=4096,
        compact_scan_bound(width,stripe,rows,x)+4+2*rows<(u32::MAX-4) as nat,
{
    assert(stripe*width+x*rows+rows<=width*height) by(nonlinear_arith)
        requires width>0,x<width,rows>0,stripe+rows<=height;
}
pub(crate) open spec fn compact_pass_finish(effect:Part1LegacyEffect,kind:crate::tier1::Tier1PassKind)->Part1LegacyPassEffect {
    if kind is Cleanup{part1_legacy_cleanup_finish(effect,false)}else{part1_legacy_finish(effect,compact_pass_tag(kind))}
}
pub(crate) open spec fn compact_pass_suffix(frame:Part1LegacyFrame,stripe:usize,kind:crate::tier1::Tier1PassKind,
    orientation:crate::tier1::SubbandOrientation,causal:bool)->Part1LegacyPassEffect {
    compact_pass_finish(part1_legacy_stripes(frame,stripe as nat,frame.plane.width,frame.plane.height,
        compact_pass_orientation(kind,orientation),causal,compact_pass_tag(kind)),kind)
}
pub(crate) open spec fn compact_column_suffix(frame:Part1LegacyFrame,x:usize,stripe:usize,rows:usize,kind:crate::tier1::Tier1PassKind,
    orientation:crate::tier1::SubbandOrientation,causal:bool)->Part1LegacyPassEffect {
    if kind is Cleanup{part1_legacy_cleanup_column_tail(frame,x as nat,stripe as u16,rows as nat,
        frame.plane.width,frame.plane.height,orientation,causal,false)}
    else{part1_legacy_column_tail(frame,x as nat,stripe as u16,rows as nat,frame.plane.width,frame.plane.height,
        compact_pass_orientation(kind,orientation),causal,compact_pass_tag(kind))}
}
pub(crate) open spec fn compact_pass_flags(before:Part1LegacyBitplane,after:Part1LegacyBitplane,kind:crate::tier1::Tier1PassKind,success:bool)->bool {
    after==(Part1LegacyBitplane {
        significance_visited:after.significance_visited,
        significance_propagation_complete:before.significance_propagation_complete || (success && kind is SignificancePropagation),
        magnitude_refinement_complete:before.magnitude_refinement_complete || (success && kind is MagnitudeRefinement),
        cleanup_complete:before.cleanup_complete || (success && kind is Cleanup),
        ..before
    }) && after.significance_visited.len()==before.significance_visited.len()
}
pub(crate) open spec fn compact_pass_order(state:Part1LegacyBitplane,kind:crate::tier1::Tier1PassKind)->bool {
    if kind is SignificancePropagation{
        !state.significance_propagation_complete && !state.magnitude_refinement_complete && !state.cleanup_complete
    }else if kind is MagnitudeRefinement{
        state.significance_propagation_complete && !state.magnitude_refinement_complete && !state.cleanup_complete
    }else{
        !state.cleanup_complete && state.significance_propagation_complete==state.magnitude_refinement_complete
    }
}
}
