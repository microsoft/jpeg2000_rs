//! Ordered real rollback subband/tree copies and actual packet invocation.
use super::*;
verus! {
#[verifier::opaque]
pub(crate) open spec fn part2_subband_copy_run(source:Part1PacketSubbandState,index:usize,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketSubbandState> {
    part2_jpip_snapshot_bind(part2_tag_copy_run(source.inclusion_tree,crate::packet::TagTreeCopyPath {subband:index,zero:false},events),
        |inclusion:Part1TagTree,rest|part2_jpip_snapshot_bind(part2_tag_copy_run(source.zero_bitplane_tree,crate::packet::TagTreeCopyPath {subband:index,zero:true},rest),
            |zero:Part1TagTree,tail|Some((Ok(Part1PacketSubbandState {inclusion_tree:inclusion,zero_bitplane_tree:zero,..source}),tail))))
}
#[verifier::opaque]
pub(crate) open spec fn part2_subband_copy_result(source:Part1PacketSubbandState,index:usize,result:Result<Part1PacketSubbandState,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_subband_copy_run(source,index,events),result)
}
pub(crate) proof fn part2_subband_copy_observed(source:Part1PacketSubbandState,index:usize,first:Result<Part1TagTree,crate::DecodeError>,
    second:Option<Result<Part1TagTree,crate::DecodeError>>,result:Result<Part1PacketSubbandState,crate::DecodeError>)
    requires part2_tag_copy_result(source.inclusion_tree,crate::packet::TagTreeCopyPath {subband:index,zero:false},first),
        match first {Err(error)=>result==Err(error),Ok(inclusion)=>second.is_some() && part2_tag_copy_result(source.zero_bitplane_tree,crate::packet::TagTreeCopyPath {subband:index,zero:true},second.unwrap())
            && result==match second.unwrap(){Err(error)=>Err(error),Ok(zero)=>Ok(Part1PacketSubbandState {inclusion_tree:inclusion,zero_bitplane_tree:zero,..source})}},
    ensures part2_subband_copy_result(source,index,result),
{
    reveal(part2_subband_copy_result);reveal(part2_subband_copy_run);
    let path=crate::packet::TagTreeCopyPath {subband:index,zero:false};
    part2_tag_copy_frames(source.inclusion_tree,path,first);
    if let Ok(inclusion)=first{
        let next=second.unwrap();
        part2_tag_copy_frames(source.zero_bitplane_tree,crate::packet::TagTreeCopyPath {subband:index,zero:true},next);
        if next.is_ok(){part2_cold_pure(result);}
        part2_cold_bind(|events|part2_tag_copy_run(source.zero_bitplane_tree,crate::packet::TagTreeCopyPath {subband:index,zero:true},events),
            |zero:Part1TagTree,tail|Some((Ok(Part1PacketSubbandState {inclusion_tree:inclusion,zero_bitplane_tree:zero,..source}),tail)),next,result);
        part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_tag_copy_run(source.zero_bitplane_tree,crate::packet::TagTreeCopyPath {subband:index,zero:true},events),
            |zero:Part1TagTree,tail|Some((Ok(Part1PacketSubbandState {inclusion_tree:inclusion,zero_bitplane_tree:zero,..source}),tail))),result);
    }
    part2_cold_bind(|events|part2_tag_copy_run(source.inclusion_tree,path,events),
        |inclusion:Part1TagTree,rest|part2_jpip_snapshot_bind(part2_tag_copy_run(source.zero_bitplane_tree,crate::packet::TagTreeCopyPath {subband:index,zero:true},rest),
            |zero:Part1TagTree,tail|Some((Ok(Part1PacketSubbandState {inclusion_tree:inclusion,zero_bitplane_tree:zero,..source}),tail))),first,result);
}
#[verifier::opaque]
pub(crate) open spec fn part2_subbands_copy_run(source:Seq<Part1PacketSubbandState>,index:nat,before:Seq<Part1PacketSubbandState>,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part1PacketSubbandState>>
    decreases if index<source.len(){source.len()-index}else{0},
{
    if index>=source.len(){Some((Ok(before),events))}else{
        part2_jpip_snapshot_bind(part2_subband_copy_run(source[index as int],index as usize,events),
            |copied:Part1PacketSubbandState,rest|part2_subbands_copy_run(source,index+1,before.push(copied),rest))
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_subbands_copy_result(source:Seq<Part1PacketSubbandState>,result:Result<Seq<Part1PacketSubbandState>,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_subbands_copy_run(source,0,Seq::empty(),events),result)
}
pub(crate) proof fn part2_subband_copy_frames(source:Part1PacketSubbandState,index:usize,result:Result<Part1PacketSubbandState,crate::DecodeError>)
    requires part2_subband_copy_result(source,index,result),
    ensures part2_cold_framed(|events|part2_subband_copy_run(source,index,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketSubbandState>|
            (forall|events| #[trigger] other(events)==part2_subband_copy_run(source,index,events)) ==> #[trigger] part2_cold_framed(other,result),
{reveal(part2_subband_copy_result);part2_decode_eta(|events|part2_subband_copy_run(source,index,events),result);}
pub(crate) proof fn part2_subbands_copy_step(source:Seq<Part1PacketSubbandState>,index:nat,before:Seq<Part1PacketSubbandState>)
    requires index<source.len(),
    ensures forall|events:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_subbands_copy_run(source,index,before,events)
        ==part2_jpip_snapshot_bind(part2_subband_copy_run(source[index as int],index as usize,events),
            |copied:Part1PacketSubbandState,rest|part2_subbands_copy_run(source,index+1,before.push(copied),rest)),
{reveal_with_fuel(part2_subbands_copy_run,1);}
pub(crate) proof fn part2_subbands_copy_end(source:Seq<Part1PacketSubbandState>,root:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part1PacketSubbandState>>,
    prefix:Seq<Part2JpipSnapshotEvent>,before:Seq<Part1PacketSubbandState>)
    requires part2_cold_phase(root,prefix,|events|part2_subbands_copy_run(source,source.len(),before,events)),
        forall|events| #[trigger] root(events)==part2_subbands_copy_run(source,0,Seq::empty(),events),
    ensures part2_subbands_copy_result(source,Ok(before)),
{
    reveal(part2_subbands_copy_result);reveal_with_fuel(part2_subbands_copy_run,1);
    part2_cold_pure(Ok(before));
    part2_cold_prefix_result(root,|events|Some((Ok(before),events)),prefix,Ok(before));
    part2_cold_framed_extensional(root,|events|part2_subbands_copy_run(source,0,Seq::empty(),events),Ok(before));
}
pub(crate) proof fn part2_subbands_copy_join(source:Seq<Part1PacketSubbandState>,root:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part1PacketSubbandState>>,
    result:Result<Seq<Part1PacketSubbandState>,crate::DecodeError>)
    requires part2_cold_framed(root,result),forall|events| #[trigger] root(events)==part2_subbands_copy_run(source,0,Seq::empty(),events),
    ensures part2_subbands_copy_result(source,result),
{reveal(part2_subbands_copy_result);part2_cold_framed_extensional(root,|events|part2_subbands_copy_run(source,0,Seq::empty(),events),result);}
pub(crate) proof fn part2_subband_copy_normal(source:Part1PacketSubbandState,index:usize)
    ensures part2_subband_copy_result(source,index,Ok(source)),
{
    part2_tag_copy_normal(source.inclusion_tree,crate::packet::TagTreeCopyPath {subband:index,zero:false});
    part2_tag_copy_normal(source.zero_bitplane_tree,crate::packet::TagTreeCopyPath {subband:index,zero:true});
    part2_subband_copy_observed(source,index,Ok(source.inclusion_tree),Some(Ok(source.zero_bitplane_tree)),Ok(source));
}
pub(crate) proof fn part2_subbands_copy_normal_at(source:Seq<Part1PacketSubbandState>,index:nat,before:Seq<Part1PacketSubbandState>)
    requires index<=source.len(),
    ensures part2_cold_framed(|events|part2_subbands_copy_run(source,index,before,events),
        Ok(before+source.subrange(index as int,source.len() as int))),
    decreases source.len()-index,
{
    reveal_with_fuel(part2_subbands_copy_run,1);
    if index==source.len(){
        assert(before+source.subrange(index as int,source.len() as int) =~= before);
        part2_cold_pure(Ok(before));
    }else{
        let row=source[index as int];let after=before.push(row);
        part2_subband_copy_normal(row,index as usize);part2_subband_copy_frames(row,index as usize,Ok(row));
        part2_subbands_copy_normal_at(source,index+1,after);
        assert(after+source.subrange(index as int+1,source.len() as int) =~= before+source.subrange(index as int,source.len() as int));
        part2_decode_eta(|events|part2_subbands_copy_run(source,index+1,after,events),Ok(before+source.subrange(index as int,source.len() as int)));
        part2_cold_bind(|events|part2_subband_copy_run(row,index as usize,events),
            |copied:Part1PacketSubbandState,rest|part2_subbands_copy_run(source,index+1,before.push(copied),rest),
            Ok(row),Ok(before+source.subrange(index as int,source.len() as int)));
    }
}
pub(crate) proof fn part2_subbands_copy_normal(source:Seq<Part1PacketSubbandState>)
    ensures part2_subbands_copy_result(source,Ok(source)),
{
    reveal(part2_subbands_copy_result);
    part2_subbands_copy_normal_at(source,0,Seq::empty());
    assert(Seq::empty()+source.subrange(0,source.len() as int) =~= source);
}
#[verifier::opaque]
pub(crate) open spec fn part2_jpip_packet_copy_run(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Result<usize,crate::DecodeError>,Part1PacketPrecinctState)> {
    match part2_subbands_copy_run(initial.subbands,0,Seq::empty(),events){
        None=>None,Some((Err(error),rest))=>Some((Ok((Err(error),initial)),rest)),
        Some((Ok(_),rest))=>Some((Ok(part2_jpip_snapshot_decode_packet(initial,part,data,sequence,layer,limits)),rest)),
    }
}
pub closed spec fn part2_jpip_packet_copy_result(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,result:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState))->bool {
    part2_cold_framed(|events|part2_jpip_packet_copy_run(initial,part,data,sequence,layer,limits,events),Ok(result))
}
pub(crate) proof fn part2_jpip_packet_copy_observed(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,first:Result<Seq<Part1PacketSubbandState>,crate::DecodeError>,result:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState))
    requires part2_subbands_copy_result(initial.subbands,first),
        match first{Err(error)=>result==(Err(error),initial),Ok(_)=>result==part2_jpip_snapshot_decode_packet(initial,part,data,sequence,layer,limits)},
    ensures part2_jpip_packet_copy_result(initial,part,data,sequence,layer,limits,result),
{
    reveal(part2_subbands_copy_result);reveal(part2_jpip_packet_copy_run);
    let child=|events|part2_subbands_copy_run(initial.subbands,0,Seq::empty(),events);
    let prefix=part2_cold_witness(child,first);
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_jpip_packet_copy_run(initial,part,data,sequence,layer,limits,prefix+tail)==Some((Ok(result),tail)) by{
        part2_cold_prefix_at(child,prefix,first,tail);
    }
    assert(part2_cold_prefix(|events|part2_jpip_packet_copy_run(initial,part,data,sequence,layer,limits,events),prefix,Ok(result)));
}
pub(crate) proof fn part2_jpip_packet_copy_frames(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,result:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState))
    requires part2_jpip_packet_copy_result(initial,part,data,sequence,layer,limits,result),
    ensures part2_cold_framed(|events|part2_jpip_packet_copy_run(initial,part,data,sequence,layer,limits,events),Ok(result)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Result<usize,crate::DecodeError>,Part1PacketPrecinctState)>|
            (forall|events| #[trigger] other(events)==part2_jpip_packet_copy_run(initial,part,data,sequence,layer,limits,events)) ==> #[trigger] part2_cold_framed(other,Ok(result)),
{part2_decode_eta(|events|part2_jpip_packet_copy_run(initial,part,data,sequence,layer,limits,events),Ok(result));}
pub(crate) proof fn part2_jpip_packet_copy_normal(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits)
    ensures part2_jpip_packet_copy_result(initial,part,data,sequence,layer,limits,
        part2_jpip_snapshot_decode_packet(initial,part,data,sequence,layer,limits)),
{
    part2_subbands_copy_normal(initial.subbands);
    part2_jpip_packet_copy_observed(initial,part,data,sequence,layer,limits,Ok(initial.subbands),
        part2_jpip_snapshot_decode_packet(initial,part,data,sequence,layer,limits));
}
#[verifier::opaque]
pub(crate) open spec fn part2_jpip_phase_copy_run(plan:Part2ProgressionTilePlan,execution:usize,part:Part2OwnedTilePart,prefix:Seq<u8>,start:usize,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Result<usize,crate::DecodeError>,Part2ProgressionTilePlan)> {
    if execution as nat>=plan.precincts.len(){Some((Ok((Err(part2_jpip_range_overflow(0)),plan)),events))}
    else{part2_jpip_snapshot_bind(part2_jpip_packet_copy_run(plan.precincts[execution as int],part,prefix.subrange(start as int,prefix.len() as int),sequence,layer,limits,events),
        |decoded:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState),rest|Some((Ok((decoded.0,Part2ProgressionTilePlan {precincts:plan.precincts.update(execution as int,decoded.1),..plan})),rest)))}
}
pub(crate) open spec fn part2_jpip_phase_copy_result(plan:Part2ProgressionTilePlan,execution:usize,part:Part2OwnedTilePart,prefix:Seq<u8>,start:usize,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,result:(Result<usize,crate::DecodeError>,Part2ProgressionTilePlan))->bool {
    part2_cold_framed(|events|part2_jpip_phase_copy_run(plan,execution,part,prefix,start,sequence,layer,limits,events),Ok(result))
}
pub(crate) proof fn part2_jpip_phase_copy_lookup_error(plan:Part2ProgressionTilePlan,execution:usize,part:Part2OwnedTilePart,prefix:Seq<u8>,start:usize,sequence:u16,layer:u16,limits:&crate::ResourceLimits)
    requires execution as nat>=plan.precincts.len(),
    ensures part2_jpip_phase_copy_result(plan,execution,part,prefix,start,sequence,layer,limits,(Err(part2_jpip_range_overflow(0)),plan)),
{reveal(part2_jpip_phase_copy_run);part2_cold_pure(Ok((Err::<usize,crate::DecodeError>(part2_jpip_range_overflow(0)),plan)));}
pub(crate) proof fn part2_jpip_phase_copy_observed(plan:Part2ProgressionTilePlan,execution:usize,part:Part2OwnedTilePart,prefix:Seq<u8>,start:usize,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,decoded:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState))
    requires (execution as nat)<plan.precincts.len(),
        part2_jpip_packet_copy_result(plan.precincts[execution as int],part,prefix.subrange(start as int,prefix.len() as int),sequence,layer,limits,decoded),
    ensures part2_jpip_phase_copy_result(plan,execution,part,prefix,start,sequence,layer,limits,
        (decoded.0,Part2ProgressionTilePlan {precincts:plan.precincts.update(execution as int,decoded.1),..plan})),
{
    reveal(part2_jpip_phase_copy_run);
    part2_jpip_packet_copy_frames(plan.precincts[execution as int],part,prefix.subrange(start as int,prefix.len() as int),sequence,layer,limits,decoded);
    let result=(decoded.0,Part2ProgressionTilePlan {precincts:plan.precincts.update(execution as int,decoded.1),..plan});
    part2_cold_pure(Ok(result));
    part2_cold_bind(|events|part2_jpip_packet_copy_run(plan.precincts[execution as int],part,prefix.subrange(start as int,prefix.len() as int),sequence,layer,limits,events),
        |decoded:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState),rest|Some((Ok((decoded.0,Part2ProgressionTilePlan {precincts:plan.precincts.update(execution as int,decoded.1),..plan})),rest)),Ok(decoded),Ok(result));
}
pub(crate) proof fn part2_jpip_phase_copy_normal(plan:Part2ProgressionTilePlan,execution:usize,template:&crate::codestream::TilePartPayload<'_>,
    prefix:Seq<u8>,start:usize,sequence:u16,layer:u16,limits:&crate::ResourceLimits)
    ensures part2_jpip_phase_copy_result(plan,execution,crate::codestream::tile_part_owned_view(template),prefix,start,sequence,layer,limits,
        part2_jpip_precinct_phase(plan,execution,template,prefix,start,sequence,layer,limits)),
{
    let part=crate::codestream::tile_part_owned_view(template);
    if execution as nat>=plan.precincts.len(){
        part2_jpip_phase_copy_lookup_error(plan,execution,part,prefix,start,sequence,layer,limits);
    }else{
        let data=prefix.subrange(start as int,prefix.len() as int);
        crate::jpip::jpip_snapshot_decode_packet_known(plan.precincts[execution as int],template,data,sequence,layer,limits);
        part2_jpip_packet_copy_normal(plan.precincts[execution as int],part,data,sequence,layer,limits);
        part2_jpip_phase_copy_observed(plan,execution,part,prefix,start,sequence,layer,limits,
            part2_jpip_snapshot_decode_packet(plan.precincts[execution as int],part,data,sequence,layer,limits));
    }
}
}
