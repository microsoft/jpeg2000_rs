//! Actual rollback TagTree owner copies, separate from fresh tree construction.
use super::*;
verus! {
pub struct Part2TagCopyContext {
    pub path:crate::packet::TagTreeCopyPath,pub source:Part1TagTree,pub levels:Option<Seq<Part1TagLevel>>,
}
#[verifier::opaque]
pub(crate) open spec fn part2_tag_copy_capacity_run(context:Part2TagCopyContext,nodes:bool,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=if nodes{context.source.nodes.len()}else{context.source.levels.len()};
    if count==0{Some((Ok(()),events))}else if events.len()==0{None}else{match events[0] {
        Part2JpipSnapshotEvent::TagCopyCapacity {context:actual,nodes:field,elements,succeeded}=>
            if actual!=context || field!=nodes || elements!=count{None}else{
                Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))
            },
        _=>None,
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_tag_copy_capacity_result(context:Part2TagCopyContext,nodes:bool,result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_tag_copy_capacity_run(context,nodes,events),result)
}
pub(crate) proof fn part2_tag_copy_capacity_observed(context:Part2TagCopyContext,nodes:bool,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || ((if nodes{context.source.nodes.len()}else{context.source.levels.len()})>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_tag_copy_capacity_result(context,nodes,result),
{
    reveal(part2_tag_copy_capacity_result);reveal(part2_tag_copy_capacity_run);
    let count=if nodes{context.source.nodes.len()}else{context.source.levels.len()};
    let prefix=if count==0{Seq::empty()}else{seq![Part2JpipSnapshotEvent::TagCopyCapacity {context,nodes,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_tag_copy_capacity_run(context,nodes,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_tag_copy_capacity_run(context,nodes,events),prefix,result));
}
#[verifier::opaque]
pub(crate) open spec fn part2_tag_copy_run(source:Part1TagTree,path:crate::packet::TagTreeCopyPath,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1TagTree> {
    part2_jpip_snapshot_bind(part2_tag_copy_capacity_run(Part2TagCopyContext {path,source,levels:None},false,events),
        |_:(),rest|part2_jpip_snapshot_bind(part2_tag_copy_capacity_run(Part2TagCopyContext {path,source,levels:Some(source.levels)},true,rest),
            |_:(),tail|Some((Ok(source),tail))))
}
#[verifier::opaque]
pub(crate) open spec fn part2_tag_copy_result(source:Part1TagTree,path:crate::packet::TagTreeCopyPath,result:Result<Part1TagTree,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_tag_copy_run(source,path,events),result)
}
pub(crate) proof fn part2_tag_copy_levels_error(source:Part1TagTree,path:crate::packet::TagTreeCopyPath,error:crate::DecodeError)
    requires part2_tag_copy_capacity_result(Part2TagCopyContext {path,source,levels:None},false,Err(error)),
    ensures part2_tag_copy_result(source,path,Err(error)),
{
    reveal(part2_tag_copy_result);reveal(part2_tag_copy_run);reveal(part2_tag_copy_capacity_result);
    part2_cold_bind(|events|part2_tag_copy_capacity_run(Part2TagCopyContext {path,source,levels:None},false,events),
        |_:(),rest|part2_jpip_snapshot_bind(part2_tag_copy_capacity_run(Part2TagCopyContext {path,source,levels:Some(source.levels)},true,rest),
            |_:(),tail|Some((Ok(source),tail))),Err(error),Err(error));
}
pub(crate) proof fn part2_tag_copy_after_levels(source:Part1TagTree,path:crate::packet::TagTreeCopyPath,result:Result<(),crate::DecodeError>)
    requires part2_tag_copy_capacity_result(Part2TagCopyContext {path,source,levels:None},false,Ok(())),
        part2_tag_copy_capacity_result(Part2TagCopyContext {path,source,levels:Some(source.levels)},true,result),
    ensures part2_tag_copy_result(source,path,match result{Err(error)=>Err(error),Ok(())=>Ok(source)}),
{
    reveal(part2_tag_copy_result);reveal(part2_tag_copy_run);reveal(part2_tag_copy_capacity_result);
    let output=match result{Err(error)=>Err(error),Ok(())=>Ok(source)};
    if result.is_ok(){part2_cold_pure(Ok(source));}
    part2_cold_bind(|events|part2_tag_copy_capacity_run(Part2TagCopyContext {path,source,levels:Some(source.levels)},true,events),
        |_:(),tail|Some((Ok(source),tail)),result,output);
    part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_tag_copy_capacity_run(Part2TagCopyContext {path,source,levels:Some(source.levels)},true,events),
        |_:(),tail|Some((Ok(source),tail))),output);
    part2_cold_bind(|events|part2_tag_copy_capacity_run(Part2TagCopyContext {path,source,levels:None},false,events),
        |_:(),rest|part2_jpip_snapshot_bind(part2_tag_copy_capacity_run(Part2TagCopyContext {path,source,levels:Some(source.levels)},true,rest),
            |_:(),tail|Some((Ok(source),tail))),Ok(()),output);
}
pub(crate) proof fn part2_tag_copy_normal(source:Part1TagTree,path:crate::packet::TagTreeCopyPath)
    ensures part2_tag_copy_result(source,path,Ok(source)),
{
    part2_tag_copy_capacity_observed(Part2TagCopyContext {path,source,levels:None},false,Ok(()));
    part2_tag_copy_capacity_observed(Part2TagCopyContext {path,source,levels:Some(source.levels)},true,Ok(()));
    part2_tag_copy_after_levels(source,path,Ok(()));
}
pub(crate) proof fn part2_tag_copy_frames(source:Part1TagTree,path:crate::packet::TagTreeCopyPath,result:Result<Part1TagTree,crate::DecodeError>)
    requires part2_tag_copy_result(source,path,result),
    ensures part2_cold_framed(|events|part2_tag_copy_run(source,path,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1TagTree>|
            (forall|events| #[trigger] other(events)==part2_tag_copy_run(source,path,events)) ==> #[trigger] part2_cold_framed(other,result),
{reveal(part2_tag_copy_result);part2_decode_eta(|events|part2_tag_copy_run(source,path,events),result);}
}
