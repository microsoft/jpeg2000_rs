//! Fresh TagTree level/node owners; caller envelopes carry real tree roles.
use super::*;
verus! {
pub struct Part2TagStorageEvent {
    pub width:u32,pub height:u32,pub maximum:u64,pub built:Part1TagBuild,pub levels:bool,pub succeeded:bool,
}
pub(crate) open spec fn part2_tag_storage_admit(width:u32,height:u32,maximum:u64)->Result<Part1TagBuild,crate::DecodeError> {
    if width==0 || height==0 {Err(part1_packet_reader_error(0,crate::MalformedKind::InvalidTagTree))}
    else{part1_tag_build(width,height,Part1TagBuild {levels:Seq::empty(),total:0},64,maximum)}
}
pub(crate) open spec fn part2_tag_storage_run(width:u32,height:u32,maximum:u64,calls:Seq<Part2TagStorageEvent>)
    ->Option<(Result<Part1TagTree,crate::DecodeError>,Seq<Part2TagStorageEvent>)> {
    match part2_tag_storage_admit(width,height,maximum) {
        Err(error)=>Some((Err(error),calls)),
        Ok(built)=>if built.total==0 {Some((part1_tag_initial(width,height,maximum),calls))}
        else if calls.len()==0 {None}else{
            let call=calls[0];
            if call.width!=width || call.height!=height || call.maximum!=maximum || call.built!=built || !call.levels {None}
            else if !call.succeeded {Some((Err(crate::DecodeError::AllocationFailed),calls.drop_first()))}
            else if calls.len()<2 {None}else{
                let nodes=calls[1];
                if nodes.width!=width || nodes.height!=height || nodes.maximum!=maximum || nodes.built!=built || nodes.levels {None}
                else{Some((if nodes.succeeded {part1_tag_initial(width,height,maximum)}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first().drop_first()))}
            }
        },
    }
}
pub(crate) open spec fn part2_tag_storage_prefix(width:u32,height:u32,maximum:u64,prefix:Seq<Part2TagStorageEvent>,result:Result<Part1TagTree,crate::DecodeError>)->bool {
    forall|tail:Seq<Part2TagStorageEvent>| #[trigger] part2_tag_storage_run(width,height,maximum,prefix+tail)==Some((result,tail))
}
pub closed spec fn part1_tag_storage_result(width:u32,height:u32,maximum:u64,result:Result<Part1TagTree,crate::DecodeError>)->bool {
    exists|prefix:Seq<Part2TagStorageEvent>| #[trigger] part2_tag_storage_prefix(width,height,maximum,prefix,result)
}
pub(crate) proof fn part2_tag_storage_normal(width:u32,height:u32,maximum:u64)
    ensures part1_tag_storage_result(width,height,maximum,part1_tag_initial(width,height,maximum)),
{
    let result=part1_tag_initial(width,height,maximum);
    let prefix=match part2_tag_storage_admit(width,height,maximum) {
        Err(_)=>Seq::empty(),Ok(built)=>if built.total==0 {Seq::empty()}else{seq![
            Part2TagStorageEvent {width,height,maximum,built,levels:true,succeeded:true},
            Part2TagStorageEvent {width,height,maximum,built,levels:false,succeeded:true}]},
    };
    assert forall|tail:Seq<Part2TagStorageEvent>|part2_tag_storage_run(width,height,maximum,prefix+tail)==Some((result,tail)) by{
        match part2_tag_storage_admit(width,height,maximum) {
            Ok(built)=>if built.total>0 {assert((prefix+tail).drop_first().drop_first() =~= tail);}else{assert(prefix+tail =~= tail);},
            Err(_)=>{assert(prefix+tail =~= tail);},
        }
    }
    assert(part2_tag_storage_prefix(width,height,maximum,prefix,result));
}
pub(crate) proof fn part2_tag_storage_observed(width:u32,height:u32,maximum:u64,built:Part1TagBuild,result:Result<(),crate::DecodeError>)
    requires part2_tag_storage_admit(width,height,maximum)==Ok(built),
        result==Ok(()) || (built.total>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part1_tag_storage_result(width,height,maximum,if result.is_ok(){part1_tag_initial(width,height,maximum)}else{Err(crate::DecodeError::AllocationFailed)}),
{
    let value=if result.is_ok(){part1_tag_initial(width,height,maximum)}else{Err(crate::DecodeError::AllocationFailed)};
    let prefix=if built.total==0{Seq::empty()}else{seq![
        Part2TagStorageEvent {width,height,maximum,built,levels:true,succeeded:true},
        Part2TagStorageEvent {width,height,maximum,built,levels:false,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2TagStorageEvent>|part2_tag_storage_run(width,height,maximum,prefix+tail)==Some((value,tail)) by{
        if built.total==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first().drop_first() =~= tail);}
    }
    assert(part2_tag_storage_prefix(width,height,maximum,prefix,value));
}
pub(crate) proof fn part2_tag_storage_levels_refused(width:u32,height:u32,maximum:u64,built:Part1TagBuild)
    requires part2_tag_storage_admit(width,height,maximum)==Ok(built),built.total>0,
    ensures part1_tag_storage_result(width,height,maximum,Err(crate::DecodeError::AllocationFailed)),
{
    let prefix=seq![Part2TagStorageEvent {width,height,maximum,built,levels:true,succeeded:false}];
    assert forall|tail:Seq<Part2TagStorageEvent>|
        part2_tag_storage_run(width,height,maximum,prefix+tail)==Some((Err(crate::DecodeError::AllocationFailed),tail)) by{
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_tag_storage_prefix(width,height,maximum,prefix,Err(crate::DecodeError::AllocationFailed)));
}
pub struct Part2PrecinctTreeContext {
    pub before:Part1PacketPrecinctState,pub total:u64,pub execution:Part2PacketSubbandExecution,pub index:usize,
    pub zero:bool,pub inclusion:Option<Part1TagTree>,pub maximum:u64,
}
pub(crate) open spec fn part2_precinct_tree_run(context:Part2PrecinctTreeContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1TagTree> {
    let width=context.execution.across;let height=context.execution.down;let maximum=context.maximum;
    match part2_tag_storage_admit(width,height,maximum) {
        Err(error)=>Some((Err(error),events)),
        Ok(built)=>if built.total==0 {Some((part1_tag_initial(width,height,maximum),events))}
        else if events.len()==0 {None}else{
            match events[0] {
                Part2JpipSnapshotEvent::PrecinctTagTree {context:actual,calls}=>if actual!=context{None}else{
                    match part2_tag_storage_run(width,height,maximum,calls) {
                        Some((result,rest))=>if rest.len()==0 {Some((result,events.drop_first()))}else{None},
                        None=>None,
                    }
                },
                _=>None,
            }
        },
    }
}
pub(crate) proof fn part2_precinct_tree_observed(context:Part2PrecinctTreeContext,result:Result<Part1TagTree,crate::DecodeError>)
    requires part1_tag_storage_result(context.execution.across,context.execution.down,context.maximum,result),
    ensures part2_cold_framed(|events|part2_precinct_tree_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1TagTree>|
            (forall|events| #[trigger] other(events)==part2_precinct_tree_run(context,events)) ==> #[trigger] part2_cold_framed(other,result),
{
    let width=context.execution.across;let height=context.execution.down;let maximum=context.maximum;
    let calls=choose|prefix:Seq<Part2TagStorageEvent>| #[trigger] part2_tag_storage_prefix(width,height,maximum,prefix,result);
    assert(calls+Seq::empty() =~= calls);
    assert(part2_tag_storage_run(width,height,maximum,calls)==Some((result,Seq::empty())));
    let prefix=match part2_tag_storage_admit(width,height,maximum) {
        Err(_)=>Seq::empty(),Ok(built)=>if built.total==0{Seq::empty()}else{seq![Part2JpipSnapshotEvent::PrecinctTagTree {context,calls}]},
    };
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_precinct_tree_run(context,prefix+tail)==Some((result,tail)) by{
        match part2_tag_storage_admit(width,height,maximum) {
            Ok(built)=>if built.total>0 {assert((prefix+tail).drop_first() =~= tail);}else{assert(prefix+tail =~= tail);},
            Err(_)=>{assert(prefix+tail =~= tail);},
        }
    }
    assert(part2_cold_prefix(|events|part2_precinct_tree_run(context,events),prefix,result));
    part2_decode_eta(|events|part2_precinct_tree_run(context,events),result);
}
pub(crate) proof fn part2_precinct_tree_normal(context:Part2PrecinctTreeContext)
    ensures part2_cold_framed(|events|part2_precinct_tree_run(context,events),part1_tag_initial(context.execution.across,context.execution.down,context.maximum)),
{
    part2_tag_storage_normal(context.execution.across,context.execution.down,context.maximum);
    part2_precinct_tree_observed(context,part1_tag_initial(context.execution.across,context.execution.down,context.maximum));
}
}
