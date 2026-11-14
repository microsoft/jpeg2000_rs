//! Fresh grid constructor requests, separate from packet/decode preparation.
use super::*;
verus! {
pub enum Part2GridCapacityContext {
    Offsets { counts:Seq<u32>, resolutions:Seq<u8>, maximum:u8, expected:usize },
    Uniform { layers:u16, components:u16, resolutions:u8, counts:Seq<u32> },
}
pub(crate) open spec fn part2_grid_capacity_count(context:Part2GridCapacityContext)->usize {
    match context {
        Part2GridCapacityContext::Offsets {expected,..}=>(expected+1) as usize,
        Part2GridCapacityContext::Uniform {components,..}=>components as usize,
    }
}
pub(crate) open spec fn part2_grid_capacity_run(context:Part2GridCapacityContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_grid_capacity_count(context);
    if count==0 {Some((Ok(()),events))}else if events.len()==0 {None}else{
        match events[0] {
            Part2JpipSnapshotEvent::GridCapacity {context:actual,elements,succeeded}=>
                if actual!=context || elements!=count {None}else{
                    Some((if succeeded {Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))
                },
            _=>None,
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_grid_capacity_result(context:Part2GridCapacityContext,result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_grid_capacity_run(context,events),result)
}
pub(crate) proof fn part2_grid_capacity_observed(context:Part2GridCapacityContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_grid_capacity_count(context)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_grid_capacity_result(context,result),
{
    reveal(part2_grid_capacity_result);
    let count=part2_grid_capacity_count(context);
    let calls=if count==0 {Seq::empty()}else{seq![Part2JpipSnapshotEvent::GridCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_grid_capacity_run(context,calls+tail)==Some((result,tail)) by {
        if count==0 {assert(calls+tail =~= tail);}else{assert((calls+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_grid_capacity_run(context,events),calls,result));
}
pub(crate) open spec fn part2_grid_summary_run(counts:Seq<u32>,resolutions:Seq<u8>,maximum:u8,expected:usize,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1GridCountState> {
    if expected==usize::MAX {Some((part1_grid_count_summary(counts,resolutions,maximum,expected),events))}
    else {part2_jpip_snapshot_bind(part2_grid_capacity_run(Part2GridCapacityContext::Offsets {counts,resolutions,maximum,expected},events),
        |_:(),rest|Some((part1_grid_count_summary(counts,resolutions,maximum,expected),rest)))}
}
#[verifier::opaque]
pub(crate) open spec fn part2_grid_summary_result(counts:Seq<u32>,resolutions:Seq<u8>,maximum:u8,expected:usize,result:Result<Part1GridCountState,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_grid_summary_run(counts,resolutions,maximum,expected,events),result)
}
pub(crate) proof fn part2_grid_summary_normal(counts:Seq<u32>,resolutions:Seq<u8>,maximum:u8,expected:usize)
    ensures part2_grid_summary_result(counts,resolutions,maximum,expected,part1_grid_count_summary(counts,resolutions,maximum,expected)),
{
    reveal(part2_grid_summary_result);reveal(part2_grid_capacity_result);
    let result=part1_grid_count_summary(counts,resolutions,maximum,expected);
    if expected==usize::MAX {part2_cold_pure::<Part1GridCountState>(result);}else{
        let context=Part2GridCapacityContext::Offsets {counts,resolutions,maximum,expected};
        part2_grid_capacity_observed(context,Ok(()));part2_cold_pure(result);
        part2_cold_bind(|events|part2_grid_capacity_run(context,events),|_:(),rest|Some((result,rest)),Ok(()),result);
    }
}
pub(crate) proof fn part2_grid_summary_refused(counts:Seq<u32>,resolutions:Seq<u8>,maximum:u8,expected:usize)
    requires expected<usize::MAX,part2_grid_capacity_result(Part2GridCapacityContext::Offsets {counts,resolutions,maximum,expected},Err(crate::DecodeError::AllocationFailed)),
    ensures part2_grid_summary_result(counts,resolutions,maximum,expected,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_grid_summary_result);reveal(part2_grid_capacity_result);
    let context=Part2GridCapacityContext::Offsets {counts,resolutions,maximum,expected};
    part2_cold_bind(|events|part2_grid_capacity_run(context,events),|_:(),rest|Some((part1_grid_count_summary(counts,resolutions,maximum,expected),rest)),
        Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) open spec fn part2_grid_admit(layers:u16,components:u16,resolutions:Seq<u8>,counts:Seq<u32>,limits:&crate::ResourceLimits)
    ->Result<(u8,usize),crate::DecodeError> {
    match part1_grid_resolution_summary(resolutions,0,0,false) {
        Err(error)=>Err(error),Ok((maximum,zero))=>{
            if layers==0 || components==0 || maximum==0 || resolutions.len()!=components as nat || zero {
                Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
            }else if layers>crate::limits::resource_layer_limit(limits){
                Err(part1_packet_reader_limit(crate::Resource::Layers,crate::limits::resource_layer_limit(limits) as u64,layers as u64))
            }else if components>crate::limits::resource_component_limit(limits){
                Err(part1_packet_reader_limit(crate::Resource::Components,crate::limits::resource_component_limit(limits) as u64,components as u64))
            }else if maximum>crate::limits::resource_resolution_limit(limits){
                Err(part1_packet_reader_limit(crate::Resource::Resolutions,crate::limits::resource_resolution_limit(limits) as u64,maximum as u64))
            }else if components as nat*maximum as nat>usize::MAX{
                Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
            }else if counts.len()!=components as nat*maximum as nat{
                Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
            }else{Ok((maximum,(components as nat*maximum as nat) as usize))}
        },
    }
}
pub(crate) open spec fn part2_grid_run(layers:u16,components:u16,resolutions:Seq<u8>,counts:Seq<u32>,selected:Option<Seq<u8>>,
    limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketGrid> {
    match part2_grid_admit(layers,components,resolutions,counts,limits) {
        Err(error)=>Some((Err(error),events)),
        Ok((maximum,expected))=>part2_jpip_snapshot_bind(part2_grid_summary_run(counts,resolutions,maximum,expected,events),
            |_:Part1GridCountState,rest|Some((part1_packet_grid_new(layers,components,resolutions,counts,selected,limits),rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_grid_result(layers:u16,components:u16,resolutions:Seq<u8>,counts:Seq<u32>,selected:Option<Seq<u8>>,
    limits:&crate::ResourceLimits,result:Result<Part1PacketGrid,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_grid_run(layers,components,resolutions,counts,selected,limits,events),result)
}
pub(crate) proof fn part2_grid_normal(layers:u16,components:u16,resolutions:Seq<u8>,counts:Seq<u32>,selected:Option<Seq<u8>>,limits:&crate::ResourceLimits)
    ensures part2_grid_result(layers,components,resolutions,counts,selected,limits,part1_packet_grid_new(layers,components,resolutions,counts,selected,limits)),
{
    reveal(part2_grid_result);reveal(part2_grid_summary_result);
    let result=part1_packet_grid_new(layers,components,resolutions,counts,selected,limits);
    match part2_grid_admit(layers,components,resolutions,counts,limits) {
        Err(_)=>{part2_cold_pure::<Part1PacketGrid>(result);},
        Ok((maximum,expected))=>{
            part2_grid_summary_normal(counts,resolutions,maximum,expected);
            let summary=part1_grid_count_summary(counts,resolutions,maximum,expected);
            if summary.is_ok(){part2_cold_pure(result);}
            part2_cold_bind(|events|part2_grid_summary_run(counts,resolutions,maximum,expected,events),
                |_:Part1GridCountState,rest|Some((result,rest)),summary,result);
        },
    }
}
pub(crate) proof fn part2_grid_summary_error(layers:u16,components:u16,resolutions:Seq<u8>,counts:Seq<u32>,selected:Option<Seq<u8>>,limits:&crate::ResourceLimits,
    maximum:u8,expected:usize,error:crate::DecodeError)
    requires part2_grid_admit(layers,components,resolutions,counts,limits)==Ok((maximum,expected)),
        part2_grid_summary_result(counts,resolutions,maximum,expected,Err(error)),
    ensures part2_grid_result(layers,components,resolutions,counts,selected,limits,Err(error)),
{
    reveal(part2_grid_result);reveal(part2_grid_summary_result);
    part2_cold_bind(|events|part2_grid_summary_run(counts,resolutions,maximum,expected,events),
        |_:Part1GridCountState,rest|Some((part1_packet_grid_new(layers,components,resolutions,counts,selected,limits),rest)),Err(error),Err(error));
}
pub(crate) open spec fn part2_uniform_grid_run(layers:u16,components:u16,resolutions:u8,counts:Seq<u32>,limits:&crate::ResourceLimits,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketGrid> {
    part2_jpip_snapshot_bind(part2_grid_capacity_run(Part2GridCapacityContext::Uniform {layers,components,resolutions,counts},events),
        |_:(),rest|part2_grid_run(layers,components,Seq::new(components as nat,|_:int|resolutions),counts,None,limits,rest))
}
pub open spec fn part1_uniform_grid_model(layers:u16,components:u16,resolutions:u8,counts:Seq<u32>,limits:&crate::ResourceLimits)->Result<Part1PacketGrid,crate::DecodeError> {
    part1_packet_grid_new(layers,components,Seq::new(components as nat,|_:int|resolutions),counts,None,limits)
}
pub closed spec fn part1_uniform_grid_cold_result(layers:u16,components:u16,resolutions:u8,counts:Seq<u32>,limits:&crate::ResourceLimits,
    result:Result<Part1PacketGrid,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_uniform_grid_run(layers,components,resolutions,counts,limits,events),result)
}
pub(crate) proof fn part2_uniform_grid_frames(layers:u16,components:u16,resolutions:u8,counts:Seq<u32>,limits:&crate::ResourceLimits,result:Result<Part1PacketGrid,crate::DecodeError>)
    requires part1_uniform_grid_cold_result(layers,components,resolutions,counts,limits,result),
    ensures part2_cold_framed(|events|part2_uniform_grid_run(layers,components,resolutions,counts,limits,events),result),
{
    part2_decode_eta(|events|part2_uniform_grid_run(layers,components,resolutions,counts,limits,events),result);
}
pub(crate) proof fn part2_uniform_grid_normal(layers:u16,components:u16,resolutions:u8,counts:Seq<u32>,limits:&crate::ResourceLimits)
    ensures part1_uniform_grid_cold_result(layers,components,resolutions,counts,limits,
        part1_packet_grid_new(layers,components,Seq::new(components as nat,|_:int|resolutions),counts,None,limits)),
{
    reveal(part2_grid_result);reveal(part2_grid_capacity_result);
    let context=Part2GridCapacityContext::Uniform {layers,components,resolutions,counts};
    let result=part1_packet_grid_new(layers,components,Seq::new(components as nat,|_:int|resolutions),counts,None,limits);
    part2_grid_capacity_observed(context,Ok(()));
    part2_grid_normal(layers,components,Seq::new(components as nat,|_:int|resolutions),counts,None,limits);
    part2_decode_eta(|events|part2_grid_run(layers,components,Seq::new(components as nat,|_:int|resolutions),counts,None,limits,events),result);
    part2_cold_bind(|events|part2_grid_capacity_run(context,events),
        |_:(),rest|part2_grid_run(layers,components,Seq::new(components as nat,|_:int|resolutions),counts,None,limits,rest),Ok(()),result);
}
pub(crate) proof fn part2_uniform_grid_actual(layers:u16,components:u16,resolutions:u8,counts:Seq<u32>,limits:&crate::ResourceLimits,
    response:Result<(),crate::DecodeError>,result:Result<Part1PacketGrid,crate::DecodeError>)
    requires part2_grid_capacity_result(Part2GridCapacityContext::Uniform {layers,components,resolutions,counts},response),
        match response {Err(error)=>result==Err(error),Ok(())=>part2_grid_result(layers,components,Seq::new(components as nat,|_:int|resolutions),counts,None,limits,result)},
    ensures part1_uniform_grid_cold_result(layers,components,resolutions,counts,limits,result),
{
    reveal(part2_grid_capacity_result);reveal(part2_grid_result);
    if response.is_ok(){part2_decode_eta(|events|part2_grid_run(layers,components,Seq::new(components as nat,|_:int|resolutions),counts,None,limits,events),result);}
    part2_cold_bind(|events|part2_grid_capacity_run(Part2GridCapacityContext::Uniform {layers,components,resolutions,counts},events),
        |_:(),rest|part2_grid_run(layers,components,Seq::new(components as nat,|_:int|resolutions),counts,None,limits,rest),response,result);
}
}
