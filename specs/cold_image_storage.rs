//! Reached image assembly metadata storage before component traversal.
use super::*;
verus! {
pub struct Part2AssemblyOwnerContext {
    pub size:Part1AssemblySize,pub tiles:Seq<Part1AssemblyTile>,pub selection:Option<([u32;4],u8)>,pub maximum:u64,
}
pub(crate) open spec fn part2_assembly_owner_admit(context:Part2AssemblyOwnerContext)->Result<(),crate::DecodeError> {
    match context.selection {
        None=>Ok(()),Some((region,discard))=>match part1_assembly_selected_header(region,discard){Err(error)=>Err(error),Ok(_)=>Ok(())},
    }
}
    pub(crate) open spec fn part2_decode_prepared_storage_finish(image:Part1DecodedImageModel,transform:crate::decode::ComponentTransform)
        ->Result<Part1DecodedImageModel,crate::DecodeError> {
        let result=match transform {
            crate::decode::ComponentTransform::None=>(Ok(()),image),
            crate::decode::ComponentTransform::Reversible=>part1_apply_component_transform(image,false),
            crate::decode::ComponentTransform::Irreversible=>part1_apply_component_transform(image,true),
        };
        match result.0{Err(error)=>Err(error),Ok(())=>Ok(result.1)}
    }
    pub(crate) open spec fn part2_decode_prepared_storage_run(size:Part1AssemblySize,tiles:Seq<Part1AssemblyTile>,transform:crate::decode::ComponentTransform,maximum:u64,
        calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1DecodedImageModel> {
        part2_tier1_storage_bind(part2_assembly_storage_run(Part2AssemblyOwnerContext {size,tiles,selection:None,maximum},calls),
            |image:Part1DecodedImageModel,rest|Some((part2_decode_prepared_storage_finish(image,transform),rest)))
    }
    pub closed spec fn part2_decode_prepared_storage_result(size:Part1AssemblySize,tiles:Seq<Part1AssemblyTile>,transform:crate::decode::ComponentTransform,maximum:u64,
        result:Result<Part1DecodedImageModel,crate::DecodeError>)->bool {
        part2_tier1_storage_framed(|calls|part2_decode_prepared_storage_run(size,tiles,transform,maximum,calls),result)
    }
    pub(crate) proof fn part2_decode_prepared_storage_normal(size:Part1AssemblySize,tiles:Seq<Part1AssemblyTile>,transform:crate::decode::ComponentTransform,maximum:u64)
        ensures part2_decode_prepared_storage_result(size,tiles,transform,maximum,part1_decode_prepared_image(size,tiles,transform,maximum)),
    {
        let context=Part2AssemblyOwnerContext {size,tiles,selection:None,maximum};
        let result=part1_decode_prepared_image(size,tiles,transform,maximum);
        let image=part1_assemble_image(size,tiles,maximum);
        part2_assembly_storage_normal(context);
        if let Ok(value)=image{part2_tier1_storage_pure(part2_decode_prepared_storage_finish(value,transform));}
        part2_tier1_storage_bind_frame(|calls|part2_assembly_storage_run(context,calls),
            |image:Part1DecodedImageModel,rest|Some((part2_decode_prepared_storage_finish(image,transform),rest)),image,result);
    }
    pub(crate) proof fn part2_decode_prepared_assembly_error(size:Part1AssemblySize,tiles:Seq<Part1AssemblyTile>,transform:crate::decode::ComponentTransform,maximum:u64,error:crate::DecodeError)
        requires part2_assembly_storage_result(Part2AssemblyOwnerContext {size,tiles,selection:None,maximum},Err(error)),
        ensures part2_decode_prepared_storage_result(size,tiles,transform,maximum,Err(error)),
    {
        part2_tier1_storage_bind_frame(|calls|part2_assembly_storage_run(Part2AssemblyOwnerContext {size,tiles,selection:None,maximum},calls),
            |image:Part1DecodedImageModel,rest|Some((part2_decode_prepared_storage_finish(image,transform),rest)),Err(error),Err(error));
    }
pub(crate) proof fn part2_decode_prepared_storage_frames(size:Part1AssemblySize,tiles:Seq<Part1AssemblyTile>,transform:crate::decode::ComponentTransform,maximum:u64,
    result:Result<Part1DecodedImageModel,crate::DecodeError>)
    requires part2_decode_prepared_storage_result(size,tiles,transform,maximum,result),
    ensures part2_tier1_storage_framed(|calls|part2_decode_prepared_storage_run(size,tiles,transform,maximum,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1DecodedImageModel>|
            (forall|calls| #[trigger] other(calls)==part2_decode_prepared_storage_run(size,tiles,transform,maximum,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{
    part2_tier1_storage_eta(|calls|part2_decode_prepared_storage_run(size,tiles,transform,maximum,calls),result);
}
pub(crate) open spec fn part2_assembly_owner_run(context:Part2AssemblyOwnerContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    if context.size.4==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0] {
        Part2Tier1StorageEvent::AssemblyOwnerCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=context.size.4 as nat {None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) open spec fn part2_assembly_storage_run(context:Part2AssemblyOwnerContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1DecodedImageModel> {
    match part2_assembly_owner_admit(context) {
        Err(error)=>Some((Err(error),calls)),
        Ok(())=>part2_tier1_storage_bind(part2_assembly_owner_run(context,calls),
            |_:(),rest|Some((part2_assemble_prepared(context.size,context.tiles,context.selection,context.maximum),rest))),
    }
}
pub closed spec fn part2_assembly_storage_result(context:Part2AssemblyOwnerContext,result:Result<Part1DecodedImageModel,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_assembly_storage_run(context,calls),result)
}
pub(crate) proof fn part2_assembly_owner_observed(context:Part2AssemblyOwnerContext,response:Result<(),crate::DecodeError>)
    requires response==Ok(()) || (context.size.4>0 && response==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_tier1_storage_framed(|calls|part2_assembly_owner_run(context,calls),response),
{
    let prefix=if context.size.4==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::AssemblyOwnerCapacity {context,elements:context.size.4 as nat,succeeded:response.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_assembly_owner_run(context,prefix+tail)==Some((response,tail)) by{
        if context.size.4==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_assembly_owner_run(context,calls),prefix,response));
}
pub(crate) proof fn part2_assembly_storage_normal(context:Part2AssemblyOwnerContext)
    ensures part2_assembly_storage_result(context,part2_assemble_prepared(context.size,context.tiles,context.selection,context.maximum)),
{
    let result=part2_assemble_prepared(context.size,context.tiles,context.selection,context.maximum);
    part2_tier1_storage_pure(result);
    if part2_assembly_owner_admit(context).is_ok() {
        part2_assembly_owner_observed(context,Ok(()));
        part2_tier1_storage_bind_frame(|calls|part2_assembly_owner_run(context,calls),
            |_:(),rest|Some((part2_assemble_prepared(context.size,context.tiles,context.selection,context.maximum),rest)),Ok(()),result);
    }
}
pub(crate) proof fn part2_assembly_storage_refused(context:Part2AssemblyOwnerContext,response:Result<(),crate::DecodeError>)
    requires part2_assembly_owner_admit(context)==Ok(()),response==Err(crate::DecodeError::AllocationFailed),
        part2_tier1_storage_framed(|calls|part2_assembly_owner_run(context,calls),response),
    ensures part2_assembly_storage_result(context,Err(crate::DecodeError::AllocationFailed)),
{
    part2_tier1_storage_bind_frame(|calls|part2_assembly_owner_run(context,calls),
        |_:(),rest|Some((part2_assemble_prepared(context.size,context.tiles,context.selection,context.maximum),rest)),response,Err(crate::DecodeError::AllocationFailed));
}
pub(crate) open spec fn part2_assembly_calls_run(context:Part2AssemblyOwnerContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedImageModel> {
    if events.len()==0{None}else{match events[0] {
        Part2JpipSnapshotEvent::AssemblyCalls {context:actual,calls}=>if actual!=context{None}else{
            match part2_assembly_storage_run(context,calls){Some((result,rest))=>if rest.len()==0{Some((result,events.drop_first()))}else{None},None=>None}
        },
        _=>None,
    }}
}
pub(crate) proof fn part2_assembly_calls_observed(context:Part2AssemblyOwnerContext,result:Result<Part1DecodedImageModel,crate::DecodeError>)
    requires part2_assembly_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_assembly_calls_run(context,events),result),
{
    let run=|calls|part2_assembly_storage_run(context,calls);
    let calls=choose|prefix| #[trigger] part2_tier1_storage_prefix(run,prefix,result);
    assert(calls+Seq::empty() =~= calls);
    assert(run(calls)==Some((result,Seq::empty())));
    let prefix=seq![Part2JpipSnapshotEvent::AssemblyCalls {context,calls}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_assembly_calls_run(context,prefix+tail)==Some((result,tail)) by{
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|part2_assembly_calls_run(context,events),prefix,result));
    part2_decode_eta(|events|part2_assembly_calls_run(context,events),result);
}
}
