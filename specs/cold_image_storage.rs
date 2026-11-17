//! Reached image assembly metadata storage before component traversal.
use super::*;
verus! {
pub struct Part2AssemblyOwnerContext {
    pub size:Part1AssemblySize,pub tiles:Seq<Part1AssemblyTile>,pub selection:Option<([u32;4],u8)>,pub maximum:u64,
}
pub struct Part2AssemblyPlaneContext {
    pub image:Part1DecodedImageModel,pub bytes:u64,pub size:Part1AssemblySize,pub tiles:Seq<Part1AssemblyTile>,
    pub component:u16,pub extent:(u32,u32),pub selection:Part1AssemblySelection,pub maximum:u64,
}
pub enum Part2AssemblyPlaneStage {
    Samples,Visited {samples:Seq<i64>},Publish {plane:Part1AssemblyPlane},
}
pub(crate) open spec fn part2_assembly_plane_preflight(context:Part2AssemblyPlaneContext)
    ->(Result<(Part1AssemblyDimensions,usize,Option<(u32,u32,u32,u32)>),crate::DecodeError>,u64) {
    match part1_assembly_component_dimensions(context.size,context.component,context.extent,context.selection) {
        Err(error)=>(Err(error),context.bytes),
        Ok(dimensions)=>match part1_transform_area(dimensions.1,dimensions.2) {
            Err(error)=>(Err(error),context.bytes),Ok(count)=>{
                let charged=part1_accumulate_decoded_bytes(count as nat,context.bytes,context.maximum);
                match charged.0 {
                    Err(error)=>(Err(error),charged.1),
                    Ok(())=>match part1_assembly_component_crop(context.size,dimensions,context.selection.is_some()) {
                        Err(error)=>(Err(error),charged.1),Ok(crop)=>(Ok((dimensions,count,crop)),charged.1),
                    },
                }
            },
        },
    }
}
pub(crate) open spec fn part2_assembly_plane_finish(context:Part2AssemblyPlaneContext,dimensions:Part1AssemblyDimensions,bytes:u64,
    collected:Part1AssemblyPlaneState)->Part1AssemblyState {
    match collected.0 {
        Err(error)=>(Err(error),context.image,bytes),
        Ok(())=>match collected.1.2 {
            None=>(Err(part1_image_error(false)),context.image,bytes),
            Some(fraction)=>(Ok(()),(context.image.0,context.image.1,context.image.2,context.image.3,
                context.image.4.push((dimensions.1,dimensions.2,dimensions.0,fraction,collected.1.3))),bytes),
        },
    }
}
pub(crate) open spec fn part2_assembly_plane_capacity_run(context:Part2AssemblyPlaneContext,stage:Part2AssemblyPlaneStage,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let preflight=part2_assembly_plane_preflight(context);
    let count=match stage {Part2AssemblyPlaneStage::Publish {..}=>1nat,_=>if preflight.0.is_ok(){preflight.0.get_Ok_0().1 as nat}else{0nat}};
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0] {
        Part2Tier1StorageEvent::AssemblyPlaneCapacity {context:actual,stage:actual_stage,elements,succeeded}=>
            if actual!=context || actual_stage!=stage || elements!=count {None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) open spec fn part2_assembly_plane_after_visited_run(context:Part2AssemblyPlaneContext,samples:Seq<i64>,visited:Seq<bool>,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1AssemblyState> {
    let preflight=part2_assembly_plane_preflight(context);let bytes=preflight.1;
    match preflight.0 {
        Err(error)=>Some((Ok((Err(error),context.image,bytes)),calls)),
        Ok((dimensions,count,crop))=>{
            let initial=(dimensions.1,dimensions.2,None,samples,visited);
            let collected=part1_collect_assembly_tiles(initial,context.tiles,context.component,crop);
            let ordinary=part2_assembly_plane_finish(context,dimensions,bytes,collected);
            if ordinary.0.is_err(){Some((Ok(ordinary),calls))}else{
                part2_tier1_storage_resume(part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Publish {plane:collected.1},calls),
                    |response:Result<(),crate::DecodeError>,rest|Some((Ok(match response {
                        Err(error)=>(Err(error),context.image,bytes),Ok(())=>ordinary,
                    }),rest)))
            }
        },
    }
}
pub(crate) open spec fn part2_assembly_plane_after_samples_run(context:Part2AssemblyPlaneContext,samples:Seq<i64>,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1AssemblyState> {
    let preflight=part2_assembly_plane_preflight(context);
    match preflight.0 {
        Err(error)=>Some((Ok((Err(error),context.image,preflight.1)),calls)),
        Ok((_,count,_))=>part2_tier1_storage_resume(part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Visited {samples},calls),
            |response:Result<(),crate::DecodeError>,rest|match response {
                Err(error)=>Some((Ok((Err(error),context.image,preflight.1)),rest)),
                Ok(())=>part2_assembly_plane_after_visited_run(context,samples,Seq::new(count as nat,|_:int|false),rest),
            }),
    }
}
pub(crate) open spec fn part2_assembly_plane_run(context:Part2AssemblyPlaneContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1AssemblyState> {
    let preflight=part2_assembly_plane_preflight(context);
    match preflight.0 {
        Err(error)=>Some((Ok((Err(error),context.image,preflight.1)),calls)),
        Ok((_,count,_))=>part2_tier1_storage_resume(part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Samples,calls),
            |response:Result<(),crate::DecodeError>,rest|match response {
                Err(error)=>Some((Ok((Err(error),context.image,preflight.1)),rest)),
                Ok(())=>part2_assembly_plane_after_samples_run(context,Seq::new(count as nat,|_:int|0i64),rest),
            }),
    }
}
pub(crate) open spec fn part2_assembly_plane_result(context:Part2AssemblyPlaneContext,result:Part1AssemblyState)->bool {
    part2_tier1_storage_framed(|calls|part2_assembly_plane_run(context,calls),Ok(result))
}
pub(crate) open spec fn part2_assembly_plane_value(context:Part2AssemblyPlaneContext,samples:Seq<i64>,visited:Seq<bool>)->Part1AssemblyState {
    let preflight=part2_assembly_plane_preflight(context);
    match preflight.0 {
        Err(error)=>(Err(error),context.image,preflight.1),
        Ok((dimensions,_,crop))=>part2_assembly_plane_finish(context,dimensions,preflight.1,
            part1_collect_assembly_tiles((dimensions.1,dimensions.2,None,samples,visited),context.tiles,context.component,crop)),
    }
}
pub(crate) open spec fn part2_assembly_plane_count(context:Part2AssemblyPlaneContext)->nat {
    let preflight=part2_assembly_plane_preflight(context);
    if preflight.0.is_ok(){preflight.0.get_Ok_0().1 as nat}else{0nat}
}
pub(crate) proof fn part2_assembly_plane_capacity_observed(context:Part2AssemblyPlaneContext,stage:Part2AssemblyPlaneStage,response:Result<(),crate::DecodeError>)
    requires response==Ok(()) || (response==Err(crate::DecodeError::AllocationFailed)
        && (stage is Publish || part2_assembly_plane_count(context)>0)),
    ensures part2_tier1_storage_framed(|calls|part2_assembly_plane_capacity_run(context,stage,calls),response),
{
    let count=if stage is Publish{1nat}else{part2_assembly_plane_count(context)};
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::AssemblyPlaneCapacity {context,stage,elements:count,succeeded:response.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_assembly_plane_capacity_run(context,stage,prefix+tail)==Some((response,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_assembly_plane_capacity_run(context,stage,calls),prefix,response));
}
pub(crate) proof fn part2_assembly_plane_after_visited_normal(context:Part2AssemblyPlaneContext,samples:Seq<i64>,visited:Seq<bool>)
    ensures part2_tier1_storage_framed(|calls|part2_assembly_plane_after_visited_run(context,samples,visited,calls),Ok(part2_assembly_plane_value(context,samples,visited))),
{
    let preflight=part2_assembly_plane_preflight(context);
    let ordinary=part2_assembly_plane_value(context,samples,visited);
    part2_tier1_storage_pure(Ok(ordinary));
    if let Ok((dimensions,_,crop))=preflight.0 {
        let collected=part1_collect_assembly_tiles((dimensions.1,dimensions.2,None,samples,visited),context.tiles,context.component,crop);
        if ordinary.0.is_ok(){
            let stage=Part2AssemblyPlaneStage::Publish {plane:collected.1};
            part2_assembly_plane_capacity_observed(context,stage,Ok(()));
            part2_tier1_resume_frame(|calls|part2_assembly_plane_capacity_run(context,stage,calls),
                |response:Result<(),crate::DecodeError>,rest|Some((Ok(match response {
                    Err(error)=>(Err(error),context.image,preflight.1),Ok(())=>ordinary,
                }),rest)),Ok(()),Ok(ordinary));
        }
    }
}
pub(crate) proof fn part2_assembly_plane_after_samples_normal(context:Part2AssemblyPlaneContext,samples:Seq<i64>)
    ensures part2_tier1_storage_framed(|calls|part2_assembly_plane_after_samples_run(context,samples,calls),
        Ok(part2_assembly_plane_value(context,samples,Seq::new(part2_assembly_plane_count(context),|_:int|false)))),
{
    let preflight=part2_assembly_plane_preflight(context);
    let visited=Seq::new(part2_assembly_plane_count(context),|_:int|false);
    let ordinary=part2_assembly_plane_value(context,samples,visited);
    if preflight.0.is_err(){part2_tier1_storage_pure(Ok(ordinary));}else{
        let stage=Part2AssemblyPlaneStage::Visited {samples};
        part2_assembly_plane_capacity_observed(context,stage,Ok(()));
        part2_assembly_plane_after_visited_normal(context,samples,visited);
        part2_tier1_storage_eta(|calls|part2_assembly_plane_after_visited_run(context,samples,visited,calls),Ok(ordinary));
        part2_tier1_resume_frame(|calls|part2_assembly_plane_capacity_run(context,stage,calls),
            |response:Result<(),crate::DecodeError>,rest|match response {
                Err(error)=>Some((Ok((Err(error),context.image,preflight.1)),rest)),
                Ok(())=>part2_assembly_plane_after_visited_run(context,samples,visited,rest),
            },Ok(()),Ok(ordinary));
    }
}
pub(crate) proof fn part2_assembly_plane_normal(context:Part2AssemblyPlaneContext)
    ensures part2_assembly_plane_result(context,part1_assembly_append_plane(context.image,context.bytes,context.size,context.tiles,context.component,context.extent,context.selection,context.maximum)),
{
    let preflight=part2_assembly_plane_preflight(context);
    let samples=Seq::new(part2_assembly_plane_count(context),|_:int|0i64);
    let visited=Seq::new(part2_assembly_plane_count(context),|_:int|false);
    let ordinary=part1_assembly_append_plane(context.image,context.bytes,context.size,context.tiles,context.component,context.extent,context.selection,context.maximum);
    assert(ordinary==part2_assembly_plane_value(context,samples,visited));
    if preflight.0.is_err(){part2_tier1_storage_pure(Ok(ordinary));}else{
        let stage=Part2AssemblyPlaneStage::Samples;
        part2_assembly_plane_capacity_observed(context,stage,Ok(()));
        part2_assembly_plane_after_samples_normal(context,samples);
        part2_tier1_storage_eta(|calls|part2_assembly_plane_after_samples_run(context,samples,calls),Ok(ordinary));
        part2_tier1_resume_frame(|calls|part2_assembly_plane_capacity_run(context,stage,calls),
            |response:Result<(),crate::DecodeError>,rest|match response {
                Err(error)=>Some((Ok((Err(error),context.image,preflight.1)),rest)),
                Ok(())=>part2_assembly_plane_after_samples_run(context,samples,rest),
            },Ok(()),Ok(ordinary));
    }
}
pub(crate) proof fn part2_assembly_plane_samples_refused(context:Part2AssemblyPlaneContext)
    requires part2_assembly_plane_preflight(context).0.is_ok(),
        part2_tier1_storage_framed(|calls|part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Samples,calls),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_assembly_plane_result(context,(Err(crate::DecodeError::AllocationFailed),context.image,part2_assembly_plane_preflight(context).1)),
{
    let preflight=part2_assembly_plane_preflight(context);
    let ordinary=Ok((Err(crate::DecodeError::AllocationFailed),context.image,preflight.1));
    part2_tier1_storage_pure(ordinary);
    part2_tier1_resume_frame(|calls|part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Samples,calls),
        |response:Result<(),crate::DecodeError>,rest|match response {
            Err(error)=>Some((Ok((Err(error),context.image,preflight.1)),rest)),
            Ok(())=>part2_assembly_plane_after_samples_run(context,Seq::new(part2_assembly_plane_count(context),|_:int|0i64),rest),
        },Err(crate::DecodeError::AllocationFailed),ordinary);
}
pub(crate) proof fn part2_assembly_plane_visited_refused(context:Part2AssemblyPlaneContext)
    requires part2_assembly_plane_preflight(context).0.is_ok(),
        part2_tier1_storage_framed(|calls|part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Visited {samples:Seq::new(part2_assembly_plane_count(context),|_:int|0i64)},calls),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_assembly_plane_result(context,(Err(crate::DecodeError::AllocationFailed),context.image,part2_assembly_plane_preflight(context).1)),
{
    let preflight=part2_assembly_plane_preflight(context);let samples=Seq::new(part2_assembly_plane_count(context),|_:int|0i64);
    let ordinary=Ok((Err(crate::DecodeError::AllocationFailed),context.image,preflight.1));
    part2_tier1_storage_pure(ordinary);
    part2_tier1_resume_frame(|calls|part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Visited {samples},calls),
        |response:Result<(),crate::DecodeError>,rest|match response {
            Err(error)=>Some((Ok((Err(error),context.image,preflight.1)),rest)),
            Ok(())=>part2_assembly_plane_after_visited_run(context,samples,Seq::new(part2_assembly_plane_count(context),|_:int|false),rest),
        },Err(crate::DecodeError::AllocationFailed),ordinary);
    part2_tier1_storage_eta(|calls|part2_assembly_plane_after_samples_run(context,samples,calls),ordinary);
    part2_assembly_plane_capacity_observed(context,Part2AssemblyPlaneStage::Samples,Ok(()));
    part2_tier1_resume_frame(|calls|part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Samples,calls),
        |response:Result<(),crate::DecodeError>,rest|match response {
            Err(error)=>Some((Ok((Err(error),context.image,preflight.1)),rest)),
            Ok(())=>part2_assembly_plane_after_samples_run(context,samples,rest),
        },Ok(()),ordinary);
}
pub(crate) proof fn part2_assembly_plane_publish_refused(context:Part2AssemblyPlaneContext,plane:Part1AssemblyPlane)
    requires part2_assembly_plane_preflight(context).0.is_ok(),
        {
            let ready=part2_assembly_plane_preflight(context).0.get_Ok_0();
            part1_collect_assembly_tiles((ready.0.1,ready.0.2,None,Seq::new(ready.1 as nat,|_:int|0i64),Seq::new(ready.1 as nat,|_:int|false)),
                context.tiles,context.component,ready.2)==(Ok(()),plane)
        },
        plane.2.is_some(),
        part2_tier1_storage_framed(|calls|part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Publish {plane},calls),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_assembly_plane_result(context,(Err(crate::DecodeError::AllocationFailed),context.image,part2_assembly_plane_preflight(context).1)),
{
    let preflight=part2_assembly_plane_preflight(context);
    let ready=preflight.0.get_Ok_0();
    let samples=Seq::new(ready.1 as nat,|_:int|0i64);let visited=Seq::new(ready.1 as nat,|_:int|false);
    let ordinary=part2_assembly_plane_finish(context,ready.0,preflight.1,(Ok(()),plane));
    let effect=Ok((Err(crate::DecodeError::AllocationFailed),context.image,preflight.1));
    part2_tier1_storage_pure(effect);
    part2_tier1_resume_frame(|calls|part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Publish {plane},calls),
        |response:Result<(),crate::DecodeError>,rest|Some((Ok(match response {
            Err(error)=>(Err(error),context.image,preflight.1),Ok(())=>ordinary,
        }),rest)),Err(crate::DecodeError::AllocationFailed),effect);
    part2_tier1_storage_eta(|calls|part2_assembly_plane_after_visited_run(context,samples,visited,calls),effect);
    part2_assembly_plane_capacity_observed(context,Part2AssemblyPlaneStage::Visited {samples},Ok(()));
    part2_tier1_resume_frame(|calls|part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Visited {samples},calls),
        |response:Result<(),crate::DecodeError>,rest|match response {
            Err(error)=>Some((Ok((Err(error),context.image,preflight.1)),rest)),
            Ok(())=>part2_assembly_plane_after_visited_run(context,samples,visited,rest),
        },Ok(()),effect);
    part2_tier1_storage_eta(|calls|part2_assembly_plane_after_samples_run(context,samples,calls),effect);
    part2_assembly_plane_capacity_observed(context,Part2AssemblyPlaneStage::Samples,Ok(()));
    part2_tier1_resume_frame(|calls|part2_assembly_plane_capacity_run(context,Part2AssemblyPlaneStage::Samples,calls),
        |response:Result<(),crate::DecodeError>,rest|match response {
            Err(error)=>Some((Ok((Err(error),context.image,preflight.1)),rest)),
            Ok(())=>part2_assembly_plane_after_samples_run(context,samples,rest),
        },Ok(()),effect);
}
#[verifier::opaque]
pub(crate) open spec fn part2_assembly_prefix_run(image:Part1DecodedImageModel,bytes:u64,size:Part1AssemblySize,tiles:Seq<Part1AssemblyTile>,
    extent:(u32,u32),selection:Part1AssemblySelection,maximum:u64,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1AssemblyState>
    decreases count,
{
    if count==0{Some((Ok((Ok(()),image,bytes)),calls))}else{
        part2_tier1_storage_bind(part2_assembly_prefix_run(image,bytes,size,tiles,extent,selection,maximum,(count-1) as nat,calls),
            |before:Part1AssemblyState,rest|if before.0.is_err(){Some((Ok(before),rest))}else{
                part2_assembly_plane_run(Part2AssemblyPlaneContext {image:before.1,bytes:before.2,size,tiles,component:(count-1) as u16,extent,selection,maximum},rest)
            })
    }
}
pub(crate) open spec fn part2_assembly_body_header(context:Part2AssemblyOwnerContext)
    ->Result<(Part1DecodedImageModel,(u32,u32),Part1AssemblySelection),crate::DecodeError> {
    let size=context.size;
    match context.selection {
        None=>match part1_image_checked_u32(size.2 as int+size.0) {
            Err(error)=>Err(error),Ok(x1)=>match part1_image_checked_u32(size.3 as int+size.1) {
                Err(error)=>Err(error),Ok(y1)=>Ok(((size.0,size.1,size.2,size.3,Seq::empty()),(x1,y1),None)),
            },
        },
        Some((region,discard))=>match part1_assembly_selected_header(region,discard) {
            Err(error)=>Err(error),Ok(header)=>Ok(((header.3,header.4,header.1,header.2,Seq::empty()),(0,0),Some((region,header.0)))),
        },
    }
}
pub(crate) open spec fn part2_assembly_body_run(context:Part2AssemblyOwnerContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1DecodedImageModel> {
    match part2_assembly_body_header(context) {
        Err(error)=>Some((Err(error),calls)),
        Ok((image,extent,selection))=>part2_tier1_storage_bind(
            part2_assembly_prefix_run(image,0,context.size,context.tiles,extent,selection,context.maximum,context.size.4 as nat,calls),
            |effect:Part1AssemblyState,rest|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(effect.1)},rest))),
    }
}
pub(crate) proof fn part2_assembly_prefix_normal(image:Part1DecodedImageModel,bytes:u64,size:Part1AssemblySize,tiles:Seq<Part1AssemblyTile>,
    extent:(u32,u32),selection:Part1AssemblySelection,maximum:u64,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_assembly_prefix_run(image,bytes,size,tiles,extent,selection,maximum,count,calls),
        Ok(part1_assembly_components_prefix(image,bytes,size,tiles,extent,selection,maximum,count))),
    decreases count,
{
    reveal_with_fuel(part2_assembly_prefix_run,1);reveal_with_fuel(part1_assembly_components_prefix,1);
    let before=if count==0{(Ok(()),image,bytes)}else{part1_assembly_components_prefix(image,bytes,size,tiles,extent,selection,maximum,(count-1) as nat)};
    let result=part1_assembly_components_prefix(image,bytes,size,tiles,extent,selection,maximum,count);
    if count==0{part2_tier1_storage_pure(Ok(result));}else{
        part2_assembly_prefix_normal(image,bytes,size,tiles,extent,selection,maximum,(count-1) as nat);
        if before.0.is_err(){part2_tier1_storage_pure(Ok(result));}else{
            let context=Part2AssemblyPlaneContext {image:before.1,bytes:before.2,size,tiles,component:(count-1) as u16,extent,selection,maximum};
            part2_assembly_plane_normal(context);
            part2_tier1_storage_eta(|calls|part2_assembly_plane_run(context,calls),Ok(result));
        }
        part2_tier1_storage_bind_frame(|calls|part2_assembly_prefix_run(image,bytes,size,tiles,extent,selection,maximum,(count-1) as nat,calls),
            |before:Part1AssemblyState,rest|if before.0.is_err(){Some((Ok(before),rest))}else{
                part2_assembly_plane_run(Part2AssemblyPlaneContext {image:before.1,bytes:before.2,size,tiles,component:(count-1) as u16,extent,selection,maximum},rest)
            },Ok(before),Ok(result));
    }
}
pub(crate) proof fn part2_assembly_prefix_step(image:Part1DecodedImageModel,bytes:u64,size:Part1AssemblySize,tiles:Seq<Part1AssemblyTile>,
    extent:(u32,u32),selection:Part1AssemblySelection,maximum:u64,index:nat,before:Part1AssemblyState,effect:Part1AssemblyState)
    requires part1_assembly_components_prefix(image,bytes,size,tiles,extent,selection,maximum,index)==before,before.0==Ok(()),
        part2_assembly_plane_result(Part2AssemblyPlaneContext {image:before.1,bytes:before.2,size,tiles,component:index as u16,extent,selection,maximum},effect),
    ensures part2_tier1_storage_framed(|calls|part2_assembly_prefix_run(image,bytes,size,tiles,extent,selection,maximum,index+1,calls),Ok(effect)),
{
    reveal_with_fuel(part2_assembly_prefix_run,1);
    part2_assembly_prefix_normal(image,bytes,size,tiles,extent,selection,maximum,index);
    let context=Part2AssemblyPlaneContext {image:before.1,bytes:before.2,size,tiles,component:index as u16,extent,selection,maximum};
    part2_tier1_storage_eta(|calls|part2_assembly_plane_run(context,calls),Ok(effect));
    part2_tier1_storage_bind_frame(|calls|part2_assembly_prefix_run(image,bytes,size,tiles,extent,selection,maximum,index,calls),
        |before:Part1AssemblyState,rest|if before.0.is_err(){Some((Ok(before),rest))}else{
            part2_assembly_plane_run(Part2AssemblyPlaneContext {image:before.1,bytes:before.2,size,tiles,component:index as u16,extent,selection,maximum},rest)
        },Ok(before),Ok(effect));
}
pub(crate) proof fn part2_assembly_prefix_error(image:Part1DecodedImageModel,bytes:u64,size:Part1AssemblySize,tiles:Seq<Part1AssemblyTile>,
    extent:(u32,u32),selection:Part1AssemblySelection,maximum:u64,from:nat,to:nat,effect:Part1AssemblyState)
    requires from<=to,effect.0.is_err(),
        part2_tier1_storage_framed(|calls|part2_assembly_prefix_run(image,bytes,size,tiles,extent,selection,maximum,from,calls),Ok(effect)),
    ensures part2_tier1_storage_framed(|calls|part2_assembly_prefix_run(image,bytes,size,tiles,extent,selection,maximum,to,calls),Ok(effect)),
    decreases to-from,
{
    if from<to{
        reveal_with_fuel(part2_assembly_prefix_run,1);
        part2_assembly_prefix_error(image,bytes,size,tiles,extent,selection,maximum,from,(to-1) as nat,effect);
        part2_tier1_storage_pure(Ok(effect));
        part2_tier1_storage_bind_frame(|calls|part2_assembly_prefix_run(image,bytes,size,tiles,extent,selection,maximum,(to-1) as nat,calls),
            |before:Part1AssemblyState,rest|if before.0.is_err(){Some((Ok(before),rest))}else{
                part2_assembly_plane_run(Part2AssemblyPlaneContext {image:before.1,bytes:before.2,size,tiles,component:(to-1) as u16,extent,selection,maximum},rest)
            },Ok(effect),Ok(effect));
    }
}
pub(crate) proof fn part2_assembly_body_normal(context:Part2AssemblyOwnerContext)
    ensures part2_tier1_storage_framed(|calls|part2_assembly_body_run(context,calls),part2_assemble_prepared(context.size,context.tiles,context.selection,context.maximum)),
{
    let result=part2_assemble_prepared(context.size,context.tiles,context.selection,context.maximum);
    match part2_assembly_body_header(context) {
        Err(_)=>{part2_tier1_storage_pure(result);},
        Ok((image,extent,selection))=>{
            let effect=part1_assembly_components_prefix(image,0,context.size,context.tiles,extent,selection,context.maximum,context.size.4 as nat);
            part2_assembly_prefix_normal(image,0,context.size,context.tiles,extent,selection,context.maximum,context.size.4 as nat);
            part2_tier1_storage_pure(result);
            part2_tier1_storage_bind_frame(
                |calls|part2_assembly_prefix_run(image,0,context.size,context.tiles,extent,selection,context.maximum,context.size.4 as nat,calls),
                |effect:Part1AssemblyState,rest|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(effect.1)},rest)),Ok(effect),result);
        },
    }
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
            |_:(),rest|part2_assembly_body_run(context,rest)),
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
        part2_assembly_body_normal(context);
        part2_tier1_storage_eta(|calls|part2_assembly_body_run(context,calls),result);
        part2_tier1_storage_bind_frame(|calls|part2_assembly_owner_run(context,calls),
            |_:(),rest|part2_assembly_body_run(context,rest),Ok(()),result);
    }
}
pub(crate) proof fn part2_assembly_storage_refused(context:Part2AssemblyOwnerContext,response:Result<(),crate::DecodeError>)
    requires part2_assembly_owner_admit(context)==Ok(()),response==Err(crate::DecodeError::AllocationFailed),
        part2_tier1_storage_framed(|calls|part2_assembly_owner_run(context,calls),response),
    ensures part2_assembly_storage_result(context,Err(crate::DecodeError::AllocationFailed)),
{
    part2_tier1_storage_bind_frame(|calls|part2_assembly_owner_run(context,calls),
        |_:(),rest|part2_assembly_body_run(context,rest),response,Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_assembly_storage_plane_error(context:Part2AssemblyOwnerContext,index:nat,before:Part1AssemblyState,effect:Part1AssemblyState)
    requires index<context.size.4,before.0==Ok(()),effect.0.is_err(),part2_assembly_body_header(context).is_ok(),
        {
            let header=part2_assembly_body_header(context).get_Ok_0();
            part1_assembly_components_prefix(header.0,0,context.size,context.tiles,header.1,header.2,context.maximum,index)==before
            && part2_assembly_plane_result(Part2AssemblyPlaneContext {image:before.1,bytes:before.2,size:context.size,tiles:context.tiles,component:index as u16,
                extent:header.1,selection:header.2,maximum:context.maximum},effect)
        },
    ensures part2_assembly_storage_result(context,Err(effect.0.get_Err_0())),
{
    let header=part2_assembly_body_header(context).get_Ok_0();
    let error=effect.0.get_Err_0();
    part2_assembly_prefix_step(header.0,0,context.size,context.tiles,header.1,header.2,context.maximum,index,before,effect);
    part2_assembly_prefix_error(header.0,0,context.size,context.tiles,header.1,header.2,context.maximum,index+1,context.size.4 as nat,effect);
    part2_tier1_storage_pure(Err::<Part1DecodedImageModel,crate::DecodeError>(error));
    part2_tier1_storage_bind_frame(
        |calls|part2_assembly_prefix_run(header.0,0,context.size,context.tiles,header.1,header.2,context.maximum,context.size.4 as nat,calls),
        |effect:Part1AssemblyState,rest|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(effect.1)},rest)),Ok(effect),Err(error));
    part2_tier1_storage_eta(|calls|part2_assembly_body_run(context,calls),Err(error));
    part2_assembly_owner_observed(context,Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_assembly_owner_run(context,calls),
        |_:(),rest|part2_assembly_body_run(context,rest),Ok(()),Err(error));
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
