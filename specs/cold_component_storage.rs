//! Fresh component-plan and subband descriptor owners, before later precinct storage.
use super::*;
verus! {
pub enum Part2ComponentCapacityContext {
    Components {size:crate::codestream::ImageSize,style:crate::codestream::CodingStyle,styles:crate::codestream::ComponentCodingStyles,
        quantizations:(u16,Seq<crate::codestream::Quantization>),roi:crate::codestream::RoiShifts,selection:(u16,u8),policy:(bool,u8,bool,bool)},
    Subbands {size:crate::codestream::ImageSize,style:crate::codestream::CodingStyle,quantization:Part2Quantization,component:u16,tile:Option<u16>,roi:u8},
}
pub(crate) open spec fn part2_component_capacity_count(context:Part2ComponentCapacityContext)->usize {
    match context {
        Part2ComponentCapacityContext::Components {size,..}=>size.components as usize,
        Part2ComponentCapacityContext::Subbands {style,..}=>{
            let selector=crate::codestream::decomposition_selector_view(style);
            part2_subband_count(selector.0,selector.1) as usize
        },
    }
}
pub(crate) open spec fn part2_component_capacity_run(context:Part2ComponentCapacityContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_component_capacity_count(context);
    if count==0 {Some((Ok(()),events))}else if events.len()==0 {None}else{
        match events[0] {
            Part2JpipSnapshotEvent::ComponentCapacity {context:actual,elements,succeeded}=>
                if actual!=context || elements!=count {None}else{Some((if succeeded {Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
            _=>None,
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_component_capacity_result(context:Part2ComponentCapacityContext,result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_component_capacity_run(context,events),result)
}
pub(crate) proof fn part2_component_capacity_observed(context:Part2ComponentCapacityContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_component_capacity_count(context)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_component_capacity_result(context,result),
{
    reveal(part2_component_capacity_result);
    let count=part2_component_capacity_count(context);
    let calls=if count==0 {Seq::empty()}else{seq![Part2JpipSnapshotEvent::ComponentCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_component_capacity_run(context,calls+tail)==Some((result,tail)) by{
        if count==0 {assert(calls+tail =~= tail);}else{assert((calls+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_component_capacity_run(context,events),calls,result));
}
pub(crate) open spec fn part2_subbands_admit(size:&crate::codestream::ImageSize,component:u16,tile:Option<u16>)->Result<(),crate::DecodeError> {
    match part1_image_size_component(crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),component) {
        Err(error)=>Err(error),Ok(_)=>match part2_component_coordinate_bounds(crate::codestream::selection_geometry_view(size),
            crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),component,tile) {
            Err(error)=>Err(error),Ok(_)=>Ok(()),
        },
    }
}
pub(crate) open spec fn part2_subbands_run(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    quantization:&crate::codestream::Quantization,component:u16,tile:Option<u16>,roi:u8,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<crate::decode::SubbandGeometry>> {
    match part2_subbands_admit(size,component,tile) {
        Err(error)=>Some((Err(error),events)),
        Ok(())=>part2_jpip_snapshot_bind(part2_component_capacity_run(Part2ComponentCapacityContext::Subbands {
            size:*size,style,quantization:crate::codestream::quantization_view(quantization),component,tile,roi},events),
            |_:(),rest|Some((part2_component_subbands(size,style,quantization,component,tile,roi),rest))),
    }
}
pub closed spec fn part1_subbands_cold_result(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    quantization:&crate::codestream::Quantization,component:u16,tile:Option<u16>,roi:u8,result:Result<Seq<crate::decode::SubbandGeometry>,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_subbands_run(size,style,quantization,component,tile,roi,events),result)
}
pub(crate) proof fn part2_subbands_frames(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    quantization:&crate::codestream::Quantization,component:u16,tile:Option<u16>,roi:u8,result:Result<Seq<crate::decode::SubbandGeometry>,crate::DecodeError>)
    requires part1_subbands_cold_result(size,style,quantization,component,tile,roi,result),
    ensures part2_cold_framed(|events|part2_subbands_run(size,style,quantization,component,tile,roi,events),result),
{
    part2_decode_eta(|events|part2_subbands_run(size,style,quantization,component,tile,roi,events),result);
}
pub(crate) proof fn part2_subbands_normal(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    quantization:&crate::codestream::Quantization,component:u16,tile:Option<u16>,roi:u8)
    ensures part1_subbands_cold_result(size,style,quantization,component,tile,roi,part2_component_subbands(size,style,quantization,component,tile,roi)),
{
    reveal(part2_component_capacity_result);
    let result=part2_component_subbands(size,style,quantization,component,tile,roi);
    match part2_subbands_admit(size,component,tile) {
        Err(_)=>{part2_cold_pure::<Seq<crate::decode::SubbandGeometry>>(result);},
        Ok(())=>{
            let context=Part2ComponentCapacityContext::Subbands {size:*size,style,quantization:crate::codestream::quantization_view(quantization),component,tile,roi};
            part2_component_capacity_observed(context,Ok(()));part2_cold_pure(result);
            part2_cold_bind(|events|part2_component_capacity_run(context,events),|_:(),rest|Some((result,rest)),Ok(()),result);
        },
    }
}
pub(crate) proof fn part2_subbands_refused(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    quantization:&crate::codestream::Quantization,component:u16,tile:Option<u16>,roi:u8)
    requires part2_subbands_admit(size,component,tile)==Ok(()),
        part2_component_capacity_result(Part2ComponentCapacityContext::Subbands {size:*size,style,quantization:crate::codestream::quantization_view(quantization),component,tile,roi},Err(crate::DecodeError::AllocationFailed)),
    ensures part1_subbands_cold_result(size,style,quantization,component,tile,roi,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_component_capacity_result);
    part2_cold_bind(|events|part2_component_capacity_run(Part2ComponentCapacityContext::Subbands {size:*size,style,quantization:crate::codestream::quantization_view(quantization),component,tile,roi},events),
        |_:(),rest|Some((part2_component_subbands(size,style,quantization,component,tile,roi),rest)),Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) open spec fn part2_component_subbands_prelude(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),force:bool)
    ->Result<(crate::codestream::CodingStyle,crate::codestream::Quantization,u8),crate::DecodeError> {
    match crate::codestream::component_coding_style_result(styles,component) {
        Err(error)=>Err(error),Ok(style)=>if selection.1>style.decomposition_levels {
            Err(crate::DecodeError::InvalidSelection {reason:crate::SelectionError::ReductionTooLarge})
        }else{
            let output=(style.decomposition_levels-selection.1) as u8;
            match part2_component_quantization_owned(quantizations,component) {
                Err(error)=>Err(error),Ok(quantization)=>match crate::codestream::coding_style_tier1_result(style) {
                    Err(error)=>Err(error),Ok(_)=>match part2_tile_component_bounds(crate::codestream::selection_geometry_view(size),
                        crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),selection.0,component) {
                        Err(error)=>Err(error),Ok(bounds)=>match part2_resolution_geometry(crate::codestream::selection_geometry_view(size),
                            crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),crate::decode::resolution_geometry_style(style),
                            component,output,Some(selection.0)) {
                            Err(error)=>Err(error),Ok(_)=>{
                                let selector=crate::codestream::decomposition_selector_view(style);
                                match part2_resolution_downsampling(selector.0,selector.1,output) {
                                    Err(error)=>Err(error),Ok(scale)=>match part1_image_size_component(crate::codestream::image_size_component_count(size),
                                        crate::codestream::image_size_component_infos(size),component) {
                                        Err(error)=>Err(error),Ok(info)=>{
                                            let size_view=crate::codestream::selection_geometry_view(size);
                                            match part2_selection_ceil(size_view.2,info.x_subsampling as u32) {
                                                Err(error)=>Err(error),Ok(origin_x)=>match part2_selection_ceil(size_view.3,info.y_subsampling as u32) {
                                                    Err(error)=>Err(error),Ok(origin_y)=>match part2_selection_ceil(bounds.x0,scale.0) {
                                                        Err(error)=>Err(error),Ok(x0)=>match part2_selection_ceil(origin_x,scale.0) {
                                                            Err(error)=>Err(error),Ok(ix0)=>match part1_image_checked_u32(x0 as int-ix0 as int) {
                                                                Err(error)=>Err(error),Ok(_)=>match part2_selection_ceil(bounds.y0,scale.1) {
                                                                    Err(error)=>Err(error),Ok(y0)=>match part2_selection_ceil(origin_y,scale.1) {
                                                                        Err(error)=>Err(error),Ok(iy0)=>match part1_image_checked_u32(y0 as int-iy0 as int) {
                                                                            Err(error)=>Err(error),Ok(_)=>match part2_roi_shift(crate::codestream::roi_shifts_view(roi),component) {
                                                                                Err(error)=>Err(error),Ok(shift)=>Ok((style,quantization,shift)),
                                                                            },
                                                                        },
                                                                    },
                                                                },
                                                            },
                                                        },
                                                    },
                                                },
                                            }
                                        },
                                    },
                                }
                            },
                        },
                    },
                },
            }
        },
    }
}
pub(crate) open spec fn part2_component_metadata_run(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),force:bool,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ComponentPlanMetadata> {
    match part2_component_subbands_prelude(size,styles,quantizations,roi,component,selection,force) {
        Err(error)=>Some((Err(error),events)),
        Ok((style,quantization,shift))=>part2_jpip_snapshot_bind(part2_subbands_run(size,style,&quantization,component,Some(selection.0),shift,events),
            |_:Seq<crate::decode::SubbandGeometry>,rest|Some((part2_component_plan_metadata_owned(size,styles,quantizations,roi,component,selection,force),rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_component_metadata_result(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),force:bool,
    result:Result<Part2ComponentPlanMetadata,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_component_metadata_run(size,styles,quantizations,roi,component,selection,force,events),result)
}
pub(crate) proof fn part2_component_metadata_normal(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),force:bool)
    ensures part2_component_metadata_result(size,styles,quantizations,roi,component,selection,force,
        part2_component_plan_metadata_owned(size,styles,quantizations,roi,component,selection,force)),
{
    reveal(part2_component_metadata_result);
    let result=part2_component_plan_metadata_owned(size,styles,quantizations,roi,component,selection,force);
    match part2_component_subbands_prelude(size,styles,quantizations,roi,component,selection,force) {
        Err(_)=>{part2_cold_pure::<Part2ComponentPlanMetadata>(result);},
        Ok((style,quantization,shift))=>{
            part2_subbands_normal(size,style,&quantization,component,Some(selection.0),shift);
            let bands=part2_component_subbands(size,style,&quantization,component,Some(selection.0),shift);
            part2_subbands_frames(size,style,&quantization,component,Some(selection.0),shift,bands);
            if bands.is_ok(){part2_cold_pure(result);}
            part2_cold_bind(|events|part2_subbands_run(size,style,&quantization,component,Some(selection.0),shift,events),
                |_:Seq<crate::decode::SubbandGeometry>,rest|Some((result,rest)),bands,result);
        },
    }
}
pub(crate) proof fn part2_component_metadata_subbands_error(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),force:bool,
    style:crate::codestream::CodingStyle,quantization:crate::codestream::Quantization,shift:u8,error:crate::DecodeError)
    requires part2_component_subbands_prelude(size,styles,quantizations,roi,component,selection,force)==Ok((style,quantization,shift)),
        part1_subbands_cold_result(size,style,&quantization,component,Some(selection.0),shift,Err(error)),
    ensures part2_component_metadata_result(size,styles,quantizations,roi,component,selection,force,Err(error)),
{
    reveal(part2_component_metadata_result);
    part2_subbands_frames(size,style,&quantization,component,Some(selection.0),shift,Err(error));
    part2_cold_bind(|events|part2_subbands_run(size,style,&quantization,component,Some(selection.0),shift,events),
        |_:Seq<crate::decode::SubbandGeometry>,rest|Some((part2_component_plan_metadata_owned(size,styles,quantizations,roi,component,selection,force),rest)),Err(error),Err(error));
}
pub(crate) open spec fn part2_planned_component_run(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),policy:(bool,u8,bool,bool),
    precincts:Seq<Part1PacketPrecinctState>,total:u64,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedComponent> {
    part2_jpip_snapshot_bind(part2_component_metadata_run(size,styles,quantizations,roi,component,selection,policy.2,events),
        |meta:Part2ComponentPlanMetadata,rest|part2_resolution_plan_run(size,component,selection.0,meta,policy,limits,0,
            Part2ComponentPlanBuffers {precincts,placements:Seq::empty(),planned_code_blocks:total},rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_planned_component_result(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),policy:(bool,u8,bool,bool),
    precincts:Seq<Part1PacketPrecinctState>,total:u64,limits:&crate::ResourceLimits,result:Result<Part2PlannedComponent,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_planned_component_run(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,events),result)
}
pub(crate) proof fn part2_planned_component_frames(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),policy:(bool,u8,bool,bool),
    precincts:Seq<Part1PacketPrecinctState>,total:u64,limits:&crate::ResourceLimits,result:Result<Part2PlannedComponent,crate::DecodeError>)
    requires part2_planned_component_result(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,result),
    ensures part2_cold_framed(|events|part2_planned_component_run(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedComponent>|
            (forall|events| #[trigger] other(events)==part2_planned_component_run(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,events))
                ==> #[trigger] part2_cold_framed(other,result),
{
    reveal(part2_planned_component_result);
    part2_decode_eta(|events|part2_planned_component_run(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,events),result);
}
pub(crate) proof fn part2_planned_component_normal(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),policy:(bool,u8,bool,bool),
    precincts:Seq<Part1PacketPrecinctState>,total:u64,limits:&crate::ResourceLimits)
    ensures part2_planned_component_result(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,
        part2_planned_component_owned(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits)),
{
    reveal(part2_planned_component_result);reveal(part2_component_metadata_result);
    part2_component_metadata_normal(size,styles,quantizations,roi,component,selection,policy.2);
    let meta=part2_component_plan_metadata_owned(size,styles,quantizations,roi,component,selection,policy.2);
    let result=part2_planned_component_owned(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits);
    if let Ok(value)=meta {
        let before=Part2ComponentPlanBuffers {precincts,placements:Seq::empty(),planned_code_blocks:total};
        part2_resolution_plan_normal(size,component,selection.0,value,policy,limits,0,before);
        part2_decode_eta(|events|part2_resolution_plan_run(size,component,selection.0,value,policy,limits,0,before,events),result);
    }
    part2_cold_bind(|events|part2_component_metadata_run(size,styles,quantizations,roi,component,selection,policy.2,events),
        |meta:Part2ComponentPlanMetadata,rest|part2_resolution_plan_run(size,component,selection.0,meta,policy,limits,0,
            Part2ComponentPlanBuffers {precincts,placements:Seq::empty(),planned_code_blocks:total},rest),meta,result);
}
pub(crate) proof fn part2_planned_component_metadata_error(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),policy:(bool,u8,bool,bool),
    precincts:Seq<Part1PacketPrecinctState>,total:u64,limits:&crate::ResourceLimits,error:crate::DecodeError)
    requires part2_component_metadata_result(size,styles,quantizations,roi,component,selection,policy.2,Err(error)),
    ensures part2_planned_component_result(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,Err(error)),
{
    reveal(part2_planned_component_result);reveal(part2_component_metadata_result);
    part2_cold_bind(|events|part2_component_metadata_run(size,styles,quantizations,roi,component,selection,policy.2,events),
        |meta:Part2ComponentPlanMetadata,rest|part2_resolution_plan_run(size,component,selection.0,meta,policy,limits,0,
            Part2ComponentPlanBuffers {precincts,placements:Seq::empty(),planned_code_blocks:total},rest),Err(error),Err(error));
}
}
