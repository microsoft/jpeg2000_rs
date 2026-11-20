//! Ordered actual component-plan owners and subband construction.
use super::*;
verus! {
pub(crate) open spec fn part2_component_owner_context(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool))->Part2ComponentCapacityContext {
    Part2ComponentCapacityContext::Components {size:*size,style,styles:*styles,quantizations,roi:*roi,selection,policy}
}
#[verifier::opaque]
pub(crate) open spec fn part2_component_plan_fold(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,grid:Part1PacketGrid,component:u16,before:Part2TilePlanBuffers,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ProgressionTilePlan>
    decreases if component<crate::codestream::image_size_component_count(size){(crate::codestream::image_size_component_count(size) as int-component as int) as nat}else{0nat},
{
    if component>=crate::codestream::image_size_component_count(size) {
        Some((Ok(Part2ProgressionTilePlan {tile:selection.0,coding_style:style,coding_styles:*styles,grid,precincts:before.precincts,components:before.components}),events))
    }else{
        part2_jpip_snapshot_bind(part2_planned_component_run(size,styles,quantizations,roi,component,selection,policy,before.precincts,before.planned_code_blocks,limits,events),
            |planned:Part2PlannedComponent,rest|part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,(component+1) as u16,
                Part2TilePlanBuffers {precincts:planned.precincts,components:before.components.push(planned.component),planned_code_blocks:planned.planned_code_blocks},rest))
    }
}
pub(crate) proof fn part2_component_plan_fold_normal(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,grid:Part1PacketGrid,component:u16,before:Part2TilePlanBuffers)
    ensures part2_cold_framed(|events|part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,component,before,events),
        part2_tile_plan_components(size,style,styles,quantizations,roi,selection,policy,limits,grid,component,before)),
    decreases if component<crate::codestream::image_size_component_count(size){(crate::codestream::image_size_component_count(size) as int-component as int) as nat}else{0nat},
{
    reveal_with_fuel(part2_component_plan_fold,1);reveal_with_fuel(part2_tile_plan_components,1);reveal(part2_planned_component_result);
    let result=part2_tile_plan_components(size,style,styles,quantizations,roi,selection,policy,limits,grid,component,before);
    if component>=crate::codestream::image_size_component_count(size){part2_cold_pure::<Part2ProgressionTilePlan>(result);}else{
        part2_planned_component_normal(size,styles,quantizations,roi,component,selection,policy,before.precincts,before.planned_code_blocks,limits);
        let planned=part2_planned_component_owned(size,styles,quantizations,roi,component,selection,policy,before.precincts,before.planned_code_blocks,limits);
        if let Ok(value)=planned {
            let after=Part2TilePlanBuffers {precincts:value.precincts,components:before.components.push(value.component),planned_code_blocks:value.planned_code_blocks};
            part2_component_plan_fold_normal(size,style,styles,quantizations,roi,selection,policy,limits,grid,(component+1) as u16,after);
            part2_decode_eta(|events|part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,(component+1) as u16,after,events),
                part2_tile_plan_components(size,style,styles,quantizations,roi,selection,policy,limits,grid,(component+1) as u16,after));
        }
        part2_cold_bind(|events|part2_planned_component_run(size,styles,quantizations,roi,component,selection,policy,before.precincts,before.planned_code_blocks,limits,events),
            |planned:Part2PlannedComponent,rest|part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,(component+1) as u16,
                Part2TilePlanBuffers {precincts:planned.precincts,components:before.components.push(planned.component),planned_code_blocks:planned.planned_code_blocks},rest),planned,result);
    }
}
pub(crate) open spec fn part2_plan_after_grid_run(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,grid:Part1PacketGrid,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ProgressionTilePlan> {
    part2_jpip_snapshot_bind(part2_component_capacity_run(part2_component_owner_context(size,style,styles,quantizations,roi,selection,policy),events),
        |_:(),rest|part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,0,
            Part2TilePlanBuffers {precincts:Seq::empty(),components:Seq::empty(),planned_code_blocks:0},rest))
}
pub(crate) proof fn part2_plan_after_grid_normal(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,grid:Part1PacketGrid)
    requires part2_selection_tile_bounds(crate::codestream::selection_geometry_view(size),selection.0).is_ok(),
        part2_spatial_packet_grid_from_components(size,styles,style.layers,limits,Some(selection.0),selection.1)==Ok(grid),
    ensures part2_cold_framed(|events|part2_plan_after_grid_run(size,style,styles,quantizations,roi,selection,policy,limits,grid,events),
        part2_progression_tile_plan_owned(size,style,styles,quantizations,roi,selection,policy,limits)),
{
    reveal(part2_component_capacity_result);
    let context=part2_component_owner_context(size,style,styles,quantizations,roi,selection,policy);
    let initial=Part2TilePlanBuffers {precincts:Seq::empty(),components:Seq::empty(),planned_code_blocks:0};
    let result=part2_progression_tile_plan_owned(size,style,styles,quantizations,roi,selection,policy,limits);
    part2_component_capacity_observed(context,Ok(()));
    part2_component_plan_fold_normal(size,style,styles,quantizations,roi,selection,policy,limits,grid,0,initial);
    part2_decode_eta(|events|part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,0,initial,events),result);
    part2_cold_bind(|events|part2_component_capacity_run(context,events),
        |_:(),rest|part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,0,initial,rest),Ok(()),result);
}
pub(crate) proof fn part2_plan_component_owner_refused(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,grid:Part1PacketGrid)
    requires part2_selection_tile_bounds(crate::codestream::selection_geometry_view(size),selection.0).is_ok(),
        part2_spatial_derived_grid_result(size,styles,style.layers,limits,Some(selection.0),selection.1,Ok(grid)),
        part2_component_capacity_result(part2_component_owner_context(size,style,styles,quantizations,roi,selection,policy),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_grid_plan_result(size,style,styles,quantizations,roi,selection,policy,limits,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_grid_plan_result);reveal(part2_grid_plan_run);reveal(part2_spatial_derived_grid_result);reveal(part2_component_capacity_result);
    let context=part2_component_owner_context(size,style,styles,quantizations,roi,selection,policy);
    let initial=Part2TilePlanBuffers {precincts:Seq::empty(),components:Seq::empty(),planned_code_blocks:0};
    part2_cold_bind(|events|part2_component_capacity_run(context,events),
        |_:(),rest|part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,0,initial,rest),Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
    part2_decode_eta(|events|part2_plan_after_grid_run(size,style,styles,quantizations,roi,selection,policy,limits,grid,events),Err(crate::DecodeError::AllocationFailed));
    part2_cold_bind(|events|part2_spatial_derived_grid_run(size,styles,style.layers,limits,Some(selection.0),selection.1,events),
        |grid:Part1PacketGrid,rest|part2_plan_after_grid_run(size,style,styles,quantizations,roi,selection,policy,limits,grid,rest),Ok(grid),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_plan_component_prefix(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,grid:Part1PacketGrid)->(prefix:Seq<Part2JpipSnapshotEvent>)
    requires part2_selection_tile_bounds(crate::codestream::selection_geometry_view(size),selection.0).is_ok(),
        part2_spatial_derived_grid_result(size,styles,style.layers,limits,Some(selection.0),selection.1,Ok(grid)),
        part2_component_capacity_result(part2_component_owner_context(size,style,styles,quantizations,roi,selection,policy),Ok(())),
    ensures forall|events| #[trigger] part2_grid_plan_run(size,style,styles,quantizations,roi,selection,policy,limits,prefix+events)
        ==part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,0,
            Part2TilePlanBuffers {precincts:Seq::empty(),components:Seq::empty(),planned_code_blocks:0},events),
{
    reveal(part2_grid_plan_run);reveal(part2_spatial_derived_grid_result);reveal(part2_component_capacity_result);
    let first=|events|part2_spatial_derived_grid_run(size,styles,style.layers,limits,Some(selection.0),selection.1,events);
    let second=|events|part2_component_capacity_run(part2_component_owner_context(size,style,styles,quantizations,roi,selection,policy),events);
    let before=part2_cold_witness(first,Ok(grid));let after=part2_cold_witness(second,Ok(()));
    assert forall|events:Seq<Part2JpipSnapshotEvent>|
        part2_grid_plan_run(size,style,styles,quantizations,roi,selection,policy,limits,(before+after)+events)
            ==part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,0,
                Part2TilePlanBuffers {precincts:Seq::empty(),components:Seq::empty(),planned_code_blocks:0},events) by{
        assert((before+after)+events =~= before+(after+events));
        part2_cold_prefix_at(first,before,Ok(grid),after+events);part2_cold_prefix_at(second,after,Ok(()),events);
    }
    before+after
}
pub(crate) proof fn part2_component_fold_step(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,grid:Part1PacketGrid,component:u16,before:Part2TilePlanBuffers)
    requires component<crate::codestream::image_size_component_count(size),
    ensures forall|events| #[trigger] part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,component,before,events)
        ==part2_jpip_snapshot_bind(part2_planned_component_run(size,styles,quantizations,roi,component,selection,policy,before.precincts,before.planned_code_blocks,limits,events),
            |planned:Part2PlannedComponent,rest|part2_component_plan_fold(size,style,styles,quantizations,roi,selection,policy,limits,grid,(component+1) as u16,
                Part2TilePlanBuffers {precincts:planned.precincts,components:before.components.push(planned.component),planned_code_blocks:planned.planned_code_blocks},rest)),
{
    reveal_with_fuel(part2_component_plan_fold,1);
}
}
