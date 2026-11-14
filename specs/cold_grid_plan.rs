//! Source-derived planning with grid construction preceding packet preparation.
use super::*;
verus! {
pub(crate) open spec fn part2_grid_plan_run(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ProgressionTilePlan> {
    match part2_selection_tile_bounds(crate::codestream::selection_geometry_view(size),selection.0) {
        Err(error)=>Some((Err(error),events)),
        Ok(_)=>part2_jpip_snapshot_bind(part2_derived_grid_run(size,styles,style.layers,limits,Some(selection.0),selection.1,events),
            |_:Part1PacketGrid,rest|Some((part2_progression_tile_plan_owned(size,style,styles,quantizations,roi,selection,policy,limits),rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_grid_plan_result(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,result:Result<Part2ProgressionTilePlan,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_grid_plan_run(size,style,styles,quantizations,roi,selection,policy,limits,events),result)
}
pub(crate) proof fn part2_grid_plan_frames(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,result:Result<Part2ProgressionTilePlan,crate::DecodeError>)
    requires part2_grid_plan_result(size,style,styles,quantizations,roi,selection,policy,limits,result),
    ensures part2_cold_framed(|events|part2_grid_plan_run(size,style,styles,quantizations,roi,selection,policy,limits,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ProgressionTilePlan>|
            (forall|events| #[trigger] other(events)==part2_grid_plan_run(size,style,styles,quantizations,roi,selection,policy,limits,events))
                ==> #[trigger] part2_cold_framed(other,result),
{
    reveal(part2_grid_plan_result);
    part2_decode_eta(|events|part2_grid_plan_run(size,style,styles,quantizations,roi,selection,policy,limits,events),result);
}
pub closed spec fn part1_progression_plan_cold_result(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:&crate::codestream::ComponentQuantizations,roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,result:Result<Part2ProgressionTilePlan,crate::DecodeError>)->bool {
    part2_grid_plan_result(size,style,styles,crate::codestream::quantization_owner_view(quantizations),roi,selection,policy,limits,result)
}
pub(crate) proof fn part2_grid_plan_public_equivalent(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:&crate::codestream::ComponentQuantizations,roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits)
    ensures forall|result|part1_progression_plan_cold_result(size,style,styles,quantizations,roi,selection,policy,limits,result)
        ==part2_grid_plan_result(size,style,styles,crate::codestream::quantization_owner_view(quantizations),roi,selection,policy,limits,result),
{}
pub(crate) proof fn part2_grid_plan_normal(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits)
    ensures part2_grid_plan_result(size,style,styles,quantizations,roi,selection,policy,limits,
        part2_progression_tile_plan_owned(size,style,styles,quantizations,roi,selection,policy,limits)),
{
    reveal(part2_grid_plan_result);reveal(part2_derived_grid_result);
    let result=part2_progression_tile_plan_owned(size,style,styles,quantizations,roi,selection,policy,limits);
    match part2_selection_tile_bounds(crate::codestream::selection_geometry_view(size),selection.0) {
        Err(_)=>{part2_cold_pure::<Part2ProgressionTilePlan>(result);},
        Ok(_)=>{
            part2_derived_grid_normal(size,styles,style.layers,limits,Some(selection.0),selection.1);
            let grid=part2_packet_grid_from_components(size,styles,style.layers,limits,Some(selection.0),selection.1);
            if grid.is_ok(){part2_cold_pure(result);}
            part2_cold_bind(|events|part2_derived_grid_run(size,styles,style.layers,limits,Some(selection.0),selection.1,events),
                |_:Part1PacketGrid,rest|Some((result,rest)),grid,result);
        },
    }
}
pub(crate) proof fn part2_grid_plan_error(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    styles:&crate::codestream::ComponentCodingStyles,quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,
    selection:(u16,u8),policy:(bool,u8,bool),limits:&crate::ResourceLimits,error:crate::DecodeError)
    requires part2_selection_tile_bounds(crate::codestream::selection_geometry_view(size),selection.0).is_ok(),
        part2_derived_grid_result(size,styles,style.layers,limits,Some(selection.0),selection.1,Err(error)),
    ensures part2_grid_plan_result(size,style,styles,quantizations,roi,selection,policy,limits,Err(error)),
{
    reveal(part2_grid_plan_result);reveal(part2_derived_grid_result);
    part2_cold_bind(|events|part2_derived_grid_run(size,styles,style.layers,limits,Some(selection.0),selection.1,events),
        |_:Part1PacketGrid,rest|Some((part2_progression_tile_plan_owned(size,style,styles,quantizations,roi,selection,policy,limits),rest)),Err(error),Err(error));
}
pub(crate) open spec fn part2_tile_after_grid_plan(size:&crate::codestream::ImageSize,parts:Seq<Part2OwnedTilePart>,metadata:Part2TileDecodeMetadata,
    discard:Option<u8>,limits:&crate::ResourceLimits,prepared:Seq<Part1AssemblyTile>,initial:(u64,u64,u64),work:u64,
    plan:Part2ProgressionTilePlan,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2DecodedLayoutTile> {
    let maximum=match discard {None=>None,Some(_)=>Some(metadata.resolution_counts)};
    match part2_planned_tile_accounting(plan,maximum,initial,limits) {
        Err(error)=>Some((Err(error),events)),
        Ok(counters)=>part2_jpip_snapshot_bind(part2_planned_decode_run(plan,parts,metadata.first,size,metadata.standard,maximum,limits,prepared,work,events),
            |decoded:Part2DecodedTileComponents,rest|Some((Ok(Part2DecodedLayoutTile {prepared:decoded.prepared,counters,mct_work:decoded.mct_work}),rest))),
    }
}
pub(crate) proof fn part2_tile_after_grid_plan_normal(size:&crate::codestream::ImageSize,tile:u16,parts:Seq<Part2OwnedTilePart>,caps:Option<(u32,Seq<u16>)>,
    discard:Option<u8>,limits:&crate::ResourceLimits,prepared:Seq<Part1AssemblyTile>,initial:(u64,u64,u64),work:u64,metadata:Part2TileDecodeMetadata,plan:Part2ProgressionTilePlan)
    requires part2_tile_decode_metadata_owned(parts,crate::codestream::image_size_component_count(size),discard)==Ok(metadata),
        part2_progression_tile_plan_owned(size,metadata.first.coding_style,&metadata.first.component_coding_styles,metadata.first.component_quantizations,&metadata.first.roi_shifts,
            (tile,match discard {None=>0u8,Some(level)=>level}),(part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps)),limits)==Ok(plan),
    ensures part2_cold_framed(|events|part2_tile_after_grid_plan(size,parts,metadata,discard,limits,prepared,initial,work,plan,events),
        part2_decode_tile_parts_owned(size,tile,parts,caps,discard,limits,prepared,initial,work)),
{
    reveal(part2_planned_decode_result);
    let result=part2_decode_tile_parts_owned(size,tile,parts,caps,discard,limits,prepared,initial,work);
    let maximum=match discard {None=>None,Some(_)=>Some(metadata.resolution_counts)};
    match part2_planned_tile_accounting(plan,maximum,initial,limits) {
        Err(_)=>{part2_cold_pure::<Part2DecodedLayoutTile>(result);},
        Ok(counters)=>{
            part2_planned_decode_normal(plan,parts,metadata.first,size,metadata.standard,maximum,limits,prepared,work);
            let decoded=part2_decode_planned_tile_components_owned(plan,parts,metadata.first,size,metadata.standard,maximum,limits,prepared,work);
            if let Ok(value)=decoded {part2_cold_pure::<Part2DecodedLayoutTile>(Ok(Part2DecodedLayoutTile {prepared:value.prepared,counters,mct_work:value.mct_work}));}
            let finish=|decoded:Part2DecodedTileComponents,rest|Some((Ok(Part2DecodedLayoutTile {prepared:decoded.prepared,counters,mct_work:decoded.mct_work}),rest));
            part2_cold_bind(|events|part2_planned_decode_run(plan,parts,metadata.first,size,metadata.standard,maximum,limits,prepared,work,events),finish,decoded,result);
            part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_planned_decode_run(plan,parts,metadata.first,size,metadata.standard,maximum,limits,prepared,work,events),finish),result);
        },
    }
}
pub(crate) proof fn part2_tile_grid_plan_error(size:&crate::codestream::ImageSize,tile:u16,parts:Seq<Part2OwnedTilePart>,caps:Option<(u32,Seq<u16>)>,
    discard:Option<u8>,limits:&crate::ResourceLimits,prepared:Seq<Part1AssemblyTile>,initial:(u64,u64,u64),work:u64,metadata:Part2TileDecodeMetadata,error:crate::DecodeError)
    requires part2_tile_decode_metadata_owned(parts,crate::codestream::image_size_component_count(size),discard)==Ok(metadata),
        part2_tile_metadata_result(parts,crate::codestream::image_size_component_count(size),discard,Ok(metadata)),
        part2_grid_plan_result(size,metadata.first.coding_style,&metadata.first.component_coding_styles,metadata.first.component_quantizations,&metadata.first.roi_shifts,
            (tile,match discard {None=>0u8,Some(level)=>level}),(part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps)),limits,Err(error)),
    ensures part2_tile_decode_result(size,tile,parts,caps,discard,limits,prepared,initial,work,Err(error)),
{
    reveal(part2_tile_decode_result);reveal(part2_grid_plan_result);
    part2_grid_plan_frames(size,metadata.first.coding_style,&metadata.first.component_coding_styles,metadata.first.component_quantizations,&metadata.first.roi_shifts,
        (tile,match discard {None=>0u8,Some(level)=>level}),(part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps)),limits,Err(error));
    part2_cold_bind(|events|part2_grid_plan_run(size,metadata.first.coding_style,&metadata.first.component_coding_styles,metadata.first.component_quantizations,&metadata.first.roi_shifts,
            (tile,match discard {None=>0u8,Some(level)=>level}),(part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps)),limits,events),
        |plan:Part2ProgressionTilePlan,rest|part2_tile_after_grid_plan(size,parts,metadata,discard,limits,prepared,initial,work,plan,rest),Err(error),Err(error));
    part2_decode_eta(|events|part2_tile_after_metadata_run(size,tile,parts,caps,discard,limits,prepared,initial,work,metadata,events),Err(error));
    part2_tile_metadata_frames(parts,crate::codestream::image_size_component_count(size),discard,Ok(metadata));
    part2_cold_bind(|events|part2_tile_metadata_run(parts,crate::codestream::image_size_component_count(size),discard,events),
        |metadata:Part2TileDecodeMetadata,rest|part2_tile_after_metadata_run(size,tile,parts,caps,discard,limits,prepared,initial,work,metadata,rest),Ok(metadata),Err(error));
}
}
