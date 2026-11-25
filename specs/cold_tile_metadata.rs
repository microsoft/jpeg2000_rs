//! Selected tile metadata construction before actual grid/planning requests.
use super::*;
verus! {
pub enum Part2TileMetadataCapacityContext {
    SelectedResolutions {styles:crate::codestream::ComponentCodingStyles,main:crate::codestream::CodingStyle,components:u16,discard:u8},
}
pub(crate) open spec fn part2_tile_metadata_capacity_count(context:Part2TileMetadataCapacityContext)->usize {
    match context {Part2TileMetadataCapacityContext::SelectedResolutions {components,..}=>components as usize}
}
pub(crate) open spec fn part2_tile_metadata_capacity_run(context:Part2TileMetadataCapacityContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_tile_metadata_capacity_count(context);
    if count==0 {Some((Ok(()),events))}else if events.len()==0 {None}else{
        match events[0] {
            Part2JpipSnapshotEvent::TileMetadataCapacity {context:actual,elements,succeeded}=>
                if actual!=context || elements!=count {None}else{Some((if succeeded {Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
            _=>None,
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_tile_metadata_capacity_result(context:Part2TileMetadataCapacityContext,result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_tile_metadata_capacity_run(context,events),result)
}
pub(crate) proof fn part2_tile_metadata_capacity_observed(context:Part2TileMetadataCapacityContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_tile_metadata_capacity_count(context)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_tile_metadata_capacity_result(context,result),
{
    reveal(part2_tile_metadata_capacity_result);
    let count=part2_tile_metadata_capacity_count(context);
    let calls=if count==0 {Seq::empty()}else{seq![Part2JpipSnapshotEvent::TileMetadataCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_tile_metadata_capacity_run(context,calls+tail)==Some((result,tail)) by{
        if count==0 {assert(calls+tail =~= tail);}else{assert((calls+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_tile_metadata_capacity_run(context,events),calls,result));
}
pub(crate) open spec fn part2_tile_resolutions_run(styles:&crate::codestream::ComponentCodingStyles,main:crate::codestream::CodingStyle,
    components:u16,discard:Option<u8>,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<u8>> {
    let ordinary=part2_tile_component_resolutions(styles,main,components,discard);
    match discard {
        None=>Some((ordinary,events)),
        Some(levels)=>part2_jpip_snapshot_bind(part2_tile_metadata_capacity_run(Part2TileMetadataCapacityContext::SelectedResolutions {styles:*styles,main,components,discard:levels},events),
            |_:(),rest|Some((ordinary,rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_tile_resolutions_result(styles:&crate::codestream::ComponentCodingStyles,main:crate::codestream::CodingStyle,
    components:u16,discard:Option<u8>,result:Result<Seq<u8>,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_tile_resolutions_run(styles,main,components,discard,events),result)
}
pub(crate) proof fn part2_tile_resolutions_normal(styles:&crate::codestream::ComponentCodingStyles,main:crate::codestream::CodingStyle,
    components:u16,discard:Option<u8>)
    ensures part2_tile_resolutions_result(styles,main,components,discard,part2_tile_component_resolutions(styles,main,components,discard)),
{
    reveal(part2_tile_resolutions_result);reveal(part2_tile_metadata_capacity_result);
    let ordinary=part2_tile_component_resolutions(styles,main,components,discard);
    match discard {
        None=>{part2_cold_pure(ordinary);},
        Some(levels)=>{
            let context=Part2TileMetadataCapacityContext::SelectedResolutions {styles:*styles,main,components,discard:levels};
            part2_tile_metadata_capacity_observed(context,Ok(()));part2_cold_pure(ordinary);
            part2_cold_bind(|events|part2_tile_metadata_capacity_run(context,events),|_:(),rest|Some((ordinary,rest)),Ok(()),ordinary);
        },
    }
}
pub(crate) proof fn part2_tile_resolutions_refused(styles:&crate::codestream::ComponentCodingStyles,main:crate::codestream::CodingStyle,
    components:u16,discard:u8)
    requires part2_tile_metadata_capacity_result(Part2TileMetadataCapacityContext::SelectedResolutions {styles:*styles,main,components,discard},Err(crate::DecodeError::AllocationFailed)),
    ensures part2_tile_resolutions_result(styles,main,components,Some(discard),Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_tile_resolutions_result);reveal(part2_tile_metadata_capacity_result);
    part2_cold_bind(|events|part2_tile_metadata_capacity_run(Part2TileMetadataCapacityContext::SelectedResolutions {styles:*styles,main,components,discard},events),
        |_:(),rest|Some((part2_tile_component_resolutions(styles,main,components,Some(discard)),rest)),Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) open spec fn part2_tile_metadata_admit(parts:Seq<Part2OwnedTilePart>)->Result<(Part2OwnedTilePart,(bool,bool)),crate::DecodeError> {
    if parts.len()==0 {Err(crate::DecodeError::MalformedInput {offset:0,kind:crate::MalformedKind::InvalidTilePart})}
    else if !(forall|i:int|0<=i<parts.len()==> #[trigger] parts[i].multiple_component_transform==parts[0].multiple_component_transform) {
        Err(crate::DecodeError::MalformedInput {offset:0,kind:crate::MalformedKind::InvalidTransform})
    }else{
        match part2_tile_decode_standard_owned(parts[0]) {Err(error)=>Err(error),Ok(standard)=>Ok((parts[0],standard))}
    }
}
pub(crate) open spec fn part2_tile_metadata_run(parts:Seq<Part2OwnedTilePart>,components:u16,discard:Option<u8>,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2TileDecodeMetadata> {
    match part2_tile_metadata_admit(parts) {
        Err(error)=>Some((Err(error),events)),
        Ok((first,standard))=>part2_jpip_snapshot_bind(part2_tile_resolutions_run(&first.component_coding_styles,first.coding_style,components,discard,events),
            |resolution_counts:Seq<u8>,rest|Some((Ok(Part2TileDecodeMetadata {first,standard,resolution_counts}),rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_tile_metadata_result(parts:Seq<Part2OwnedTilePart>,components:u16,discard:Option<u8>,result:Result<Part2TileDecodeMetadata,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_tile_metadata_run(parts,components,discard,events),result)
}
pub(crate) proof fn part2_tile_metadata_normal(parts:Seq<Part2OwnedTilePart>,components:u16,discard:Option<u8>)
    ensures part2_tile_metadata_result(parts,components,discard,part2_tile_decode_metadata_owned(parts,components,discard)),
{
    reveal(part2_tile_metadata_result);reveal(part2_tile_resolutions_result);
    let ordinary=part2_tile_decode_metadata_owned(parts,components,discard);
    match part2_tile_metadata_admit(parts) {
        Err(_)=>{part2_cold_pure::<Part2TileDecodeMetadata>(ordinary);},
        Ok((first,standard))=>{
            part2_tile_resolutions_normal(&first.component_coding_styles,first.coding_style,components,discard);
            let counts=part2_tile_component_resolutions(&first.component_coding_styles,first.coding_style,components,discard);
            if let Ok(values)=counts {part2_cold_pure::<Part2TileDecodeMetadata>(Ok(Part2TileDecodeMetadata {first,standard,resolution_counts:values}));}
            part2_cold_bind(|events|part2_tile_resolutions_run(&first.component_coding_styles,first.coding_style,components,discard,events),
                |resolution_counts:Seq<u8>,rest|Some((Ok(Part2TileDecodeMetadata {first,standard,resolution_counts}),rest)),counts,ordinary);
        },
    }
}
pub(crate) proof fn part2_tile_metadata_resolution_error(parts:Seq<Part2OwnedTilePart>,components:u16,discard:Option<u8>,first:Part2OwnedTilePart,standard:(bool,bool),error:crate::DecodeError)
    requires part2_tile_metadata_admit(parts)==Ok((first,standard)),
        part2_tile_resolutions_result(&first.component_coding_styles,first.coding_style,components,discard,Err(error)),
    ensures part2_tile_metadata_result(parts,components,discard,Err(error)),
{
    reveal(part2_tile_metadata_result);reveal(part2_tile_resolutions_result);
    part2_cold_bind(|events|part2_tile_resolutions_run(&first.component_coding_styles,first.coding_style,components,discard,events),
        |resolution_counts:Seq<u8>,rest|Some((Ok(Part2TileDecodeMetadata {first,standard,resolution_counts}),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_tile_metadata_frames(parts:Seq<Part2OwnedTilePart>,components:u16,discard:Option<u8>,result:Result<Part2TileDecodeMetadata,crate::DecodeError>)
    requires part2_tile_metadata_result(parts,components,discard,result),
    ensures part2_cold_framed(|events|part2_tile_metadata_run(parts,components,discard,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2TileDecodeMetadata>|
            (forall|events| #[trigger] other(events)==part2_tile_metadata_run(parts,components,discard,events)) ==> #[trigger] part2_cold_framed(other,result),
{
    reveal(part2_tile_metadata_result);
    part2_decode_eta(|events|part2_tile_metadata_run(parts,components,discard,events),result);
}
pub(crate) open spec fn part2_tile_after_metadata_run(size:&crate::codestream::ImageSize,tile:u16,parts:Seq<Part2OwnedTilePart>,caps:Option<(u32,Seq<u16>)>,
    discard:Option<u8>,limits:&crate::ResourceLimits,prepared:Seq<Part1AssemblyTile>,initial:(u64,u64,u64),work:u64,
    metadata:Part2TileDecodeMetadata,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2DecodedLayoutTile> {
    if private_ht_eligible(size,tile,parts,caps,discard){
        private_image_run(PrivateImageContext{size:*size,tile,parts,caps,discard,limits:*limits,prepared,initial,work,metadata},events)
    }else if private_ht_standard_eligible(size,tile,parts,caps,discard){
        private_standard_image_run(PrivateImageContext{size:*size,tile,parts,caps,discard,limits:*limits,prepared,initial,work,metadata},events)
    }else{part2_jpip_snapshot_bind(part2_grid_plan_run(size,metadata.first.coding_style,&metadata.first.component_coding_styles,
        metadata.first.component_quantizations,&metadata.first.roi_shifts,(tile,match discard {None=>0u8,Some(level)=>level}),
        (part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps),true),limits,events),
        |plan:Part2ProgressionTilePlan,rest|part2_tile_after_grid_plan(size,parts,metadata,discard,limits,prepared,initial,work,plan,rest))}
}
pub(crate) proof fn part2_tile_after_metadata_normal(size:&crate::codestream::ImageSize,tile:u16,parts:Seq<Part2OwnedTilePart>,caps:Option<(u32,Seq<u16>)>,
    discard:Option<u8>,limits:&crate::ResourceLimits,prepared:Seq<Part1AssemblyTile>,initial:(u64,u64,u64),work:u64,metadata:Part2TileDecodeMetadata)
    requires part2_tile_decode_metadata_owned(parts,crate::codestream::image_size_component_count(size),discard)==Ok(metadata),
    ensures part2_cold_framed(|events|part2_tile_after_metadata_run(size,tile,parts,caps,discard,limits,prepared,initial,work,metadata,events),
        part2_decode_tile_parts_owned(size,tile,parts,caps,discard,limits,prepared,initial,work)),
{
    if private_ht_eligible(size,tile,parts,caps,discard){
        let context=PrivateImageContext{size:*size,tile,parts,caps,discard,limits:*limits,prepared,initial,work,metadata};
        private_image_normal(context);private_image_reference(context);
        part2_decode_eta(|events|private_image_run(context,events),private_image_value(context));
    }else if private_ht_standard_eligible(size,tile,parts,caps,discard){
        let context=PrivateImageContext{size:*size,tile,parts,caps,discard,limits:*limits,prepared,initial,work,metadata};
        private_standard_image_normal(context);private_standard_image_reference(context);
        part2_decode_eta(|events|private_standard_image_run(context,events),private_standard_image_value(context));
    }else{
    let result=part2_decode_tile_parts_owned(size,tile,parts,caps,discard,limits,prepared,initial,work);
    let select=(tile,match discard {None=>0u8,Some(level)=>level});
    let policy=(part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps),true);
    let plan=part2_progression_tile_plan_owned(size,metadata.first.coding_style,&metadata.first.component_coding_styles,metadata.first.component_quantizations,&metadata.first.roi_shifts,select,policy,limits);
    part2_grid_plan_normal(size,metadata.first.coding_style,&metadata.first.component_coding_styles,metadata.first.component_quantizations,&metadata.first.roi_shifts,select,policy,limits);
    part2_grid_plan_frames(size,metadata.first.coding_style,&metadata.first.component_coding_styles,metadata.first.component_quantizations,&metadata.first.roi_shifts,select,policy,limits,plan);
    if let Ok(value)=plan {
        part2_tile_after_grid_plan_normal(size,tile,parts,caps,discard,limits,prepared,initial,work,metadata,value);
        part2_decode_eta(|events|part2_tile_after_grid_plan(size,parts,metadata,discard,limits,prepared,initial,work,value,events),result);
    }
    part2_cold_bind(|events|part2_grid_plan_run(size,metadata.first.coding_style,&metadata.first.component_coding_styles,metadata.first.component_quantizations,&metadata.first.roi_shifts,select,policy,limits,events),
        |plan:Part2ProgressionTilePlan,rest|part2_tile_after_grid_plan(size,parts,metadata,discard,limits,prepared,initial,work,plan,rest),plan,result);
    }
}
pub(crate) proof fn part2_tile_metadata_decode_error(size:&crate::codestream::ImageSize,tile:u16,parts:Seq<Part2OwnedTilePart>,caps:Option<(u32,Seq<u16>)>,
    discard:Option<u8>,limits:&crate::ResourceLimits,prepared:Seq<Part1AssemblyTile>,initial:(u64,u64,u64),work:u64,error:crate::DecodeError)
    requires part2_tile_metadata_result(parts,crate::codestream::image_size_component_count(size),discard,Err(error)),
    ensures part2_tile_decode_result(size,tile,parts,caps,discard,limits,prepared,initial,work,Err(error)),
{
    reveal(part2_tile_decode_result);
    part2_tile_metadata_frames(parts,crate::codestream::image_size_component_count(size),discard,Err(error));
    part2_cold_bind(|events|part2_tile_metadata_run(parts,crate::codestream::image_size_component_count(size),discard,events),
        |metadata:Part2TileDecodeMetadata,rest|part2_tile_after_metadata_run(size,tile,parts,caps,discard,limits,prepared,initial,work,metadata,rest),Err(error),Err(error));
}
}
