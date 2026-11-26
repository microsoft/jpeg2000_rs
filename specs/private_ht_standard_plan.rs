use super::*;
verus! {

pub(crate) open spec fn private_ht_standard_component_eligible(
    size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,component:u16,
)->bool {
        match crate::codestream::component_coding_style_result(&first.component_coding_styles,component) {
            Err(_)=>false,
            Ok(style)=>match crate::codestream::coding_style_tier1_result(style) {
                Err(_)=>false,
                Ok(tier1)=>match part2_roi_shift(crate::codestream::roi_shifts_view(&first.roi_shifts),component) {
                    Err(_)=>false,
                    Ok(roi)=>match part2_tile_component_bounds(
                        crate::codestream::selection_geometry_view(size),
                        crate::codestream::image_size_component_count(size),
                        crate::codestream::image_size_component_infos(size),first.tile_index,component,
                    ) {
                        Err(_)=>false,
                        Ok(bounds)=>match part2_resolution_geometry(
                            crate::codestream::selection_geometry_view(size),
                            crate::codestream::image_size_component_count(size),
                            crate::codestream::image_size_component_infos(size),
                            crate::decode::resolution_geometry_style(style),component,style.decomposition_levels,Some(tile),
                        ) {
                            Err(_)=>false,
                            Ok(geometry)=>matches!(tier1.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput)
                                && style.decomposition_structure.is_none() && !style.precincts_defined
                                && !matches!(style.transform,crate::codestream::WaveletTransform::Arbitrary(_))
                                && crate::codestream::parsed_coding_style_view(style)
                                    ==crate::codestream::parsed_coding_style_view(first.coding_style)
                                && roi==0
                                && bounds.x0==0 && bounds.y0==0
                                && 0<bounds.x1<=32768 && 0<bounds.y1<=32768
                                && geometry.precincts==1 && geometry.precincts_across==1 && geometry.precincts_down==1,
                        },
                    },
                },
            },
        }
}

pub(crate) open spec fn private_ht_standard_eligible(
    size:&crate::codestream::ImageSize,tile:u16,parts:Seq<Part2OwnedTilePart>,
    caps:Option<(u32,Seq<u16>)>,discard:Option<u8>,
)->bool {
    crate::decode::PRIVATE_HT_PRIMARY_ENABLED
        && crate::codestream::image_size_component_count(size)>0 && parts.len()==1
        && (discard.is_none() || discard==Some(0u8)) && part2_profile_force_ht(caps)
        && parts[0].tile_index==tile
        && (crate::codestream::image_size_component_count(size)>1 || parts[0].coding_style.decomposition_levels>0)
        && !parts[0].has_functional_header_marker && parts[0].multiple_component_transform.is_none()
        && parts[0].progression_changes.len()==0
        && (match parts[0].packed_packet_headers.source{Part1PackedHeaderSource::None=>true,_=>false})
        && (match parts[0].packet_lengths.source{Part1PacketLengthSource::None=>true,_=>false})
        && !parts[0].has_roi_marker
        && (forall|component:u16|component<crate::codestream::image_size_component_count(size) ==>
            #[trigger] private_ht_standard_component_eligible(size,tile,parts[0],component))
}

pub(crate) proof fn private_standard_eligible_at(size:&crate::codestream::ImageSize,tile:u16,
    first:Part2OwnedTilePart,caps:Option<(u32,Seq<u16>)>,discard:Option<u8>,component:u16)
    requires private_ht_standard_eligible(size,tile,seq![first],caps,discard),
        component<crate::codestream::image_size_component_count(size),
    ensures private_ht_standard_component_eligible(size,tile,first,component),
{
    assert(0<=(component as int) && (component as int)<crate::codestream::image_size_component_count(size));
    assert(((component as int) as u16)==component);
}

pub(crate) proof fn private_standard_component_style_fields(size:&crate::codestream::ImageSize,tile:u16,
    first:Part2OwnedTilePart,component:u16)
    requires private_ht_standard_component_eligible(size,tile,first,component),
    ensures crate::codestream::component_coding_style_result(&first.component_coding_styles,component).is_ok(),
        crate::codestream::component_coding_style_result(&first.component_coding_styles,component).get_Ok_0().decomposition_levels
            ==first.coding_style.decomposition_levels,
        crate::codestream::component_coding_style_result(&first.component_coding_styles,component).get_Ok_0().transform==first.coding_style.transform,
        !matches!(first.coding_style.transform,crate::codestream::WaveletTransform::Arbitrary(_)),
{
    let style=crate::codestream::component_coding_style_result(&first.component_coding_styles,component).get_Ok_0();
    crate::codestream::parsed_coding_style_known_fields(style);
    crate::codestream::parsed_coding_style_known_fields(first.coding_style);
    crate::codestream::resolution_selectors_known_fields(style);
}

pub(crate) proof fn private_standard_selected_counts(size:&crate::codestream::ImageSize,tile:u16,
    first:Part2OwnedTilePart,component:u16,before:Seq<u8>)
    requires component<=crate::codestream::image_size_component_count(size),
        first.coding_style.decomposition_levels<u8::MAX,
        forall|i:u16|component<=i<crate::codestream::image_size_component_count(size) ==>
            #[trigger] private_ht_standard_component_eligible(size,tile,first,i),
    ensures part2_selected_tile_resolutions(&first.component_coding_styles,first.coding_style,
        crate::codestream::image_size_component_count(size),0,component,before)==Ok(
            before+Seq::new((crate::codestream::image_size_component_count(size)-component) as nat,
                |_:int|(first.coding_style.decomposition_levels+1) as u8)),
    decreases crate::codestream::image_size_component_count(size)-component,
{
    reveal_with_fuel(part2_selected_tile_resolutions,1);
    if component<crate::codestream::image_size_component_count(size){
        assert(private_ht_standard_component_eligible(size,tile,first,component));
        private_standard_component_style_fields(size,tile,first,component);
        let count=(first.coding_style.decomposition_levels+1) as u8;
        private_standard_selected_counts(size,tile,first,(component+1) as u16,before.push(count));
        assert(before.push(count)+Seq::new((crate::codestream::image_size_component_count(size)-component-1) as nat,|_:int|count)
            =~= before+Seq::new((crate::codestream::image_size_component_count(size)-component) as nat,|_:int|count));
    }else{assert(before+Seq::<u8>::empty() =~= before);}
}

pub(crate) proof fn private_ht_standard_selected_metadata(
    size:&crate::codestream::ImageSize,tile:u16,parts:Seq<Part2OwnedTilePart>,
    caps:Option<(u32,Seq<u16>)>,discard:Option<u8>,metadata:Part2TileDecodeMetadata,
)
    requires private_ht_standard_eligible(size,tile,parts,caps,discard),
        part2_tile_decode_metadata_owned(parts,crate::codestream::image_size_component_count(size),discard)==Ok(metadata),
    ensures metadata.first==parts[0],
        metadata.standard.0==parts[0].coding_style.multiple_component_transform,
        private_ht_standard_eligible(size,tile,parts,caps,None),
        metadata.resolution_counts==match discard {
            None=>Seq::empty(),
            Some(_)=>Seq::new(crate::codestream::image_size_component_count(size) as nat,
                |_:int|(metadata.first.coding_style.decomposition_levels+1) as u8),
        },
{
    private_standard_eligible_at(size,tile,parts[0],caps,discard,0);
    private_standard_component_style_fields(size,tile,parts[0],0);
    if discard.is_some(){
        reveal_with_fuel(part2_selected_tile_resolutions,1);
        assert(parts[0].coding_style.decomposition_levels<u8::MAX);
        private_standard_selected_counts(size,tile,parts[0],0,Seq::empty());
    }
    assert(Seq::<u8>::empty()+Seq::new(crate::codestream::image_size_component_count(size) as nat,
        |_:int|(metadata.first.coding_style.decomposition_levels+1) as u8)
        =~= Seq::new(crate::codestream::image_size_component_count(size) as nat,
            |_:int|(metadata.first.coding_style.decomposition_levels+1) as u8));
}

pub struct PrivateStandardBlockContext {
    pub lattice:Part2PlannedSubbandLattice,pub geometry:crate::decode::SubbandGeometry,
    pub style:crate::tier1::Tier1CodingStyle,pub allowed:bool,pub bound:u8,pub indices:(usize,usize),
}

pub struct PrivateStandardBlocksState {
    pub blocks:Seq<PrivateHtDecoderState>,
    pub placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    pub next:usize,pub total:u64,
}

pub(crate) open spec fn private_standard_blocks_public(state:PrivateStandardBlocksState)->Part2PlannedCodeBlocks {
    Part2PlannedCodeBlocks {
        decoders:state.blocks.map_values(|decoder:PrivateHtDecoderState|decoder.logical),
        placements:state.placements,decoder_index:state.next,planned_code_blocks:state.total,
    }
}

pub(crate) open spec fn private_standard_blocks_wf(state:PrivateStandardBlocksState)->bool {
    forall|i:int|0<=i<state.blocks.len() ==> #[trigger] private_ht_state_wf(state.blocks[i])
}

pub(crate) open spec fn private_standard_cell_context(context:PrivateStandardBlockContext,geometry:(u32,u32,u16,u16))->PrivateHtInitialContext {
    PrivateHtInitialContext {
        width:geometry.2,height:geometry.3,bitplanes:context.geometry.significant_bitplanes,
        orientation:context.geometry.orientation,style:context.style,allowed:context.allowed,bound:context.bound,
    }
}

pub(crate) open spec fn private_standard_placement(context:PrivateStandardBlockContext,
    before:PrivateStandardBlocksState,geometry:(u32,u32,u16,u16))->Result<crate::decode::ProgressionCodeBlockPlacement,crate::DecodeError> {
    if geometry.0<context.geometry.x0 || geometry.1<context.geometry.y0{Err(part1_block_placement_error(true))}
    else{Ok(crate::decode::ProgressionCodeBlockPlacement {
        precinct_index:context.indices.0,decoder_index:before.next,subband_index:context.indices.1,
        x:(geometry.0-context.geometry.x0) as u32,y:(geometry.1-context.geometry.y0) as u32,
    })}
}

pub(crate) open spec fn private_standard_cell_finish(before:PrivateStandardBlocksState,decoder:PrivateHtDecoderState,
    placement:crate::decode::ProgressionCodeBlockPlacement)->Result<PrivateStandardBlocksState,crate::DecodeError> {
    if before.next==usize::MAX{Err(part1_block_placement_error(true))}
    else{Ok(PrivateStandardBlocksState {
        blocks:before.blocks.push(decoder),placements:before.placements.push(placement),
        next:(before.next+1) as usize,total:before.total,
    })}
}

pub(crate) open spec fn private_standard_cell_value(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,
    block:[u32;2])->Result<PrivateStandardBlocksState,crate::DecodeError> {
    match part2_planned_codeblock_geometry(context.lattice.grid,context.lattice.clip,block){
        Err(error)=>Err(error),
        Ok(geometry)=>match private_ht_initial_value(private_standard_cell_context(context,geometry)){
            Err(error)=>Err(error),Ok(decoder)=>match private_standard_placement(context,before,geometry){
                Err(error)=>Err(error),Ok(placement)=>private_standard_cell_finish(before,decoder,placement),
            },
        },
    }
}

pub(crate) open spec fn private_standard_cell_after_placement(before:PrivateStandardBlocksState,decoder:PrivateHtDecoderState,
    placement:crate::decode::ProgressionCodeBlockPlacement,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardBlocksState> {
    part2_jpip_snapshot_bind(private_owner_capacity_run(
        PrivateOwnerCapacityContext::PlacementAppend {source:before.placements,next:placement},events),
        |_:(),rest|Some((private_standard_cell_finish(before,decoder,placement),rest)))
}

pub(crate) open spec fn private_standard_cell_after_append(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,
    geometry:(u32,u32,u16,u16),decoder:PrivateHtDecoderState,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardBlocksState> {
    part2_jpip_snapshot_bind(Some((private_standard_placement(context,before,geometry),events)),
        |placement:crate::decode::ProgressionCodeBlockPlacement,rest|private_standard_cell_after_placement(before,decoder,placement,rest))
}

pub(crate) open spec fn private_standard_cell_after_initial(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,
    geometry:(u32,u32,u16,u16),decoder:PrivateHtDecoderState,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardBlocksState> {
    part2_jpip_snapshot_bind(private_owner_capacity_run(
        PrivateOwnerCapacityContext::BlockAppend {source:before.blocks,next:decoder},events),
        |_:(),rest|private_standard_cell_after_append(context,before,geometry,decoder,rest))
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_cell_run(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,
    block:[u32;2],events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardBlocksState> {
    match part2_planned_codeblock_geometry(context.lattice.grid,context.lattice.clip,block){
        Err(error)=>Some((Err(error),events)),
        Ok(geometry)=>part2_jpip_snapshot_bind(private_decoder_initial_calls_run(private_standard_cell_context(context,geometry),events),
            |decoder:PrivateHtDecoderState,rest|private_standard_cell_after_initial(context,before,geometry,decoder,rest)),
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_columns_value(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,
    row:u32,column:nat)->Result<PrivateStandardBlocksState,crate::DecodeError>
    decreases context.lattice.blocks[0] as nat-column,
{
    if column>=context.lattice.blocks[0]{Ok(before)}
    else{match private_standard_cell_value(context,before,[column as u32,row]){
        Err(error)=>Err(error),Ok(after)=>private_standard_columns_value(context,after,row,column+1),
    }}
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_rows_value(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,
    row:nat)->Result<PrivateStandardBlocksState,crate::DecodeError>
    decreases context.lattice.blocks[1] as nat-row,
{
    if row>=context.lattice.blocks[1]{Ok(before)}
    else{match private_standard_columns_value(context,before,row as u32,0){
        Err(error)=>Err(error),Ok(after)=>private_standard_rows_value(context,after,row+1),
    }}
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_columns_run(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,
    row:u32,column:nat,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardBlocksState>
    decreases context.lattice.blocks[0] as nat-column,
{
    if column>=context.lattice.blocks[0]{Some((Ok(before),events))}
    else{part2_jpip_snapshot_bind(private_standard_cell_run(context,before,[column as u32,row],events),
        |after:PrivateStandardBlocksState,rest|private_standard_columns_run(context,after,row,column+1,rest))}
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_rows_run(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,
    row:nat,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardBlocksState>
    decreases context.lattice.blocks[1] as nat-row,
{
    if row>=context.lattice.blocks[1]{Some((Ok(before),events))}
    else{part2_jpip_snapshot_bind(private_standard_columns_run(context,before,row as u32,0,events),
        |after:PrivateStandardBlocksState,rest|private_standard_rows_run(context,after,row+1,rest))}
}

pub(crate) open spec fn private_standard_blocks_admit(context:PrivateStandardBlockContext,total:u64,
    limits:&crate::ResourceLimits)->Result<(usize,u64),crate::DecodeError> {
    let count=context.lattice.blocks[0] as nat*context.lattice.blocks[1] as nat;
    let next=total as nat+count;
    if count>u64::MAX || next>u64::MAX{Err(part1_block_placement_error(true))}
    else if next>crate::limits::resource_code_block_limit(limits){
        Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::CodeBlocks,limit:crate::limits::resource_code_block_limit(limits),actual:next as u64})
    }else if next>crate::limits::resource_work_limit(limits){
        Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::WorkUnits,limit:crate::limits::resource_work_limit(limits),actual:next as u64})
    }else if count>usize::MAX{Err(part1_block_placement_error(true))}
    else{Ok((count as usize,next as u64))}
}

pub(crate) open spec fn private_standard_blocks_capacity(context:PrivateStandardBlockContext,count:usize)->PrivateOwnerCapacityContext {
    PrivateOwnerCapacityContext::Blocks {
        geometry:context.geometry,grid:context.lattice.grid,clip:context.lattice.clip,shape:context.lattice.blocks,
        style:context.style,allowed:context.allowed,bound:context.bound,count,
    }
}

pub(crate) open spec fn private_standard_blocks_capacity_run(context:PrivateStandardBlockContext,count:usize,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    if count==0{Some((Ok(()),events))}
    else{private_owner_capacity_run(private_standard_blocks_capacity(context,count),events)}
}

pub(crate) proof fn private_standard_blocks_capacity_observed(context:PrivateStandardBlockContext,count:usize,response:Result<(),crate::DecodeError>)
    requires if count==0{response==Ok(())}else{private_owner_capacity_result(private_standard_blocks_capacity(context,count),response)},
    ensures part2_cold_framed(|events|private_standard_blocks_capacity_run(context,count,events),response),
{
    if count==0{part2_cold_pure(response);}
    else{part2_cold_framed_extensional(|events|private_owner_capacity_run(private_standard_blocks_capacity(context,count),events),
        |events|private_standard_blocks_capacity_run(context,count,events),response);}
}

pub(crate) open spec fn private_standard_blocks_initial(placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    first:usize,total:u64)->PrivateStandardBlocksState {
    PrivateStandardBlocksState {blocks:Seq::empty(),placements,next:first,total}
}

pub(crate) open spec fn private_standard_blocks_value(context:PrivateStandardBlockContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,first:usize,total:u64,
    limits:&crate::ResourceLimits)->Result<PrivateStandardBlocksState,crate::DecodeError> {
    match private_standard_blocks_admit(context,total,limits){
        Err(error)=>Err(error),Ok((_,next))=>private_standard_rows_value(context,private_standard_blocks_initial(placements,first,next),0),
    }
}

pub(crate) open spec fn private_standard_blocks_run(context:PrivateStandardBlockContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,first:usize,total:u64,
    limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardBlocksState> {
    match private_standard_blocks_admit(context,total,limits){
        Err(error)=>Some((Err(error),events)),
        Ok((count,next))=>part2_jpip_snapshot_bind(private_standard_blocks_capacity_run(context,count,events),
            |_:(),rest|private_standard_rows_run(context,private_standard_blocks_initial(placements,first,next),0,rest)),
    }
}

pub(crate) proof fn private_standard_cell_reference(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,block:[u32;2])
    requires context.style.force_high_throughput,
        matches!(context.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
    ensures match private_standard_cell_value(context,before,block){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_blocks_public(after)),
    }==part2_planned_codeblock_cell(context.lattice.grid,context.lattice.clip,block,context.geometry,context.style,
        (context.allowed,context.bound,true),context.indices,private_standard_blocks_public(before)),
{
    if let Ok(geometry)=part2_planned_codeblock_geometry(context.lattice.grid,context.lattice.clip,block){
        private_ht_initial_equivalent(private_standard_cell_context(context,geometry));
        if let Ok(decoder)=private_ht_initial_value(private_standard_cell_context(context,geometry)){
            assert(before.blocks.push(decoder).map_values(|value:PrivateHtDecoderState|value.logical) =~=
                before.blocks.map_values(|value:PrivateHtDecoderState|value.logical).push(decoder.logical));
        }
    }
}

pub(crate) proof fn private_standard_columns_reference(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,row:u32,column:nat)
    requires context.style.force_high_throughput,
        matches!(context.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
    ensures match private_standard_columns_value(context,before,row,column){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_blocks_public(after)),
    }==part2_planned_codeblock_columns(context.lattice.grid,context.lattice.clip,context.lattice.blocks[0],context.geometry,
        context.style,(context.allowed,context.bound,true),context.indices,row,column,private_standard_blocks_public(before)),
    decreases context.lattice.blocks[0] as nat-column,
{
    reveal_with_fuel(private_standard_columns_value,1);reveal_with_fuel(part2_planned_codeblock_columns,1);
    if column<context.lattice.blocks[0]{
        private_standard_cell_reference(context,before,[column as u32,row]);
        if let Ok(after)=private_standard_cell_value(context,before,[column as u32,row]){
            private_standard_columns_reference(context,after,row,column+1);
        }
    }
}

pub(crate) proof fn private_standard_rows_reference(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,row:nat)
    requires context.style.force_high_throughput,
        matches!(context.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
    ensures match private_standard_rows_value(context,before,row){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_blocks_public(after)),
    }==part2_planned_codeblock_rows(context.lattice.grid,context.lattice.clip,context.lattice.blocks,context.geometry,
        context.style,(context.allowed,context.bound,true),context.indices,row,private_standard_blocks_public(before)),
    decreases context.lattice.blocks[1] as nat-row,
{
    reveal_with_fuel(private_standard_rows_value,1);reveal_with_fuel(part2_planned_codeblock_rows,1);
    if row<context.lattice.blocks[1]{
        private_standard_columns_reference(context,before,row as u32,0);
        if let Ok(after)=private_standard_columns_value(context,before,row as u32,0){
            private_standard_rows_reference(context,after,row+1);
        }
    }
}

pub(crate) proof fn private_standard_blocks_reference(context:PrivateStandardBlockContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,first:usize,total:u64,limits:&crate::ResourceLimits)
    requires context.style.force_high_throughput,
        matches!(context.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
    ensures match private_standard_blocks_value(context,placements,first,total,limits){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_blocks_public(after)),
    }==part2_planned_codeblocks(context.lattice.grid,context.lattice.clip,context.lattice.blocks,context.geometry,
        context.style,(context.allowed,context.bound,true),(context.indices.0,context.indices.1,first),placements,total,true,limits),
{
    if let Ok((_,next))=private_standard_blocks_admit(context,total,limits){
        assert(private_standard_blocks_initial(placements,first,next).blocks.map_values(
            |decoder:PrivateHtDecoderState|decoder.logical) =~= Seq::empty());
        assert(private_standard_blocks_public(private_standard_blocks_initial(placements,first,next))==
            (Part2PlannedCodeBlocks {decoders:Seq::empty(),placements,decoder_index:first,planned_code_blocks:next}));
        private_standard_rows_reference(context,private_standard_blocks_initial(placements,first,next),0);
    }
}

pub(crate) proof fn private_standard_cell_fields(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,
    block:[u32;2],after:PrivateStandardBlocksState)
    requires private_standard_blocks_wf(before),private_standard_cell_value(context,before,block)==Ok(after),
    ensures private_standard_blocks_wf(after),after.blocks.len()==before.blocks.len()+1,
        after.placements.len()==before.placements.len()+1,after.total==before.total,
{
    let geometry=part2_planned_codeblock_geometry(context.lattice.grid,context.lattice.clip,block).get_Ok_0();
    let decoder=private_ht_initial_value(private_standard_cell_context(context,geometry)).get_Ok_0();
    private_ht_initial_fields(private_standard_cell_context(context,geometry),decoder);
}

pub(crate) proof fn private_standard_cell_normal(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,block:[u32;2])
    ensures part2_cold_framed(|events|private_standard_cell_run(context,before,block,events),private_standard_cell_value(context,before,block)),
{
    reveal(private_standard_cell_run);
    let result=private_standard_cell_value(context,before,block);
    match part2_planned_codeblock_geometry(context.lattice.grid,context.lattice.clip,block){
        Err(_)=>part2_cold_pure(result),
        Ok(geometry)=>{
            let ctor=private_standard_cell_context(context,geometry);
            let initial=private_ht_initial_value(ctor);
            private_ht_initial_normal(ctor);private_decoder_initial_calls_observed(ctor,initial);
            if let Ok(decoder)=initial{
                private_owner_capacity_observed(PrivateOwnerCapacityContext::BlockAppend {source:before.blocks,next:decoder},Ok(()));
                let placement=private_standard_placement(context,before,geometry);
                part2_cold_pure(placement);
                if let Ok(place)=placement{
                    private_owner_capacity_observed(PrivateOwnerCapacityContext::PlacementAppend {source:before.placements,next:place},Ok(()));
                    part2_cold_pure(result);
                    part2_cold_bind(|events|private_owner_capacity_run(PrivateOwnerCapacityContext::PlacementAppend {
                        source:before.placements,next:place},events),|_:(),rest|Some((private_standard_cell_finish(before,decoder,place),rest)),Ok(()),result);
                    part2_decode_eta(|events|private_standard_cell_after_placement(before,decoder,place,events),result);
                }
                part2_cold_bind(|events|Some((placement,events)),
                    |place,rest|private_standard_cell_after_placement(before,decoder,place,rest),placement,result);
                part2_decode_eta(|events|private_standard_cell_after_append(context,before,geometry,decoder,events),result);
                part2_cold_bind(|events|private_owner_capacity_run(PrivateOwnerCapacityContext::BlockAppend {
                    source:before.blocks,next:decoder},events),
                    |_:(),rest|private_standard_cell_after_append(context,before,geometry,decoder,rest),Ok(()),result);
                part2_decode_eta(|events|private_standard_cell_after_initial(context,before,geometry,decoder,events),result);
            }
            part2_cold_bind(|events|private_decoder_initial_calls_run(ctor,events),
                |decoder,rest|private_standard_cell_after_initial(context,before,geometry,decoder,rest),initial,result);
        },
    }
}

pub(crate) proof fn private_standard_columns_normal(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,row:u32,column:nat)
    ensures part2_cold_framed(|events|private_standard_columns_run(context,before,row,column,events),
        private_standard_columns_value(context,before,row,column)),
    decreases context.lattice.blocks[0] as nat-column,
{
    reveal_with_fuel(private_standard_columns_run,1);reveal_with_fuel(private_standard_columns_value,1);
    let result=private_standard_columns_value(context,before,row,column);
    if column>=context.lattice.blocks[0]{part2_cold_pure(result);}
    else{
        let value=private_standard_cell_value(context,before,[column as u32,row]);
        private_standard_cell_normal(context,before,[column as u32,row]);
        if let Ok(after)=value{
            private_standard_columns_normal(context,after,row,column+1);
            part2_decode_eta(|events|private_standard_columns_run(context,after,row,column+1,events),result);
        }
        part2_cold_bind(|events|private_standard_cell_run(context,before,[column as u32,row],events),
            |after,rest|private_standard_columns_run(context,after,row,column+1,rest),value,result);
    }
}

pub(crate) proof fn private_standard_rows_normal(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,row:nat)
    ensures part2_cold_framed(|events|private_standard_rows_run(context,before,row,events),private_standard_rows_value(context,before,row)),
    decreases context.lattice.blocks[1] as nat-row,
{
    reveal_with_fuel(private_standard_rows_run,1);reveal_with_fuel(private_standard_rows_value,1);
    let result=private_standard_rows_value(context,before,row);
    if row>=context.lattice.blocks[1]{part2_cold_pure(result);}
    else{
        let value=private_standard_columns_value(context,before,row as u32,0);
        private_standard_columns_normal(context,before,row as u32,0);
        if let Ok(after)=value{
            private_standard_rows_normal(context,after,row+1);
            part2_decode_eta(|events|private_standard_rows_run(context,after,row+1,events),result);
        }
        part2_cold_bind(|events|private_standard_columns_run(context,before,row as u32,0,events),
            |after,rest|private_standard_rows_run(context,after,row+1,rest),value,result);
    }
}

pub(crate) proof fn private_standard_blocks_normal(context:PrivateStandardBlockContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,first:usize,total:u64,limits:&crate::ResourceLimits)
    ensures part2_cold_framed(|events|private_standard_blocks_run(context,placements,first,total,limits,events),
        private_standard_blocks_value(context,placements,first,total,limits)),
{
    let result=private_standard_blocks_value(context,placements,first,total,limits);
    match private_standard_blocks_admit(context,total,limits){
        Err(_)=>part2_cold_pure(result),
        Ok((count,next))=>{
            if count==0{part2_cold_pure::<()>(Ok(()));}
            else{private_owner_capacity_observed(private_standard_blocks_capacity(context,count),Ok(()));}
            private_standard_blocks_capacity_observed(context,count,Ok(()));
            let initial=private_standard_blocks_initial(placements,first,next);
            private_standard_rows_normal(context,initial,0);
            part2_decode_eta(|events|private_standard_rows_run(context,initial,0,events),result);
            part2_cold_bind(|events|private_standard_blocks_capacity_run(context,count,events),
                |_:(),rest|private_standard_rows_run(context,initial,0,rest),Ok(()),result);
        },
    }
}

pub(crate) open spec fn private_standard_columns_prefix(context:PrivateStandardBlockContext,initial:PrivateStandardBlocksState,
    row:u32,column:nat,current:PrivateStandardBlocksState,prefix:Seq<Part2JpipSnapshotEvent>)->bool {
    forall|tail| #[trigger] private_standard_columns_run(context,initial,row,0,prefix+tail)
        ==private_standard_columns_run(context,current,row,column,tail)
}

pub(crate) open spec fn private_standard_rows_prefix(context:PrivateStandardBlockContext,initial:PrivateStandardBlocksState,
    row:nat,current:PrivateStandardBlocksState,prefix:Seq<Part2JpipSnapshotEvent>)->bool {
    forall|tail| #[trigger] private_standard_rows_run(context,initial,0,prefix+tail)
        ==private_standard_rows_run(context,current,row,tail)
}

pub(crate) proof fn private_standard_column_advance(context:PrivateStandardBlockContext,initial:PrivateStandardBlocksState,
    row:u32,column:nat,current:PrivateStandardBlocksState,prefix:Seq<Part2JpipSnapshotEvent>,after:PrivateStandardBlocksState)
    ->(extended:Seq<Part2JpipSnapshotEvent>)
    requires column<context.lattice.blocks[0],private_standard_columns_prefix(context,initial,row,column,current,prefix),
        part2_cold_framed(|events|private_standard_cell_run(context,current,[column as u32,row],events),Ok(after)),
    ensures private_standard_columns_prefix(context,initial,row,column+1,after,extended),
{
    assert forall|tail|private_standard_columns_run(context,initial,row,0,prefix+tail)==part2_jpip_snapshot_bind(
        private_standard_cell_run(context,current,[column as u32,row],tail),
        |next,rest|private_standard_columns_run(context,next,row,column+1,rest)) by {
        assert(private_standard_columns_run(context,initial,row,0,prefix+tail)==private_standard_columns_run(context,current,row,column,tail));
        reveal_with_fuel(private_standard_columns_run,1);
    }
    part2_decode_prefix_advance(|events|private_standard_columns_run(context,initial,row,0,events),
        |events|private_standard_cell_run(context,current,[column as u32,row],events),
        |next,rest|private_standard_columns_run(context,next,row,column+1,rest),prefix,after)
}

pub(crate) proof fn private_standard_column_error(context:PrivateStandardBlockContext,initial:PrivateStandardBlocksState,
    row:u32,column:nat,current:PrivateStandardBlocksState,prefix:Seq<Part2JpipSnapshotEvent>,error:crate::DecodeError)
    requires column<context.lattice.blocks[0],private_standard_columns_prefix(context,initial,row,column,current,prefix),
        part2_cold_framed(|events|private_standard_cell_run(context,current,[column as u32,row],events),Err(error)),
    ensures part2_cold_framed(|events|private_standard_columns_run(context,initial,row,0,events),Err(error)),
{
    assert forall|tail|private_standard_columns_run(context,initial,row,0,prefix+tail)==part2_jpip_snapshot_bind(
        private_standard_cell_run(context,current,[column as u32,row],tail),
        |next,rest|private_standard_columns_run(context,next,row,column+1,rest)) by {
        assert(private_standard_columns_run(context,initial,row,0,prefix+tail)==private_standard_columns_run(context,current,row,column,tail));
        reveal_with_fuel(private_standard_columns_run,1);
    }
    part2_decode_prefix_error(|events|private_standard_columns_run(context,initial,row,0,events),
        |events|private_standard_cell_run(context,current,[column as u32,row],events),
        |next,rest|private_standard_columns_run(context,next,row,column+1,rest),prefix,error);
}

pub(crate) proof fn private_standard_columns_finish(context:PrivateStandardBlockContext,initial:PrivateStandardBlocksState,
    row:u32,current:PrivateStandardBlocksState,prefix:Seq<Part2JpipSnapshotEvent>)
    requires private_standard_columns_prefix(context,initial,row,context.lattice.blocks[0] as nat,current,prefix),
    ensures part2_cold_framed(|events|private_standard_columns_run(context,initial,row,0,events),Ok(current)),
{
    assert forall|tail|private_standard_columns_run(context,initial,row,0,prefix+tail)==Some((Ok(current),tail)) by {
        assert(private_standard_columns_run(context,initial,row,0,prefix+tail)==
            private_standard_columns_run(context,current,row,context.lattice.blocks[0] as nat,tail));
        reveal_with_fuel(private_standard_columns_run,1);
    }
    assert(part2_cold_prefix(|events|private_standard_columns_run(context,initial,row,0,events),prefix,Ok(current)));
}

pub(crate) proof fn private_standard_row_advance(context:PrivateStandardBlockContext,initial:PrivateStandardBlocksState,
    row:nat,current:PrivateStandardBlocksState,prefix:Seq<Part2JpipSnapshotEvent>,after:PrivateStandardBlocksState)
    ->(extended:Seq<Part2JpipSnapshotEvent>)
    requires row<context.lattice.blocks[1],private_standard_rows_prefix(context,initial,row,current,prefix),
        part2_cold_framed(|events|private_standard_columns_run(context,current,row as u32,0,events),Ok(after)),
    ensures private_standard_rows_prefix(context,initial,row+1,after,extended),
{
    assert forall|tail|private_standard_rows_run(context,initial,0,prefix+tail)==part2_jpip_snapshot_bind(
        private_standard_columns_run(context,current,row as u32,0,tail),
        |next,rest|private_standard_rows_run(context,next,row+1,rest)) by {
        assert(private_standard_rows_run(context,initial,0,prefix+tail)==private_standard_rows_run(context,current,row,tail));
        reveal_with_fuel(private_standard_rows_run,1);
    }
    part2_decode_prefix_advance(|events|private_standard_rows_run(context,initial,0,events),
        |events|private_standard_columns_run(context,current,row as u32,0,events),
        |next,rest|private_standard_rows_run(context,next,row+1,rest),prefix,after)
}

pub(crate) proof fn private_standard_row_error(context:PrivateStandardBlockContext,initial:PrivateStandardBlocksState,
    row:nat,current:PrivateStandardBlocksState,prefix:Seq<Part2JpipSnapshotEvent>,error:crate::DecodeError)
    requires row<context.lattice.blocks[1],private_standard_rows_prefix(context,initial,row,current,prefix),
        part2_cold_framed(|events|private_standard_columns_run(context,current,row as u32,0,events),Err(error)),
    ensures part2_cold_framed(|events|private_standard_rows_run(context,initial,0,events),Err(error)),
{
    assert forall|tail|private_standard_rows_run(context,initial,0,prefix+tail)==part2_jpip_snapshot_bind(
        private_standard_columns_run(context,current,row as u32,0,tail),
        |next,rest|private_standard_rows_run(context,next,row+1,rest)) by {
        assert(private_standard_rows_run(context,initial,0,prefix+tail)==private_standard_rows_run(context,current,row,tail));
        reveal_with_fuel(private_standard_rows_run,1);
    }
    part2_decode_prefix_error(|events|private_standard_rows_run(context,initial,0,events),
        |events|private_standard_columns_run(context,current,row as u32,0,events),
        |next,rest|private_standard_rows_run(context,next,row+1,rest),prefix,error);
}

pub(crate) proof fn private_standard_rows_finish(context:PrivateStandardBlockContext,initial:PrivateStandardBlocksState,
    current:PrivateStandardBlocksState,prefix:Seq<Part2JpipSnapshotEvent>)
    requires private_standard_rows_prefix(context,initial,context.lattice.blocks[1] as nat,current,prefix),
    ensures part2_cold_framed(|events|private_standard_rows_run(context,initial,0,events),Ok(current)),
{
    assert forall|tail|private_standard_rows_run(context,initial,0,prefix+tail)==Some((Ok(current),tail)) by {
        assert(private_standard_rows_run(context,initial,0,prefix+tail)==
            private_standard_rows_run(context,current,context.lattice.blocks[1] as nat,tail));
        reveal_with_fuel(private_standard_rows_run,1);
    }
    assert(part2_cold_prefix(|events|private_standard_rows_run(context,initial,0,events),prefix,Ok(current)));
}

pub(crate) proof fn private_standard_blocks_rows_observed(context:PrivateStandardBlockContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,first:usize,total:u64,limits:&crate::ResourceLimits,
    capacity:usize,next:u64,result:Result<PrivateStandardBlocksState,crate::DecodeError>)
    requires private_standard_blocks_admit(context,total,limits)==Ok((capacity,next)),
        part2_cold_framed(|events|private_standard_blocks_capacity_run(context,capacity,events),Ok(())),
        part2_cold_framed(|events|private_standard_rows_run(context,private_standard_blocks_initial(placements,first,next),0,events),result),
    ensures part2_cold_framed(|events|private_standard_blocks_run(context,placements,first,total,limits,events),result),
{
    part2_decode_eta(|events|private_standard_rows_run(context,private_standard_blocks_initial(placements,first,next),0,events),result);
    part2_cold_bind(|events|private_standard_blocks_capacity_run(context,capacity,events),
        |_:(),rest|private_standard_rows_run(context,private_standard_blocks_initial(placements,first,next),0,rest),Ok(()),result);
}

pub struct PrivateStandardPrecinctContext {
    pub component:u16,
    pub band:[u32;4],pub block:[u32;2],pub subbands:Seq<crate::decode::SubbandGeometry>,
    pub range:(usize,usize),pub style:crate::tier1::Tier1CodingStyle,
    pub allowed:bool,pub bound:u8,pub location:(u8,u32,usize),pub limits:crate::ResourceLimits,
}

pub struct PrivateStandardPrecinctBuffers {
    pub executions:Seq<PrivateHtExecutionState>,
    pub placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    pub next:usize,pub total:u64,
}

pub struct PrivateStandardPlannedPrecinct {
    pub precinct:PrivateHtPrecinctState,
    pub placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,pub total:u64,
}

pub struct PrivateStandardComponentBuffers {
    pub precincts:Seq<PrivateHtPrecinctState>,
    pub placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,pub total:u64,
}

pub struct PrivateStandardPlanContext {
    pub component:u16,
    pub size:crate::codestream::ImageSize,pub tile:u16,pub first:Part2OwnedTilePart,
    pub caps:Option<(u32,Seq<u16>)>,pub limits:crate::ResourceLimits,
}

pub struct PrivateStandardPlanState {
    pub components:Seq<Part1PreparePlan>,pub grid:Part1PacketGrid,pub precincts:Seq<PrivateHtPrecinctState>,
}

pub struct PrivateStandardPlannedComponent {
    pub component:Part1PreparePlan,pub precincts:Seq<PrivateHtPrecinctState>,pub total:u64,
}

pub struct PrivateStandardTileBuffers {
    pub components:Seq<Part1PreparePlan>,pub precincts:Seq<PrivateHtPrecinctState>,pub total:u64,
}

pub(crate) open spec fn private_standard_precinct_buffers_public(before:PrivateStandardPrecinctBuffers)->Part2PrecinctPlanBuilder {
    Part2PrecinctPlanBuilder {executions:private_executions_public(before.executions),placements:before.placements,
        decoder_index:before.next,planned_code_blocks:before.total}
}

pub(crate) open spec fn private_standard_component_buffers_public(before:PrivateStandardComponentBuffers)->Part2ComponentPlanBuffers {
    Part2ComponentPlanBuffers {precincts:private_precincts_logical(before.precincts),placements:before.placements,planned_code_blocks:before.total}
}

pub(crate) open spec fn private_standard_precinct_initial_context(context:PrivateStandardPrecinctContext,
    before:PrivateStandardPrecinctBuffers)->PrivateResolutionInitialContext {
    PrivateResolutionInitialContext {
        component:context.component,resolution:context.location.0,precinct:context.location.1,style:context.style,
        executions:before.executions,limits:context.limits,
    }
}

pub(crate) open spec fn private_standard_band_context(context:PrivateStandardPrecinctContext,index:usize,
    geometry:crate::decode::SubbandGeometry,lattice:Part2PlannedSubbandLattice)->PrivateStandardBlockContext {
    PrivateStandardBlockContext {lattice,geometry,style:context.style,allowed:context.allowed,bound:context.bound,
        indices:(context.location.2,index)}
}

pub(crate) open spec fn private_standard_after_band(before:PrivateStandardPrecinctBuffers,geometry:crate::decode::SubbandGeometry,
    lattice:Part2PlannedSubbandLattice,blocks:PrivateStandardBlocksState)->PrivateStandardPrecinctBuffers {
    PrivateStandardPrecinctBuffers {
        executions:before.executions.push(PrivateHtExecutionState {
            orientation:geometry.orientation,across:lattice.blocks[0],down:lattice.blocks[1],
            maximum_zero:geometry.significant_bitplanes,decoders:blocks.blocks,
        }),
        placements:blocks.placements,next:blocks.next,total:blocks.total,
    }
}

pub(crate) open spec fn private_standard_band_value(context:PrivateStandardPrecinctContext,local:nat,
    before:PrivateStandardPrecinctBuffers)->Result<PrivateStandardPrecinctBuffers,crate::DecodeError> {
    let index=context.range.0 as nat+local;
    if index>usize::MAX{Err(part1_block_placement_error(true))}
    else if index>=context.subbands.len(){Err(part1_block_placement_error(false))}
    else{let geometry=context.subbands[index as int];
        match part2_planned_subband_lattice(context.band,context.block,geometry){
            Err(error)=>Err(error),Ok(None)=>Ok(before),
            Ok(Some(lattice))=>match private_standard_blocks_value(private_standard_band_context(context,index as usize,geometry,lattice),
                before.placements,before.next,before.total,&context.limits){
                Err(error)=>Err(error),Ok(blocks)=>Ok(private_standard_after_band(before,geometry,lattice,blocks)),
            },
        }
    }
}

pub(crate) open spec fn private_standard_band_run(context:PrivateStandardPrecinctContext,local:nat,
    before:PrivateStandardPrecinctBuffers,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardPrecinctBuffers> {
    let index=context.range.0 as nat+local;
    if index>usize::MAX{Some((Err(part1_block_placement_error(true)),events))}
    else if index>=context.subbands.len(){Some((Err(part1_block_placement_error(false)),events))}
    else{let geometry=context.subbands[index as int];
        match part2_planned_subband_lattice(context.band,context.block,geometry){
            Err(error)=>Some((Err(error),events)),Ok(None)=>Some((Ok(before),events)),
            Ok(Some(lattice))=>part2_jpip_snapshot_bind(private_standard_blocks_run(private_standard_band_context(context,index as usize,geometry,lattice),
                before.placements,before.next,before.total,&context.limits,events),
                |blocks:PrivateStandardBlocksState,rest|Some((Ok(private_standard_after_band(before,geometry,lattice,blocks)),rest))),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_bands_value(context:PrivateStandardPrecinctContext,local:nat,
    before:PrivateStandardPrecinctBuffers)->Result<PrivateStandardPlannedPrecinct,crate::DecodeError>
    decreases context.range.1 as nat-local,
{
    if local>=context.range.1{
        match private_resolution_initial_value(private_standard_precinct_initial_context(context,before)){
            Err(error)=>Err(error),Ok(precinct)=>Ok(PrivateStandardPlannedPrecinct {precinct,placements:before.placements,total:before.total}),
        }
    }else{match private_standard_band_value(context,local,before){
        Err(error)=>Err(error),Ok(after)=>private_standard_bands_value(context,local+1,after),
    }}
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_bands_run(context:PrivateStandardPrecinctContext,local:nat,
    before:PrivateStandardPrecinctBuffers,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardPlannedPrecinct>
    decreases context.range.1 as nat-local,
{
    if local>=context.range.1{
        part2_jpip_snapshot_bind(private_resolution_initial_run(private_standard_precinct_initial_context(context,before),events),
            |precinct:PrivateHtPrecinctState,rest|Some((Ok(PrivateStandardPlannedPrecinct {precinct,placements:before.placements,total:before.total}),rest)))
    }else{part2_jpip_snapshot_bind(private_standard_band_run(context,local,before,events),
        |after,rest|private_standard_bands_run(context,local+1,after,rest))}
}

pub(crate) open spec fn private_standard_executions_run(context:PrivateStandardPrecinctContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    if context.range.1==0{Some((Ok(()),events))}
    else{private_owner_capacity_run(PrivateOwnerCapacityContext::StandardExecutions {context,placements,total},events)}
}

pub(crate) proof fn private_standard_executions_observed(context:PrivateStandardPrecinctContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,response:Result<(),crate::DecodeError>)
    requires if context.range.1==0{response==Ok(())}else{
        private_owner_capacity_result(PrivateOwnerCapacityContext::StandardExecutions {context,placements,total},response)},
    ensures part2_cold_framed(|events|private_standard_executions_run(context,placements,total,events),response),
{
    if context.range.1==0{part2_cold_pure(response);}
    else{part2_cold_framed_extensional(|events|private_owner_capacity_run(PrivateOwnerCapacityContext::StandardExecutions {context,placements,total},events),
        |events|private_standard_executions_run(context,placements,total,events),response);}
}

pub(crate) open spec fn private_standard_precinct_value(context:PrivateStandardPrecinctContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64)->Result<PrivateStandardPlannedPrecinct,crate::DecodeError> {
    private_standard_bands_value(context,0,PrivateStandardPrecinctBuffers {executions:Seq::empty(),placements,next:0,total})
}

pub(crate) open spec fn private_standard_precinct_run(context:PrivateStandardPrecinctContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardPlannedPrecinct> {
    part2_jpip_snapshot_bind(private_standard_executions_run(context,placements,total,events),
        |_:(),rest|private_standard_bands_run(context,0,
            PrivateStandardPrecinctBuffers {executions:Seq::empty(),placements,next:0,total},rest))
}

pub(crate) open spec fn private_standard_precinct_context(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,origin:[u32;2],resolution:u8,precinct:u32,index:usize)->PrivateStandardPrecinctContext {
    PrivateStandardPrecinctContext {
        component:context.component,
        band:[origin[0],origin[1],data.band_size[0],data.band_size[1]],block:data.block_size,subbands:metadata.subbands,
        range:(data.first_subband,data.subband_count),style:metadata.tier1_style,
        allowed:part2_profile_multiple_sets(context.caps),bound:part2_profile_magnitude_bound(context.caps),
        location:(resolution,precinct,index),limits:context.limits,
    }
}

pub(crate) open spec fn private_standard_after_precinct(before:PrivateStandardComponentBuffers,
    row:PrivateStandardPlannedPrecinct)->PrivateStandardComponentBuffers {
    PrivateStandardComponentBuffers {precincts:before.precincts.push(row.precinct),placements:row.placements,total:row.total}
}

pub(crate) open spec fn private_standard_precinct_step_value(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,precinct:u32,before:PrivateStandardComponentBuffers)
    ->Result<PrivateStandardComponentBuffers,crate::DecodeError> {
    match part2_planned_precinct_origin(data.first_precinct,data.geometry.precincts_across,precinct,data.band_size){
        Err(error)=>Err(error),
        Ok(origin)=>match private_standard_precinct_value(private_standard_precinct_context(context,metadata,data,origin,resolution,precinct,before.precincts.len() as usize),
            before.placements,before.total){
            Err(error)=>Err(error),Ok(row)=>Ok(private_standard_after_precinct(before,row)),
        },
    }
}

pub(crate) open spec fn private_standard_precinct_step_run(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,precinct:u32,before:PrivateStandardComponentBuffers,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardComponentBuffers> {
    match part2_planned_precinct_origin(data.first_precinct,data.geometry.precincts_across,precinct,data.band_size){
        Err(error)=>Some((Err(error),events)),
        Ok(origin)=>part2_jpip_snapshot_bind(private_standard_precinct_run(
            private_standard_precinct_context(context,metadata,data,origin,resolution,precinct,before.precincts.len() as usize),
            before.placements,before.total,events),|row:PrivateStandardPlannedPrecinct,rest|
                part2_jpip_snapshot_bind(private_owner_capacity_run(PrivateOwnerCapacityContext::ResolutionAppend {
                    source:before.precincts,next:row.precinct,
                },rest),|_:(),tail|Some((Ok(private_standard_after_precinct(before,row)),tail)))),
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_precincts_value(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,precinct:nat,before:PrivateStandardComponentBuffers)
    ->Result<PrivateStandardComponentBuffers,crate::DecodeError>
    decreases data.precincts_in_resolution as nat-precinct,
{
    if precinct>=data.precincts_in_resolution{Ok(before)}
    else{match private_standard_precinct_step_value(context,metadata,data,resolution,precinct as u32,before){
        Err(error)=>Err(error),Ok(after)=>private_standard_precincts_value(context,metadata,data,resolution,precinct+1,after),
    }}
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_precincts_run(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,precinct:nat,before:PrivateStandardComponentBuffers,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardComponentBuffers>
    decreases data.precincts_in_resolution as nat-precinct,
{
    if precinct>=data.precincts_in_resolution{Some((Ok(before),events))}
    else{part2_jpip_snapshot_bind(private_standard_precinct_step_run(context,metadata,data,resolution,precinct as u32,before,events),
        |after,rest|private_standard_precincts_run(context,metadata,data,resolution,precinct+1,after,rest))}
}

pub(crate) open spec fn private_standard_resolution_value(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    resolution:u8,before:PrivateStandardComponentBuffers)->Result<PrivateStandardComponentBuffers,crate::DecodeError> {
    match part2_resolution_plan_metadata(&context.size,metadata.coding_style,context.component,(context.tile,resolution),[metadata.bounds.x0,metadata.bounds.y0]){
        Err(error)=>Err(error),
        Ok(data)=>private_standard_precincts_value(context,metadata,data,resolution,0,before),
    }
}

pub(crate) open spec fn private_standard_resolution_run(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    resolution:u8,before:PrivateStandardComponentBuffers,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardComponentBuffers> {
    match part2_resolution_plan_metadata(&context.size,metadata.coding_style,context.component,(context.tile,resolution),[metadata.bounds.x0,metadata.bounds.y0]){
        Err(error)=>Some((Err(error),events)),
        Ok(data)=>private_standard_precincts_run(context,metadata,data,resolution,0,before,events),
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_resolutions_value(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    resolution:nat,before:PrivateStandardComponentBuffers)->Result<PrivateStandardComponentBuffers,crate::DecodeError>
    decreases metadata.coding_style.decomposition_levels as nat+1-resolution,
{
    if resolution>metadata.coding_style.decomposition_levels{Ok(before)}
    else{match private_standard_resolution_value(context,metadata,resolution as u8,before){
        Err(error)=>Err(error),Ok(after)=>if resolution==u8::MAX{Err(part1_block_placement_error(true))}
            else{private_standard_resolutions_value(context,metadata,resolution+1,after)},
    }}
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_resolutions_run(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    resolution:nat,before:PrivateStandardComponentBuffers,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardComponentBuffers>
    decreases metadata.coding_style.decomposition_levels as nat+1-resolution,
{
    if resolution>metadata.coding_style.decomposition_levels{Some((Ok(before),events))}
    else{part2_jpip_snapshot_bind(private_standard_resolution_run(context,metadata,resolution as u8,before,events),
        |after,rest|if resolution==u8::MAX{Some((Err(part1_block_placement_error(true)),rest))}
            else{private_standard_resolutions_run(context,metadata,resolution+1,after,rest)})}
}

pub(crate) open spec fn private_standard_component_initial(precincts:Seq<PrivateHtPrecinctState>,total:u64)
    ->PrivateStandardComponentBuffers {
    PrivateStandardComponentBuffers {precincts,placements:Seq::empty(),total}
}

pub(crate) open spec fn private_standard_component_finish(context:PrivateStandardPlanContext,
    metadata:Part2ComponentPlanMetadata,buffers:PrivateStandardComponentBuffers)->PrivateStandardPlannedComponent {
    PrivateStandardPlannedComponent {
        component:Part1PreparePlan {component:context.component,x:metadata.x,y:metadata.y,width:metadata.width,height:metadata.height,
            resolution:metadata.output_resolution,subbands:metadata.subbands,placements:buffers.placements},
        precincts:buffers.precincts,total:buffers.total,
    }
}

pub(crate) open spec fn private_standard_component_after_metadata(context:PrivateStandardPlanContext,
    precincts:Seq<PrivateHtPrecinctState>,total:u64,metadata:Part2ComponentPlanMetadata,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardPlannedComponent> {
    part2_jpip_snapshot_bind(private_standard_resolutions_run(context,metadata,0,
        private_standard_component_initial(precincts,total),events),
        |after,rest|Some((Ok(private_standard_component_finish(context,metadata,after)),rest)))
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_component_run(context:PrivateStandardPlanContext,
    precincts:Seq<PrivateHtPrecinctState>,total:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardPlannedComponent> {
    let first=context.first;
    part2_jpip_snapshot_bind(part2_component_metadata_run(&context.size,&first.component_coding_styles,
        first.component_quantizations,&first.roi_shifts,context.component,(context.tile,0),part2_profile_force_ht(context.caps),events),
        |metadata,rest|private_standard_component_after_metadata(context,precincts,total,metadata,rest))
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_component_value(context:PrivateStandardPlanContext,
    precincts:Seq<PrivateHtPrecinctState>,total:u64)->Result<PrivateStandardPlannedComponent,crate::DecodeError> {
    let first=context.first;
    match part2_component_plan_metadata_owned(&context.size,&first.component_coding_styles,
        first.component_quantizations,&first.roi_shifts,context.component,(context.tile,0),part2_profile_force_ht(context.caps)){
        Err(error)=>Err(error),
        Ok(metadata)=>match private_standard_resolutions_value(context,metadata,0,private_standard_component_initial(precincts,total)){
            Err(error)=>Err(error),Ok(after)=>Ok(private_standard_component_finish(context,metadata,after)),
        },
    }
}

pub(crate) open spec fn private_standard_component_result(context:PrivateStandardPlanContext,
    precincts:Seq<PrivateHtPrecinctState>,total:u64,result:Result<PrivateStandardPlannedComponent,crate::DecodeError>)->bool {
    part2_cold_framed(|events|private_standard_component_run(context,precincts,total,events),result)
}

pub(crate) open spec fn private_standard_planned_component_public(row:PrivateStandardPlannedComponent)->Part2PlannedComponent {
    Part2PlannedComponent {component:row.component,precincts:private_precincts_logical(row.precincts),planned_code_blocks:row.total}
}

pub(crate) open spec fn private_standard_tile_buffers_public(before:PrivateStandardTileBuffers)->Part2TilePlanBuffers {
    Part2TilePlanBuffers {components:before.components,precincts:private_precincts_logical(before.precincts),planned_code_blocks:before.total}
}

pub(crate) open spec fn private_standard_tile_initial()->PrivateStandardTileBuffers {
    PrivateStandardTileBuffers {components:Seq::empty(),precincts:Seq::empty(),total:0}
}

pub(crate) open spec fn private_standard_tile_after_component(before:PrivateStandardTileBuffers,row:PrivateStandardPlannedComponent)
    ->PrivateStandardTileBuffers {
    PrivateStandardTileBuffers {components:before.components.push(row.component),precincts:row.precincts,total:row.total}
}

pub(crate) open spec fn private_standard_tile_finish(grid:Part1PacketGrid,buffers:PrivateStandardTileBuffers)->PrivateStandardPlanState {
    PrivateStandardPlanState {grid,components:buffers.components,precincts:buffers.precincts}
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_components_run(context:PrivateStandardPlanContext,grid:Part1PacketGrid,
    component:u16,before:PrivateStandardTileBuffers,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardPlanState>
    decreases crate::codestream::image_size_component_count(&context.size) as nat-component as nat,
{
    if component>=crate::codestream::image_size_component_count(&context.size){
        Some((Ok(private_standard_tile_finish(grid,before)),events))
    }else{
        part2_jpip_snapshot_bind(private_standard_component_run(PrivateStandardPlanContext {component,..context},
            before.precincts,before.total,events),
            |row,rest|private_standard_components_run(context,grid,(component+1) as u16,
                private_standard_tile_after_component(before,row),rest))
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_standard_components_value(context:PrivateStandardPlanContext,grid:Part1PacketGrid,
    component:u16,before:PrivateStandardTileBuffers)->Result<PrivateStandardPlanState,crate::DecodeError>
    decreases crate::codestream::image_size_component_count(&context.size) as nat-component as nat,
{
    if component>=crate::codestream::image_size_component_count(&context.size){Ok(private_standard_tile_finish(grid,before))}
    else{match private_standard_component_value(PrivateStandardPlanContext {component,..context},before.precincts,before.total){
        Err(error)=>Err(error),Ok(row)=>private_standard_components_value(context,grid,(component+1) as u16,
            private_standard_tile_after_component(before,row)),
    }}
}

pub(crate) open spec fn private_standard_component_capacity(context:PrivateStandardPlanContext)->Part2ComponentCapacityContext {
    part2_component_owner_context(&context.size,context.first.coding_style,&context.first.component_coding_styles,
        context.first.component_quantizations,&context.first.roi_shifts,(context.tile,0),private_standard_policy(context))
}

pub(crate) open spec fn private_standard_plan_after_grid(context:PrivateStandardPlanContext,grid:Part1PacketGrid,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardPlanState> {
    part2_jpip_snapshot_bind(part2_component_capacity_run(private_standard_component_capacity(context),events),
        |_:(),rest|private_standard_components_run(context,grid,0,private_standard_tile_initial(),rest))
}

pub(crate) open spec fn private_standard_plan_run(context:PrivateStandardPlanContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateStandardPlanState> {
    match part2_selection_tile_bounds(crate::codestream::selection_geometry_view(&context.size),context.tile){
        Err(error)=>Some((Err(error),events)),
        Ok(_)=>part2_jpip_snapshot_bind(part2_spatial_derived_grid_run(&context.size,&context.first.component_coding_styles,
            context.first.coding_style.layers,&context.limits,Some(context.tile),0,events),
            |grid,rest|private_standard_plan_after_grid(context,grid,rest)),
    }
}

pub(crate) open spec fn private_standard_plan_value(context:PrivateStandardPlanContext)->Result<PrivateStandardPlanState,crate::DecodeError> {
    let first=context.first;
    match part2_selection_tile_bounds(crate::codestream::selection_geometry_view(&context.size),context.tile){
        Err(error)=>Err(error),
        Ok(_)=>match part2_spatial_packet_grid_from_components(&context.size,&first.component_coding_styles,first.coding_style.layers,&context.limits,Some(context.tile),0){
            Err(error)=>Err(error),
            Ok(grid)=>private_standard_components_value(context,grid,0,private_standard_tile_initial()),
        },
    }
}

pub(crate) open spec fn private_standard_plan_result(context:PrivateStandardPlanContext,
    result:Result<PrivateStandardPlanState,crate::DecodeError>)->bool {
    part2_cold_framed(|events|private_standard_plan_run(context,events),result)
}

pub(crate) open spec fn private_standard_plan_public(context:PrivateStandardPlanContext,value:PrivateStandardPlanState)->Part2ProgressionTilePlan {
    private_standard_plan_public_view(value,context.tile,context.first)
}

pub(crate) open spec fn private_standard_plan_public_view(value:PrivateStandardPlanState,tile:u16,first:Part2OwnedTilePart)->Part2ProgressionTilePlan {
    Part2ProgressionTilePlan {
        tile,coding_style:first.coding_style,coding_styles:first.component_coding_styles,
        grid:value.grid,precincts:private_precincts_logical(value.precincts),components:value.components,
    }
}

pub(crate) open spec fn private_standard_planned_precinct_public(value:PrivateStandardPlannedPrecinct)->Part2PlannedPrecinct {
    Part2PlannedPrecinct {precinct:value.precinct.logical,placements:value.placements,planned_code_blocks:value.total}
}

pub(crate) proof fn private_standard_band_reference(context:PrivateStandardPrecinctContext,local:nat,before:PrivateStandardPrecinctBuffers)
    requires local<=usize::MAX,context.style.force_high_throughput,
        matches!(context.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
    ensures match private_standard_band_value(context,local,before){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_precinct_buffers_public(after)),
    }==part2_planned_precinct_subband(context.band,context.block,context.subbands,context.range.0,local as usize,
        context.style,(context.allowed,context.bound,true),context.location.2,true,&context.limits,private_standard_precinct_buffers_public(before)),
{
    let index=context.range.0 as nat+local;
    if index<=usize::MAX && index<context.subbands.len(){
        let geometry=context.subbands[index as int];
        if let Ok(Some(lattice))=part2_planned_subband_lattice(context.band,context.block,geometry){
            let child=private_standard_band_context(context,index as usize,geometry,lattice);
            private_standard_blocks_reference(child,before.placements,before.next,before.total,&context.limits);
            if let Ok(blocks)=private_standard_blocks_value(child,before.placements,before.next,before.total,&context.limits){
                let after=private_standard_after_band(before,geometry,lattice,blocks);
                assert(private_executions_public(after.executions) =~= private_executions_public(before.executions).push(
                    private_execution_public(after.executions.last())));
            }
        }
    }
}

pub(crate) proof fn private_standard_bands_reference(context:PrivateStandardPrecinctContext,local:nat,before:PrivateStandardPrecinctBuffers)
    requires local<=context.range.1,context.style.force_high_throughput,
        matches!(context.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
    ensures match private_standard_bands_value(context,local,before){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_planned_precinct_public(after)),
    }==part2_planned_precinct_rows(context.band,context.block,context.subbands,context.range,context.style,
        (context.allowed,context.bound,true),(context.component,context.location.0,context.location.1,context.location.2),
        true,&context.limits,local,private_standard_precinct_buffers_public(before)),
    decreases context.range.1 as nat-local,
{
    reveal_with_fuel(private_standard_bands_value,1);reveal_with_fuel(part2_planned_precinct_rows,1);
    if local>=context.range.1{
        private_resolution_initial_reference(private_standard_precinct_initial_context(context,before));
    }else{
        private_standard_band_reference(context,local,before);
        if let Ok(after)=private_standard_band_value(context,local,before){
            private_standard_bands_reference(context,local+1,after);
        }
    }
}

pub(crate) proof fn private_standard_precinct_reference(context:PrivateStandardPrecinctContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64)
    requires context.style.force_high_throughput,
        matches!(context.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
    ensures match private_standard_precinct_value(context,placements,total){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_planned_precinct_public(after)),
    }==part2_planned_precinct(context.band,context.block,context.subbands,context.range,context.style,
        (context.allowed,context.bound,true),(context.component,context.location.0,context.location.1,context.location.2),placements,total,true,&context.limits),
{
    let before=PrivateStandardPrecinctBuffers {executions:Seq::empty(),placements,next:0,total};
    assert(private_executions_public(before.executions) =~= Seq::empty());
    private_standard_bands_reference(context,0,before);
}

pub(crate) open spec fn private_standard_policy(context:PrivateStandardPlanContext)->(bool,u8,bool,bool) {
    (part2_profile_multiple_sets(context.caps),part2_profile_magnitude_bound(context.caps),true,true)
}

pub(crate) proof fn private_standard_precinct_step_reference(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,precinct:u32,before:PrivateStandardComponentBuffers)
    requires resolution<=metadata.output_resolution,metadata.tier1_style.force_high_throughput,
        matches!(metadata.tier1_style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
    ensures match private_standard_precinct_step_value(context,metadata,data,resolution,precinct,before){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_component_buffers_public(after)),
    }==part2_component_plan_precinct(context.component,resolution,metadata,data,private_standard_policy(context),&context.limits,precinct,
        private_standard_component_buffers_public(before)),
{
    if let Ok(origin)=part2_planned_precinct_origin(data.first_precinct,data.geometry.precincts_across,precinct,data.band_size){
        let child=private_standard_precinct_context(context,metadata,data,origin,resolution,precinct,before.precincts.len() as usize);
        private_standard_precinct_reference(child,before.placements,before.total);
        if let Ok(row)=private_standard_precinct_value(child,before.placements,before.total){
            assert(private_precincts_logical(before.precincts.push(row.precinct)) =~=
                private_precincts_logical(before.precincts).push(row.precinct.logical));
        }
    }
}

pub(crate) proof fn private_standard_precincts_reference(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,precinct:nat,before:PrivateStandardComponentBuffers)
    requires resolution<=metadata.output_resolution,metadata.tier1_style.force_high_throughput,
        matches!(metadata.tier1_style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
    ensures match private_standard_precincts_value(context,metadata,data,resolution,precinct,before){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_component_buffers_public(after)),
    }==part2_component_plan_precincts(context.component,resolution,metadata,data,private_standard_policy(context),&context.limits,precinct,
        private_standard_component_buffers_public(before)),
    decreases data.precincts_in_resolution as nat-precinct,
{
    reveal_with_fuel(private_standard_precincts_value,1);reveal_with_fuel(part2_component_plan_precincts,1);
    if precinct<data.precincts_in_resolution{
        private_standard_precinct_step_reference(context,metadata,data,resolution,precinct as u32,before);
        if let Ok(after)=private_standard_precinct_step_value(context,metadata,data,resolution,precinct as u32,before){
            private_standard_precincts_reference(context,metadata,data,resolution,precinct+1,after);
        }
    }
}

pub(crate) open spec fn private_standard_component_public(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,before:PrivateStandardComponentBuffers)->Part2PlannedComponent {
    Part2PlannedComponent {
        component:Part1PreparePlan {component:context.component,x:metadata.x,y:metadata.y,width:metadata.width,height:metadata.height,
            resolution:metadata.output_resolution,subbands:metadata.subbands,placements:before.placements},
        precincts:private_precincts_logical(before.precincts),planned_code_blocks:before.total,
    }
}

pub(crate) proof fn private_standard_resolutions_reference(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    resolution:nat,before:PrivateStandardComponentBuffers)
    requires metadata.output_resolution==metadata.coding_style.decomposition_levels,
        metadata.tier1_style.force_high_throughput,matches!(metadata.tier1_style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
    ensures match private_standard_resolutions_value(context,metadata,resolution,before){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_component_public(context,metadata,after)),
    }==part2_component_plan_resolutions(&context.size,context.component,context.tile,metadata,private_standard_policy(context),&context.limits,
        resolution,private_standard_component_buffers_public(before)),
    decreases metadata.coding_style.decomposition_levels as nat+1-resolution,
{
    reveal_with_fuel(private_standard_resolutions_value,1);reveal_with_fuel(part2_component_plan_resolutions,1);
    if resolution<=metadata.coding_style.decomposition_levels{
        if let Ok(data)=part2_resolution_plan_metadata(&context.size,metadata.coding_style,context.component,(context.tile,resolution as u8),
            [metadata.bounds.x0,metadata.bounds.y0]){
            private_standard_precincts_reference(context,metadata,data,resolution as u8,0,before);
            if let Ok(after)=private_standard_precincts_value(context,metadata,data,resolution as u8,0,before){
                if resolution<u8::MAX{private_standard_resolutions_reference(context,metadata,resolution+1,after);}
            }
        }
    }
}

pub(crate) proof fn private_standard_metadata_fields(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata)
    requires private_ht_standard_eligible(&context.size,context.tile,seq![context.first],context.caps,None),
        context.component<crate::codestream::image_size_component_count(&context.size),
        part2_component_plan_metadata_owned(&context.size,&context.first.component_coding_styles,context.first.component_quantizations,
            &context.first.roi_shifts,context.component,(context.tile,0),part2_profile_force_ht(context.caps))==Ok(metadata),
    ensures metadata.output_resolution==metadata.coding_style.decomposition_levels,
        metadata.tier1_style.force_high_throughput,
        matches!(metadata.tier1_style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
        metadata.coding_style==crate::codestream::component_coding_style_result(&context.first.component_coding_styles,context.component).get_Ok_0(),
{
    private_standard_eligible_at(&context.size,context.tile,context.first,context.caps,None,context.component);
    private_standard_component_style_fields(&context.size,context.tile,context.first,context.component);
    let style=crate::codestream::component_coding_style_result(&context.first.component_coding_styles,context.component).get_Ok_0();
    crate::codestream::parsed_coding_style_known_fields(style);
    crate::codestream::parsed_coding_style_known_fields(context.first.coding_style);
    crate::codestream::resolution_selectors_known_fields(style);
}

pub(crate) proof fn private_standard_component_reference(context:PrivateStandardPlanContext,
    precincts:Seq<PrivateHtPrecinctState>,total:u64)
    requires private_ht_standard_eligible(&context.size,context.tile,seq![context.first],context.caps,None),
        context.component<crate::codestream::image_size_component_count(&context.size),
    ensures match private_standard_component_value(context,precincts,total){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_planned_component_public(after)),
    }==part2_planned_component_owned(&context.size,&context.first.component_coding_styles,context.first.component_quantizations,
        &context.first.roi_shifts,context.component,(context.tile,0),private_standard_policy(context),
        private_precincts_logical(precincts),total,&context.limits),
{
    reveal(private_standard_component_value);
    if let Ok(metadata)=part2_component_plan_metadata_owned(&context.size,&context.first.component_coding_styles,
        context.first.component_quantizations,&context.first.roi_shifts,context.component,(context.tile,0),part2_profile_force_ht(context.caps)){
        private_standard_metadata_fields(context,metadata);
        private_standard_resolutions_reference(context,metadata,0,private_standard_component_initial(precincts,total));
    }
}

pub(crate) proof fn private_standard_components_reference(context:PrivateStandardPlanContext,grid:Part1PacketGrid,
    component:u16,before:PrivateStandardTileBuffers)
    requires private_ht_standard_eligible(&context.size,context.tile,seq![context.first],context.caps,None),
        component<=crate::codestream::image_size_component_count(&context.size),
    ensures match private_standard_components_value(context,grid,component,before){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_plan_public(context,after)),
    }==part2_tile_plan_components(&context.size,context.first.coding_style,&context.first.component_coding_styles,
        context.first.component_quantizations,&context.first.roi_shifts,(context.tile,0),private_standard_policy(context),
        &context.limits,grid,component,private_standard_tile_buffers_public(before)),
    decreases crate::codestream::image_size_component_count(&context.size)-component,
{
    reveal_with_fuel(private_standard_components_value,1);reveal_with_fuel(part2_tile_plan_components,1);
    if component<crate::codestream::image_size_component_count(&context.size){
        let current=PrivateStandardPlanContext {component,..context};
        private_standard_component_reference(current,before.precincts,before.total);
        if let Ok(row)=private_standard_component_value(current,before.precincts,before.total){
            private_standard_components_reference(context,grid,(component+1) as u16,private_standard_tile_after_component(before,row));
        }
    }
}

pub(crate) proof fn private_standard_plan_reference(context:PrivateStandardPlanContext)
    requires private_ht_standard_eligible(&context.size,context.tile,seq![context.first],context.caps,None),
    ensures match private_standard_plan_value(context){
        Err(error)=>Err(error),Ok(after)=>Ok(private_standard_plan_public(context,after)),
    }==part2_progression_tile_plan_owned(&context.size,context.first.coding_style,&context.first.component_coding_styles,
        context.first.component_quantizations,&context.first.roi_shifts,(context.tile,0),private_standard_policy(context),&context.limits),
{
    crate::codestream::selection_geometry_known_fields(&context.size);
    assert(private_precincts_logical(Seq::empty()) =~= Seq::<Part1PacketPrecinctState>::empty());
    if let Ok(grid)=part2_spatial_packet_grid_from_components(&context.size,&context.first.component_coding_styles,
        context.first.coding_style.layers,&context.limits,Some(context.tile),0){
        private_standard_components_reference(context,grid,0,private_standard_tile_initial());
    }
}

pub(crate) proof fn private_standard_columns_fields(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,
    row:u32,column:nat)
    requires private_standard_blocks_wf(before),
    ensures match private_standard_columns_value(context,before,row,column){Err(_)=>true,Ok(after)=>private_standard_blocks_wf(after)},
    decreases context.lattice.blocks[0] as nat-column,
{
    reveal_with_fuel(private_standard_columns_value,1);
    if column<context.lattice.blocks[0]{
        if let Ok(after)=private_standard_cell_value(context,before,[column as u32,row]){
            private_standard_cell_fields(context,before,[column as u32,row],after);
            private_standard_columns_fields(context,after,row,column+1);
        }
    }
}

pub(crate) proof fn private_standard_rows_fields(context:PrivateStandardBlockContext,before:PrivateStandardBlocksState,row:nat)
    requires private_standard_blocks_wf(before),
    ensures match private_standard_rows_value(context,before,row){Err(_)=>true,Ok(after)=>private_standard_blocks_wf(after)},
    decreases context.lattice.blocks[1] as nat-row,
{
    reveal_with_fuel(private_standard_rows_value,1);
    if row<context.lattice.blocks[1]{
        private_standard_columns_fields(context,before,row as u32,0);
        if let Ok(after)=private_standard_columns_value(context,before,row as u32,0){
            private_standard_rows_fields(context,after,row+1);
        }
    }
}

pub(crate) proof fn private_standard_blocks_fields(context:PrivateStandardBlockContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,first:usize,total:u64,limits:&crate::ResourceLimits)
    ensures match private_standard_blocks_value(context,placements,first,total,limits){Err(_)=>true,Ok(after)=>private_standard_blocks_wf(after)},
{
    if let Ok((_,next))=private_standard_blocks_admit(context,total,limits){
        private_standard_rows_fields(context,private_standard_blocks_initial(placements,first,next),0);
    }
}

pub(crate) open spec fn private_standard_precinct_buffers_wf(before:PrivateStandardPrecinctBuffers)->bool {
    forall|i:int|0<=i<before.executions.len() ==> #[trigger] private_execution_wf(before.executions[i])
}

pub(crate) open spec fn private_standard_component_buffers_wf(before:PrivateStandardComponentBuffers)->bool {
    forall|i:int|0<=i<before.precincts.len() ==> #[trigger] private_precinct_wf(before.precincts[i])
}

pub(crate) proof fn private_standard_band_fields(context:PrivateStandardPrecinctContext,local:nat,before:PrivateStandardPrecinctBuffers)
    requires private_standard_precinct_buffers_wf(before),
    ensures match private_standard_band_value(context,local,before){Err(_)=>true,Ok(after)=>
        private_standard_precinct_buffers_wf(after) && after.executions.len()<=before.executions.len()+1},
{
    let index=context.range.0 as nat+local;
    if index<=usize::MAX && index<context.subbands.len(){
        let geometry=context.subbands[index as int];
        if let Ok(Some(lattice))=part2_planned_subband_lattice(context.band,context.block,geometry){
            private_standard_blocks_fields(private_standard_band_context(context,index as usize,geometry,lattice),
                before.placements,before.next,before.total,&context.limits);
        }
    }
}

pub(crate) proof fn private_standard_bands_fields(context:PrivateStandardPrecinctContext,local:nat,before:PrivateStandardPrecinctBuffers)
    requires private_standard_precinct_buffers_wf(before),
    ensures match private_standard_bands_value(context,local,before){Err(_)=>true,Ok(after)=>private_precinct_wf(after.precinct)
        && after.precinct.logical.resolution==context.location.0 && after.precinct.logical.precinct==context.location.1},
    decreases context.range.1 as nat-local,
{
    reveal_with_fuel(private_standard_bands_value,1);
    if local>=context.range.1{
        private_resolution_initial_fields(private_standard_precinct_initial_context(context,before));
    }else{
        private_standard_band_fields(context,local,before);
        if let Ok(after)=private_standard_band_value(context,local,before){private_standard_bands_fields(context,local+1,after);}
    }
}

pub(crate) proof fn private_standard_precinct_fields(context:PrivateStandardPrecinctContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64)
    ensures match private_standard_precinct_value(context,placements,total){Err(_)=>true,Ok(after)=>private_precinct_wf(after.precinct)
        && after.precinct.logical.resolution==context.location.0 && after.precinct.logical.precinct==context.location.1},
{
    private_standard_bands_fields(context,0,PrivateStandardPrecinctBuffers {executions:Seq::empty(),placements,next:0,total});
}

pub(crate) proof fn private_standard_precincts_fields(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,precinct:nat,before:PrivateStandardComponentBuffers)
    requires private_standard_component_buffers_wf(before),
    ensures match private_standard_precincts_value(context,metadata,data,resolution,precinct,before){Err(_)=>true,Ok(after)=>private_standard_component_buffers_wf(after)},
    decreases data.precincts_in_resolution as nat-precinct,
{
    reveal_with_fuel(private_standard_precincts_value,1);
    if precinct<data.precincts_in_resolution{
        if let Ok(origin)=part2_planned_precinct_origin(data.first_precinct,data.geometry.precincts_across,precinct as u32,data.band_size){
            let child=private_standard_precinct_context(context,metadata,data,origin,resolution,precinct as u32,before.precincts.len() as usize);
            private_standard_precinct_fields(child,before.placements,before.total);
        }
        if let Ok(after)=private_standard_precinct_step_value(context,metadata,data,resolution,precinct as u32,before){
            assert(private_standard_component_buffers_wf(after));
            private_standard_precincts_fields(context,metadata,data,resolution,precinct+1,after);
        }
    }
}

pub(crate) proof fn private_standard_resolutions_fields(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    resolution:nat,before:PrivateStandardComponentBuffers)
    requires private_standard_component_buffers_wf(before),
    ensures match private_standard_resolutions_value(context,metadata,resolution,before){Err(_)=>true,Ok(after)=>private_standard_component_buffers_wf(after)},
    decreases metadata.coding_style.decomposition_levels as nat+1-resolution,
{
    reveal_with_fuel(private_standard_resolutions_value,1);
    if resolution<=metadata.coding_style.decomposition_levels{
        if let Ok(data)=part2_resolution_plan_metadata(&context.size,metadata.coding_style,context.component,(context.tile,resolution as u8),
            [metadata.bounds.x0,metadata.bounds.y0]){
            private_standard_precincts_fields(context,metadata,data,resolution as u8,0,before);
            if let Ok(after)=private_standard_precincts_value(context,metadata,data,resolution as u8,0,before){
                if resolution<u8::MAX{private_standard_resolutions_fields(context,metadata,resolution+1,after);}
            }
        }
    }
}

pub(crate) proof fn private_standard_band_normal(context:PrivateStandardPrecinctContext,local:nat,before:PrivateStandardPrecinctBuffers)
    ensures part2_cold_framed(|events|private_standard_band_run(context,local,before,events),private_standard_band_value(context,local,before)),
{
    let result=private_standard_band_value(context,local,before);
    let index=context.range.0 as nat+local;
    if index>usize::MAX || index>=context.subbands.len(){part2_cold_pure(result);}
    else{
        let geometry=context.subbands[index as int];
        match part2_planned_subband_lattice(context.band,context.block,geometry){
            Err(_)=>part2_cold_pure(result),Ok(None)=>part2_cold_pure(result),
            Ok(Some(lattice))=>{
                let child=private_standard_band_context(context,index as usize,geometry,lattice);
                let blocks=private_standard_blocks_value(child,before.placements,before.next,before.total,&context.limits);
                private_standard_blocks_normal(child,before.placements,before.next,before.total,&context.limits);
                if blocks.is_ok(){part2_cold_pure(result);}
                part2_cold_bind(|events|private_standard_blocks_run(child,before.placements,before.next,before.total,&context.limits,events),
                    |blocks,rest|Some((Ok(private_standard_after_band(before,geometry,lattice,blocks)),rest)),blocks,result);
            },
        }
    }
}

pub(crate) proof fn private_standard_bands_normal(context:PrivateStandardPrecinctContext,local:nat,before:PrivateStandardPrecinctBuffers)
    requires local<=context.range.1,before.executions.len()<=local,
    ensures part2_cold_framed(|events|private_standard_bands_run(context,local,before,events),private_standard_bands_value(context,local,before)),
    decreases context.range.1 as nat-local,
{
    reveal_with_fuel(private_standard_bands_run,1);reveal_with_fuel(private_standard_bands_value,1);
    let result=private_standard_bands_value(context,local,before);
    if local>=context.range.1{
        let child=private_standard_precinct_initial_context(context,before);
        private_resolution_initial_normal(child);
        let value=private_resolution_initial_value(child);
        if value.is_ok(){part2_cold_pure(result);}
        part2_cold_bind(|events|private_resolution_initial_run(child,events),
            |precinct,rest|Some((Ok(PrivateStandardPlannedPrecinct {precinct,placements:before.placements,total:before.total}),rest)),value,result);
    }else{
        let value=private_standard_band_value(context,local,before);
        private_standard_band_normal(context,local,before);
        if let Ok(after)=value{
            private_standard_bands_normal(context,local+1,after);
            part2_decode_eta(|events|private_standard_bands_run(context,local+1,after,events),result);
        }
        part2_cold_bind(|events|private_standard_band_run(context,local,before,events),
            |after,rest|private_standard_bands_run(context,local+1,after,rest),value,result);
    }
}

pub(crate) proof fn private_standard_precinct_normal(context:PrivateStandardPrecinctContext,
    placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64)
    ensures part2_cold_framed(|events|private_standard_precinct_run(context,placements,total,events),
        private_standard_precinct_value(context,placements,total)),
{
    let result=private_standard_precinct_value(context,placements,total);
    if context.range.1==0{part2_cold_pure::<()>(Ok(()));}
    else{private_owner_capacity_observed(PrivateOwnerCapacityContext::StandardExecutions {context,placements,total},Ok(()));}
    private_standard_executions_observed(context,placements,total,Ok(()));
    let before=PrivateStandardPrecinctBuffers {executions:Seq::empty(),placements,next:0,total};
    private_standard_bands_normal(context,0,before);
    part2_decode_eta(|events|private_standard_bands_run(context,0,before,events),result);
    part2_cold_bind(|events|private_standard_executions_run(context,placements,total,events),
        |_:(),rest|private_standard_bands_run(context,0,before,rest),Ok(()),result);
}

pub(crate) proof fn private_standard_precinct_step_normal(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,precinct:u32,before:PrivateStandardComponentBuffers)
    ensures part2_cold_framed(|events|private_standard_precinct_step_run(context,metadata,data,resolution,precinct,before,events),
        private_standard_precinct_step_value(context,metadata,data,resolution,precinct,before)),
{
    let result=private_standard_precinct_step_value(context,metadata,data,resolution,precinct,before);
    match part2_planned_precinct_origin(data.first_precinct,data.geometry.precincts_across,precinct,data.band_size){
        Err(_)=>part2_cold_pure(result),
        Ok(origin)=>{
            let child=private_standard_precinct_context(context,metadata,data,origin,resolution,precinct,before.precincts.len() as usize);
            let value=private_standard_precinct_value(child,before.placements,before.total);
            private_standard_precinct_normal(child,before.placements,before.total);
            if let Ok(row)=value{
                let capacity=PrivateOwnerCapacityContext::ResolutionAppend {source:before.precincts,next:row.precinct};
                private_owner_capacity_observed(capacity,Ok(()));
                part2_cold_pure(result);
                part2_cold_bind(|events|private_owner_capacity_run(capacity,events),
                    |_:(),rest|Some((Ok(private_standard_after_precinct(before,row)),rest)),Ok(()),result);
                part2_decode_eta(|events|part2_jpip_snapshot_bind(private_owner_capacity_run(capacity,events),
                    |_:(),rest|Some((Ok(private_standard_after_precinct(before,row)),rest))),result);
            }
            part2_cold_bind(|events|private_standard_precinct_run(child,before.placements,before.total,events),
                |row:PrivateStandardPlannedPrecinct,rest|part2_jpip_snapshot_bind(private_owner_capacity_run(
                    PrivateOwnerCapacityContext::ResolutionAppend {source:before.precincts,next:row.precinct},rest),
                    |_:(),tail|Some((Ok(private_standard_after_precinct(before,row)),tail))),value,result);
        },
    }
}

pub(crate) proof fn private_standard_precincts_normal(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,precinct:nat,before:PrivateStandardComponentBuffers)
    ensures part2_cold_framed(|events|private_standard_precincts_run(context,metadata,data,resolution,precinct,before,events),
        private_standard_precincts_value(context,metadata,data,resolution,precinct,before)),
    decreases data.precincts_in_resolution as nat-precinct,
{
    reveal_with_fuel(private_standard_precincts_run,1);reveal_with_fuel(private_standard_precincts_value,1);
    let result=private_standard_precincts_value(context,metadata,data,resolution,precinct,before);
    if precinct>=data.precincts_in_resolution{part2_cold_pure(result);}
    else{
        let value=private_standard_precinct_step_value(context,metadata,data,resolution,precinct as u32,before);
        private_standard_precinct_step_normal(context,metadata,data,resolution,precinct as u32,before);
        if let Ok(after)=value{
            private_standard_precincts_normal(context,metadata,data,resolution,precinct+1,after);
            part2_decode_eta(|events|private_standard_precincts_run(context,metadata,data,resolution,precinct+1,after,events),result);
        }
        part2_cold_bind(|events|private_standard_precinct_step_run(context,metadata,data,resolution,precinct as u32,before,events),
            |after,rest|private_standard_precincts_run(context,metadata,data,resolution,precinct+1,after,rest),value,result);
    }
}

pub(crate) proof fn private_standard_resolutions_normal(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    resolution:nat,before:PrivateStandardComponentBuffers)
    ensures part2_cold_framed(|events|private_standard_resolutions_run(context,metadata,resolution,before,events),
        private_standard_resolutions_value(context,metadata,resolution,before)),
    decreases metadata.coding_style.decomposition_levels as nat+1-resolution,
{
    reveal_with_fuel(private_standard_resolutions_run,1);reveal_with_fuel(private_standard_resolutions_value,1);
    let result=private_standard_resolutions_value(context,metadata,resolution,before);
    if resolution>metadata.coding_style.decomposition_levels{part2_cold_pure(result);}
    else{
        let value=private_standard_resolution_value(context,metadata,resolution as u8,before);
        match part2_resolution_plan_metadata(&context.size,metadata.coding_style,context.component,(context.tile,resolution as u8),
            [metadata.bounds.x0,metadata.bounds.y0]){
            Err(_)=>part2_cold_pure(value),
            Ok(data)=>{
                private_standard_precincts_normal(context,metadata,data,resolution as u8,0,before);
                private_standard_resolution_precincts_observed(context,metadata,data,resolution as u8,before,value);
            },
        }
        if let Ok(after)=value{
            if resolution==u8::MAX{part2_cold_pure(result);}
            else{
                private_standard_resolutions_normal(context,metadata,resolution+1,after);
                part2_decode_eta(|events|private_standard_resolutions_run(context,metadata,resolution+1,after,events),result);
            }
        }
        part2_cold_bind(|events|private_standard_resolution_run(context,metadata,resolution as u8,before,events),
            |after,rest|if resolution==u8::MAX{Some((Err(part1_block_placement_error(true)),rest))}
                else{private_standard_resolutions_run(context,metadata,resolution+1,after,rest)},value,result);
    }
}

pub(crate) proof fn private_standard_component_normal(context:PrivateStandardPlanContext,
    precincts:Seq<PrivateHtPrecinctState>,total:u64)
    ensures private_standard_component_result(context,precincts,total,private_standard_component_value(context,precincts,total)),
{
    reveal(private_standard_component_value);reveal(private_standard_component_run);
    reveal(part2_component_metadata_result);
    let first=context.first;
    let result=private_standard_component_value(context,precincts,total);
    let metadata_result=part2_component_plan_metadata_owned(&context.size,&first.component_coding_styles,
        first.component_quantizations,&first.roi_shifts,context.component,(context.tile,0),part2_profile_force_ht(context.caps));
    part2_component_metadata_normal(&context.size,&first.component_coding_styles,first.component_quantizations,
        &first.roi_shifts,context.component,(context.tile,0),part2_profile_force_ht(context.caps));
    if let Ok(metadata)=metadata_result{
        let before=private_standard_component_initial(precincts,total);
        let value=private_standard_resolutions_value(context,metadata,0,before);
        private_standard_resolutions_normal(context,metadata,0,before);
        if value.is_ok(){part2_cold_pure(result);}
        part2_cold_bind(|events|private_standard_resolutions_run(context,metadata,0,before,events),
            |after,rest|Some((Ok(private_standard_component_finish(context,metadata,after)),rest)),value,result);
        part2_decode_eta(|events|private_standard_component_after_metadata(context,precincts,total,metadata,events),result);
    }
    part2_cold_bind(|events|part2_component_metadata_run(&context.size,&first.component_coding_styles,first.component_quantizations,
        &first.roi_shifts,context.component,(context.tile,0),part2_profile_force_ht(context.caps),events),
        |metadata,rest|private_standard_component_after_metadata(context,precincts,total,metadata,rest),metadata_result,result);
}

pub(crate) proof fn private_standard_components_normal(context:PrivateStandardPlanContext,grid:Part1PacketGrid,
    component:u16,before:PrivateStandardTileBuffers)
    ensures part2_cold_framed(|events|private_standard_components_run(context,grid,component,before,events),
        private_standard_components_value(context,grid,component,before)),
    decreases crate::codestream::image_size_component_count(&context.size) as nat-component as nat,
{
    reveal_with_fuel(private_standard_components_run,1);reveal_with_fuel(private_standard_components_value,1);
    let result=private_standard_components_value(context,grid,component,before);
    if component>=crate::codestream::image_size_component_count(&context.size){part2_cold_pure(result);}
    else{
        let current=PrivateStandardPlanContext {component,..context};
        let value=private_standard_component_value(current,before.precincts,before.total);
        private_standard_component_normal(current,before.precincts,before.total);
        if let Ok(row)=value{
            private_standard_components_normal(context,grid,(component+1) as u16,private_standard_tile_after_component(before,row));
            part2_decode_eta(|events|private_standard_components_run(context,grid,(component+1) as u16,
                private_standard_tile_after_component(before,row),events),result);
        }
        part2_cold_bind(|events|private_standard_component_run(current,before.precincts,before.total,events),
            |row,rest|private_standard_components_run(context,grid,(component+1) as u16,
                private_standard_tile_after_component(before,row),rest),value,result);
    }
}

pub(crate) proof fn private_standard_plan_normal(context:PrivateStandardPlanContext)
    ensures private_standard_plan_result(context,private_standard_plan_value(context)),
{
    reveal(part2_spatial_derived_grid_result);reveal(part2_component_metadata_result);reveal(part2_component_capacity_result);
    let result=private_standard_plan_value(context);
    let first=context.first;
    match part2_selection_tile_bounds(crate::codestream::selection_geometry_view(&context.size),context.tile){
        Err(_)=>part2_cold_pure(result),
        Ok(_)=>{
            let grid_result=part2_spatial_packet_grid_from_components(&context.size,&first.component_coding_styles,
                first.coding_style.layers,&context.limits,Some(context.tile),0);
            part2_spatial_derived_grid_normal(&context.size,&first.component_coding_styles,first.coding_style.layers,&context.limits,Some(context.tile),0);
            if let Ok(grid)=grid_result{
                let capacity=private_standard_component_capacity(context);
                part2_component_capacity_observed(capacity,Ok(()));
                private_standard_components_normal(context,grid,0,private_standard_tile_initial());
                assert(result==private_standard_components_value(context,grid,0,private_standard_tile_initial()));
                part2_decode_eta(|events|private_standard_components_run(context,grid,0,private_standard_tile_initial(),events),result);
                part2_cold_bind(|events|part2_component_capacity_run(capacity,events),
                    |_:(),rest|private_standard_components_run(context,grid,0,private_standard_tile_initial(),rest),Ok(()),result);
                part2_decode_eta(|events|private_standard_plan_after_grid(context,grid,events),result);
            }
            part2_cold_bind(|events|part2_spatial_derived_grid_run(&context.size,&first.component_coding_styles,first.coding_style.layers,
                &context.limits,Some(context.tile),0,events),|grid,rest|private_standard_plan_after_grid(context,grid,rest),grid_result,result);
        },
    }
}

pub(crate) proof fn private_standard_grid_new_fields(layers:u16,components:u16,resolutions:Seq<u8>,counts:Seq<u32>,limits:&crate::ResourceLimits)
    ensures match part1_packet_grid_new(layers,components,resolutions,counts,None,limits){
        Err(_)=>true,Ok(grid)=>grid.layers==layers && grid.components==components && grid.component_resolutions==resolutions,
    },
{}

pub(crate) proof fn private_standard_grid_resolutions_fields(
    size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,descriptors:Part2ComponentResolutionCounts,
    component:u16,style:crate::codestream::CodingStyle,resolutions:u8,resolution:u8,counts:Seq<u32>,total:u64,
)
    ensures match part2_packet_grid_resolutions_run(size,styles,layers,limits,tile,0,descriptors,component,style,resolutions,resolution,counts,total){
        Err(_)=>true,Ok(grid)=>grid.components==crate::codestream::image_size_component_count(size)
            && grid.layers==layers && grid.component_resolutions==descriptors.1,
    },
    decreases crate::codestream::image_size_component_count(size) as nat-component as nat,0nat,
        descriptors.0 as nat-resolution as nat,
{
    reveal_with_fuel(part2_packet_grid_resolutions_run,2);
    reveal_with_fuel(part2_packet_grid_components_run,2);
    if component>=crate::codestream::image_size_component_count(size){}
    else if resolution>=descriptors.0{
        private_standard_grid_components_fields(size,styles,layers,limits,tile,descriptors,(component+1) as u16,counts,total);
    }else if resolution>=resolutions{
        private_standard_grid_resolutions_fields(size,styles,layers,limits,tile,descriptors,component,style,resolutions,
            (resolution+1) as u8,counts.push(0),total);
    }else if let Ok(geometry)=part2_resolution_geometry(crate::codestream::selection_geometry_view(size),
        crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),
        crate::decode::resolution_geometry_style(style),component,resolution,tile){
        if let Ok(subbands)=part2_packet_grid_subband_delta(style,resolution){
            if let Ok(next)=part2_packet_grid_codeblocks(total,geometry.code_blocks,resolution<resolutions,limits){
                if subbands==0 || geometry.precincts<=u32::MAX{
                    private_standard_grid_resolutions_fields(size,styles,layers,limits,tile,descriptors,component,style,resolutions,
                        (resolution+1) as u8,counts.push(if subbands==0{0u32}else{geometry.precincts as u32}),next);
                }
            }
        }
    }
}

pub(crate) proof fn private_standard_grid_components_fields(
    size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,descriptors:Part2ComponentResolutionCounts,
    component:u16,counts:Seq<u32>,total:u64)
    ensures match part2_packet_grid_components_run(size,styles,layers,limits,tile,0,descriptors,component,counts,total){
        Err(_)=>true,Ok(grid)=>grid.components==crate::codestream::image_size_component_count(size)
            && grid.layers==layers && grid.component_resolutions==descriptors.1,
    },
    decreases crate::codestream::image_size_component_count(size) as nat-component as nat,1nat,0nat,
{
    reveal_with_fuel(part2_packet_grid_components_run,2);reveal_with_fuel(part2_packet_grid_resolutions_run,2);
    if component>=crate::codestream::image_size_component_count(size){
        private_standard_grid_new_fields(layers,crate::codestream::image_size_component_count(size),descriptors.1,counts,limits);
    }else if let Ok(style)=crate::codestream::component_coding_style_result(styles,component){
        if style.decomposition_levels<u8::MAX{
            private_standard_grid_resolutions_fields(size,styles,layers,limits,tile,descriptors,component,style,
                (style.decomposition_levels+1) as u8,0,counts,total);
        }
    }
}

pub(crate) proof fn private_standard_descriptors_fields(context:PrivateStandardPlanContext,component:u16,maximum:u8,
    before:Seq<u8>)
    requires private_ht_standard_eligible(&context.size,context.tile,seq![context.first],context.caps,None),
        context.first.coding_style.decomposition_levels<u8::MAX,
        component<=crate::codestream::image_size_component_count(&context.size),
        before==Seq::new(component as nat,|_:int|(context.first.coding_style.decomposition_levels+1) as u8),
        (component==0 && maximum==0) || (component>0 && maximum==(context.first.coding_style.decomposition_levels+1) as u8),
    ensures part2_component_resolution_counts_run(crate::codestream::image_size_component_count(&context.size),
        &context.first.component_coding_styles,0,component,maximum,before,before)==Ok((
            (context.first.coding_style.decomposition_levels+1) as u8,
            Seq::new(crate::codestream::image_size_component_count(&context.size) as nat,|_:int|(context.first.coding_style.decomposition_levels+1) as u8),
            Seq::new(crate::codestream::image_size_component_count(&context.size) as nat,|_:int|(context.first.coding_style.decomposition_levels+1) as u8))),
    decreases crate::codestream::image_size_component_count(&context.size)-component,
{
    reveal_with_fuel(part2_component_resolution_counts_run,1);
    if component<crate::codestream::image_size_component_count(&context.size){
        private_standard_eligible_at(&context.size,context.tile,context.first,context.caps,None,component);
        private_standard_component_style_fields(&context.size,context.tile,context.first,component);
        let count=(context.first.coding_style.decomposition_levels+1) as u8;
        assert(before.push(count) =~= Seq::new(component as nat+1,|_:int|count));
        private_standard_descriptors_fields(context,(component+1) as u16,count,before.push(count));
    }
}

pub(crate) proof fn private_standard_spatial_fields(grid:Part1PacketGrid,size:&crate::codestream::ImageSize,
    styles:Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>>,tile:Option<u16>)
    ensures match part2_packet_spatial_value(grid,size,styles,tile){
        Err(_)=>true,Ok(after)=>after.components==grid.components
            && after.layers==grid.layers && after.component_resolutions==grid.component_resolutions,
    },
{}

pub(crate) proof fn private_standard_grid_fields(context:PrivateStandardPlanContext,grid:Part1PacketGrid)
    requires private_ht_standard_eligible(&context.size,context.tile,seq![context.first],context.caps,None),
        part2_spatial_packet_grid_from_components(&context.size,&context.first.component_coding_styles,
            context.first.coding_style.layers,&context.limits,Some(context.tile),0)==Ok(grid),
    ensures grid.components==crate::codestream::image_size_component_count(&context.size),
        grid.component_resolutions.len()==crate::codestream::image_size_component_count(&context.size),
        grid.component_resolutions==Seq::new(crate::codestream::image_size_component_count(&context.size) as nat,
            |_:int|(context.first.coding_style.decomposition_levels+1) as u8),
{
    private_standard_eligible_at(&context.size,context.tile,context.first,context.caps,None,0);
    private_standard_component_style_fields(&context.size,context.tile,context.first,0);
    reveal_with_fuel(part2_component_resolution_counts_run,1);
    assert(context.first.coding_style.decomposition_levels<u8::MAX);
    assert(Seq::<u8>::empty() =~= Seq::new(0,|_:int|(context.first.coding_style.decomposition_levels+1) as u8));
    private_standard_descriptors_fields(context,0,0,Seq::empty());
    if let Ok(descriptors)=part2_component_resolution_counts(crate::codestream::image_size_component_count(&context.size),
        &context.first.component_coding_styles,0){
        private_standard_grid_components_fields(&context.size,&context.first.component_coding_styles,
            context.first.coding_style.layers,&context.limits,Some(context.tile),descriptors,0,Seq::empty(),0);
    }
    if let Ok(base)=part2_packet_grid_from_components(&context.size,&context.first.component_coding_styles,
        context.first.coding_style.layers,&context.limits,Some(context.tile),0){
        private_standard_spatial_fields(base,&context.size,part2_packet_spatial_component_styles(&context.first.component_coding_styles),Some(context.tile));
    }
}

pub(crate) proof fn private_standard_component_fields(context:PrivateStandardPlanContext,
    precincts:Seq<PrivateHtPrecinctState>,total:u64,row:PrivateStandardPlannedComponent)
    requires private_ht_standard_eligible(&context.size,context.tile,seq![context.first],context.caps,None),
        context.component<crate::codestream::image_size_component_count(&context.size),
        forall|i:int|0<=i<precincts.len() ==> #[trigger] private_precinct_wf(precincts[i]),
        private_standard_component_value(context,precincts,total)==Ok(row),
    ensures row.component.component==context.component,
        forall|i:int|0<=i<row.precincts.len() ==> #[trigger] private_precinct_wf(row.precincts[i]),
{
    reveal(private_standard_component_value);
    let first=context.first;
    let metadata=part2_component_plan_metadata_owned(&context.size,&first.component_coding_styles,first.component_quantizations,
        &first.roi_shifts,context.component,(context.tile,0),part2_profile_force_ht(context.caps)).get_Ok_0();
    private_standard_metadata_fields(context,metadata);
    private_standard_resolutions_fields(context,metadata,0,private_standard_component_initial(precincts,total));
}

pub(crate) proof fn private_standard_components_fields(context:PrivateStandardPlanContext,grid:Part1PacketGrid,
    component:u16,before:PrivateStandardTileBuffers,value:PrivateStandardPlanState)
    requires private_ht_standard_eligible(&context.size,context.tile,seq![context.first],context.caps,None),
        component<=crate::codestream::image_size_component_count(&context.size),before.components.len()==component,
        forall|i:int|0<=i<before.components.len() ==> #[trigger] before.components[i].component==i,
        forall|i:int|0<=i<before.precincts.len() ==> #[trigger] private_precinct_wf(before.precincts[i]),
        private_standard_components_value(context,grid,component,before)==Ok(value),
    ensures value.grid==grid,value.components.len()==crate::codestream::image_size_component_count(&context.size),
        forall|i:int|0<=i<value.components.len() ==> #[trigger] value.components[i].component==i,
        forall|i:int|0<=i<value.precincts.len() ==> #[trigger] private_precinct_wf(value.precincts[i]),
    decreases crate::codestream::image_size_component_count(&context.size)-component,
{
    reveal_with_fuel(private_standard_components_value,1);
    if component<crate::codestream::image_size_component_count(&context.size){
        let current=PrivateStandardPlanContext {component,..context};
        let row=private_standard_component_value(current,before.precincts,before.total).get_Ok_0();
        private_standard_component_fields(current,before.precincts,before.total,row);
        let after=private_standard_tile_after_component(before,row);
        assert forall|i:int|0<=i<after.components.len() implies #[trigger] after.components[i].component==i by {}
        private_standard_components_fields(context,grid,(component+1) as u16,after,value);
    }
}

pub(crate) proof fn private_standard_plan_value_fields(context:PrivateStandardPlanContext,value:PrivateStandardPlanState)
    requires private_ht_standard_eligible(&context.size,context.tile,seq![context.first],context.caps,None),
        private_standard_plan_value(context)==Ok(value),
    ensures value.components.len()==crate::codestream::image_size_component_count(&context.size),
        forall|i:int|0<=i<value.components.len() ==> #[trigger] value.components[i].component==i,
        value.grid.components==crate::codestream::image_size_component_count(&context.size),
        value.grid.component_resolutions.len()==crate::codestream::image_size_component_count(&context.size),
        value.grid.component_resolutions==Seq::new(crate::codestream::image_size_component_count(&context.size) as nat,
            |_:int|(context.first.coding_style.decomposition_levels+1) as u8),
        forall|i:int|0<=i<value.precincts.len() ==> #[trigger] private_precinct_wf(value.precincts[i]),
{
    let first=context.first;
    let grid=part2_spatial_packet_grid_from_components(&context.size,&first.component_coding_styles,
        first.coding_style.layers,&context.limits,Some(context.tile),0).get_Ok_0();
    private_standard_grid_fields(context,grid);
    private_standard_components_fields(context,grid,0,private_standard_tile_initial(),value);
}

pub(crate) open spec fn private_standard_component_prepared(context:PrivateStandardPlanContext,
    metadata:Part2ComponentPlanMetadata)->bool {
    part2_component_metadata_result(&context.size,&context.first.component_coding_styles,context.first.component_quantizations,
            &context.first.roi_shifts,context.component,(context.tile,0),part2_profile_force_ht(context.caps),Ok(metadata))
        && part2_component_plan_metadata_owned(&context.size,&context.first.component_coding_styles,context.first.component_quantizations,
            &context.first.roi_shifts,context.component,(context.tile,0),part2_profile_force_ht(context.caps))==Ok(metadata)
}

pub(crate) proof fn private_standard_component_resolutions_observed(context:PrivateStandardPlanContext,
    precincts:Seq<PrivateHtPrecinctState>,total:u64,
    metadata:Part2ComponentPlanMetadata,result:Result<PrivateStandardComponentBuffers,crate::DecodeError>)
    requires private_standard_component_prepared(context,metadata),
        part2_cold_framed(|events|private_standard_resolutions_run(context,metadata,0,
            private_standard_component_initial(precincts,total),events),result),
    ensures private_standard_component_result(context,precincts,total,
        match result{Err(error)=>Err(error),Ok(after)=>Ok(private_standard_component_finish(context,metadata,after))}),
{
    reveal(private_standard_component_run);
    reveal(part2_component_metadata_result);
    let before=private_standard_component_initial(precincts,total);
    let output=match result{Err(error)=>Err(error),Ok(after)=>Ok(private_standard_component_finish(context,metadata,after))};
    if result.is_ok(){part2_cold_pure(output);}
    part2_cold_bind(|events|private_standard_resolutions_run(context,metadata,0,before,events),
        |after,rest|Some((Ok(private_standard_component_finish(context,metadata,after)),rest)),result,output);
    part2_decode_eta(|events|private_standard_component_after_metadata(context,precincts,total,metadata,events),output);
    part2_cold_bind(|events|part2_component_metadata_run(&context.size,&context.first.component_coding_styles,
        context.first.component_quantizations,&context.first.roi_shifts,context.component,(context.tile,0),part2_profile_force_ht(context.caps),events),
        |meta,rest|private_standard_component_after_metadata(context,precincts,total,meta,rest),Ok(metadata),output);
}

pub(crate) proof fn private_standard_precinct_step_observed(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,precinct:u32,before:PrivateStandardComponentBuffers,origin:[u32;2],
    row:Result<PrivateStandardPlannedPrecinct,crate::DecodeError>,response:Result<(),crate::DecodeError>)
    requires part2_planned_precinct_origin(data.first_precinct,data.geometry.precincts_across,precinct,data.band_size)==Ok(origin),
        part2_cold_framed(|events|private_standard_precinct_run(
            private_standard_precinct_context(context,metadata,data,origin,resolution,precinct,before.precincts.len() as usize),
            before.placements,before.total,events),row),
        match row{Err(_)=>true,Ok(value)=>private_owner_capacity_result(
            PrivateOwnerCapacityContext::ResolutionAppend {source:before.precincts,next:value.precinct},response)},
    ensures part2_cold_framed(|events|private_standard_precinct_step_run(context,metadata,data,resolution,precinct,before,events),
        match row{Err(error)=>Err(error),Ok(value)=>match response{Err(error)=>Err(error),Ok(())=>Ok(private_standard_after_precinct(before,value))}}),
{
    let output=match row{Err(error)=>Err(error),Ok(value)=>match response{Err(error)=>Err(error),Ok(())=>Ok(private_standard_after_precinct(before,value))}};
    if let Ok(value)=row{
        let capacity=PrivateOwnerCapacityContext::ResolutionAppend {source:before.precincts,next:value.precinct};
        part2_cold_pure(Ok(private_standard_after_precinct(before,value)));
        part2_cold_bind(|events|private_owner_capacity_run(capacity,events),
            |_:(),rest|Some((Ok(private_standard_after_precinct(before,value)),rest)),response,output);
        part2_decode_eta(|events|part2_jpip_snapshot_bind(private_owner_capacity_run(capacity,events),
            |_:(),rest|Some((Ok(private_standard_after_precinct(before,value)),rest))),output);
    }
    part2_cold_bind(|events|private_standard_precinct_run(
        private_standard_precinct_context(context,metadata,data,origin,resolution,precinct,before.precincts.len() as usize),
        before.placements,before.total,events),|value:PrivateStandardPlannedPrecinct,rest|part2_jpip_snapshot_bind(
            private_owner_capacity_run(PrivateOwnerCapacityContext::ResolutionAppend {source:before.precincts,next:value.precinct},rest),
            |_:(),tail|Some((Ok(private_standard_after_precinct(before,value)),tail))),row,output);
}

pub(crate) open spec fn private_standard_precincts_prefix(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,initial:PrivateStandardComponentBuffers,precinct:nat,
    current:PrivateStandardComponentBuffers,prefix:Seq<Part2JpipSnapshotEvent>)->bool {
    forall|events| #[trigger] private_standard_precincts_run(context,metadata,data,resolution,0,initial,prefix+events)==
        private_standard_precincts_run(context,metadata,data,resolution,precinct,current,events)
}

pub(crate) open spec fn private_standard_resolutions_prefix(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    initial:PrivateStandardComponentBuffers,resolution:nat,current:PrivateStandardComponentBuffers,prefix:Seq<Part2JpipSnapshotEvent>)->bool {
    forall|events| #[trigger] private_standard_resolutions_run(context,metadata,0,initial,prefix+events)==
        private_standard_resolutions_run(context,metadata,resolution,current,events)
}

pub(crate) proof fn private_standard_precincts_error(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,initial:PrivateStandardComponentBuffers,precinct:nat,
    current:PrivateStandardComponentBuffers,prefix:Seq<Part2JpipSnapshotEvent>,error:crate::DecodeError)
    requires precinct<data.precincts_in_resolution,private_standard_precincts_prefix(context,metadata,data,resolution,initial,precinct,current,prefix),
        part2_cold_framed(|events|private_standard_precinct_step_run(context,metadata,data,resolution,precinct as u32,current,events),Err(error)),
    ensures part2_cold_framed(|events|private_standard_precincts_run(context,metadata,data,resolution,0,initial,events),Err(error)),
{
    assert forall|events|private_standard_precincts_run(context,metadata,data,resolution,0,initial,prefix+events)==part2_jpip_snapshot_bind(
        private_standard_precinct_step_run(context,metadata,data,resolution,precinct as u32,current,events),
        |after,rest|private_standard_precincts_run(context,metadata,data,resolution,precinct+1,after,rest)) by {
        assert(private_standard_precincts_run(context,metadata,data,resolution,0,initial,prefix+events)==private_standard_precincts_run(context,metadata,data,resolution,precinct,current,events));
        reveal_with_fuel(private_standard_precincts_run,1);
    }
    part2_decode_prefix_error(|events|private_standard_precincts_run(context,metadata,data,resolution,0,initial,events),
        |events|private_standard_precinct_step_run(context,metadata,data,resolution,precinct as u32,current,events),
        |after,rest|private_standard_precincts_run(context,metadata,data,resolution,precinct+1,after,rest),prefix,error);
}

pub(crate) proof fn private_standard_resolutions_error(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    initial:PrivateStandardComponentBuffers,resolution:nat,current:PrivateStandardComponentBuffers,prefix:Seq<Part2JpipSnapshotEvent>,error:crate::DecodeError)
    requires resolution<=metadata.coding_style.decomposition_levels,
        private_standard_resolutions_prefix(context,metadata,initial,resolution,current,prefix),
        part2_cold_framed(|events|private_standard_resolution_run(context,metadata,resolution as u8,current,events),Err(error)),
    ensures part2_cold_framed(|events|private_standard_resolutions_run(context,metadata,0,initial,events),Err(error)),
{
    assert forall|events|private_standard_resolutions_run(context,metadata,0,initial,prefix+events)==part2_jpip_snapshot_bind(
        private_standard_resolution_run(context,metadata,resolution as u8,current,events),
        |after,rest|if resolution==u8::MAX{Some((Err(part1_block_placement_error(true)),rest))}
            else{private_standard_resolutions_run(context,metadata,resolution+1,after,rest)}) by {
        assert(private_standard_resolutions_run(context,metadata,0,initial,prefix+events)==private_standard_resolutions_run(context,metadata,resolution,current,events));
        reveal_with_fuel(private_standard_resolutions_run,1);
    }
    part2_decode_prefix_error(|events|private_standard_resolutions_run(context,metadata,0,initial,events),
        |events|private_standard_resolution_run(context,metadata,resolution as u8,current,events),
        |after,rest|if resolution==u8::MAX{Some((Err(part1_block_placement_error(true)),rest))}
            else{private_standard_resolutions_run(context,metadata,resolution+1,after,rest)},prefix,error);
}

pub(crate) proof fn private_standard_precincts_advance(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,initial:PrivateStandardComponentBuffers,precinct:nat,
    current:PrivateStandardComponentBuffers,prefix:Seq<Part2JpipSnapshotEvent>,after:PrivateStandardComponentBuffers)
    ->(extended:Seq<Part2JpipSnapshotEvent>)
    requires precinct<data.precincts_in_resolution,private_standard_precincts_prefix(context,metadata,data,resolution,initial,precinct,current,prefix),
        part2_cold_framed(|events|private_standard_precinct_step_run(context,metadata,data,resolution,precinct as u32,current,events),Ok(after)),
    ensures private_standard_precincts_prefix(context,metadata,data,resolution,initial,precinct+1,after,extended),
{
    assert forall|events|private_standard_precincts_run(context,metadata,data,resolution,0,initial,prefix+events)==part2_jpip_snapshot_bind(
        private_standard_precinct_step_run(context,metadata,data,resolution,precinct as u32,current,events),
        |next,rest|private_standard_precincts_run(context,metadata,data,resolution,precinct+1,next,rest)) by {
        assert(private_standard_precincts_run(context,metadata,data,resolution,0,initial,prefix+events)==
            private_standard_precincts_run(context,metadata,data,resolution,precinct,current,events));
        reveal_with_fuel(private_standard_precincts_run,1);
    }
    part2_decode_prefix_advance(|events|private_standard_precincts_run(context,metadata,data,resolution,0,initial,events),
        |events|private_standard_precinct_step_run(context,metadata,data,resolution,precinct as u32,current,events),
        |next,rest|private_standard_precincts_run(context,metadata,data,resolution,precinct+1,next,rest),prefix,after)
}

pub(crate) proof fn private_standard_precincts_finish(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,initial:PrivateStandardComponentBuffers,current:PrivateStandardComponentBuffers,
    prefix:Seq<Part2JpipSnapshotEvent>)
    requires private_standard_precincts_prefix(context,metadata,data,resolution,initial,data.precincts_in_resolution as nat,current,prefix),
    ensures part2_cold_framed(|events|private_standard_precincts_run(context,metadata,data,resolution,0,initial,events),Ok(current)),
{
    assert forall|events|private_standard_precincts_run(context,metadata,data,resolution,0,initial,prefix+events)==Some((Ok(current),events)) by {
        assert(private_standard_precincts_run(context,metadata,data,resolution,0,initial,prefix+events)==
            private_standard_precincts_run(context,metadata,data,resolution,data.precincts_in_resolution as nat,current,events));
        reveal_with_fuel(private_standard_precincts_run,1);
    }
    assert(part2_cold_prefix(|events|private_standard_precincts_run(context,metadata,data,resolution,0,initial,events),prefix,Ok(current)));
}

pub(crate) proof fn private_standard_resolution_precincts_observed(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    data:Part2ResolutionPlanMetadata,resolution:u8,before:PrivateStandardComponentBuffers,
    result:Result<PrivateStandardComponentBuffers,crate::DecodeError>)
    requires part2_resolution_plan_metadata(&context.size,metadata.coding_style,context.component,(context.tile,resolution),[metadata.bounds.x0,metadata.bounds.y0])==Ok(data),
        part2_cold_framed(|events|private_standard_precincts_run(context,metadata,data,resolution,0,before,events),result),
    ensures part2_cold_framed(|events|private_standard_resolution_run(context,metadata,resolution,before,events),result),
{
    part2_cold_framed_extensional(|events|private_standard_precincts_run(context,metadata,data,resolution,0,before,events),
        |events|private_standard_resolution_run(context,metadata,resolution,before,events),result);
}

pub(crate) proof fn private_standard_resolutions_advance(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    initial:PrivateStandardComponentBuffers,resolution:nat,current:PrivateStandardComponentBuffers,
    prefix:Seq<Part2JpipSnapshotEvent>,after:PrivateStandardComponentBuffers)
    ->(extended:Seq<Part2JpipSnapshotEvent>)
    requires resolution<=metadata.coding_style.decomposition_levels,resolution<u8::MAX,
        private_standard_resolutions_prefix(context,metadata,initial,resolution,current,prefix),
        part2_cold_framed(|events|private_standard_resolution_run(context,metadata,resolution as u8,current,events),Ok(after)),
    ensures private_standard_resolutions_prefix(context,metadata,initial,resolution+1,after,extended),
{
    assert forall|events|private_standard_resolutions_run(context,metadata,0,initial,prefix+events)==part2_jpip_snapshot_bind(
        private_standard_resolution_run(context,metadata,resolution as u8,current,events),
        |next,rest|private_standard_resolutions_run(context,metadata,resolution+1,next,rest)) by {
        assert(private_standard_resolutions_run(context,metadata,0,initial,prefix+events)==
            private_standard_resolutions_run(context,metadata,resolution,current,events));
        reveal_with_fuel(private_standard_resolutions_run,1);
    }
    part2_decode_prefix_advance(|events|private_standard_resolutions_run(context,metadata,0,initial,events),
        |events|private_standard_resolution_run(context,metadata,resolution as u8,current,events),
        |next,rest|private_standard_resolutions_run(context,metadata,resolution+1,next,rest),prefix,after)
}

pub(crate) proof fn private_standard_resolutions_terminal_error(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    initial:PrivateStandardComponentBuffers,resolution:nat,current:PrivateStandardComponentBuffers,
    prefix:Seq<Part2JpipSnapshotEvent>,after:PrivateStandardComponentBuffers)
    requires resolution<=metadata.coding_style.decomposition_levels,resolution==u8::MAX,
        private_standard_resolutions_prefix(context,metadata,initial,resolution,current,prefix),
        part2_cold_framed(|events|private_standard_resolution_run(context,metadata,resolution as u8,current,events),Ok(after)),
    ensures part2_cold_framed(|events|private_standard_resolutions_run(context,metadata,0,initial,events),Err(part1_block_placement_error(true))),
{
    assert forall|events|private_standard_resolutions_run(context,metadata,0,initial,prefix+events)==part2_jpip_snapshot_bind(
        private_standard_resolution_run(context,metadata,resolution as u8,current,events),
        |_:PrivateStandardComponentBuffers,rest|Some((Err::<PrivateStandardComponentBuffers,crate::DecodeError>(part1_block_placement_error(true)),rest))) by {
        assert(private_standard_resolutions_run(context,metadata,0,initial,prefix+events)==
            private_standard_resolutions_run(context,metadata,resolution,current,events));
        reveal_with_fuel(private_standard_resolutions_run,1);
    }
    let tail=part2_decode_prefix_advance(|events|private_standard_resolutions_run(context,metadata,0,initial,events),
        |events|private_standard_resolution_run(context,metadata,resolution as u8,current,events),
        |_:PrivateStandardComponentBuffers,rest|Some((Err::<PrivateStandardComponentBuffers,crate::DecodeError>(part1_block_placement_error(true)),rest)),prefix,after);
    assert(part2_cold_prefix(|events|private_standard_resolutions_run(context,metadata,0,initial,events),tail,Err(part1_block_placement_error(true))));
}

pub(crate) proof fn private_standard_resolutions_finish(context:PrivateStandardPlanContext,metadata:Part2ComponentPlanMetadata,
    initial:PrivateStandardComponentBuffers,resolution:nat,current:PrivateStandardComponentBuffers,prefix:Seq<Part2JpipSnapshotEvent>)
    requires resolution>metadata.coding_style.decomposition_levels,
        private_standard_resolutions_prefix(context,metadata,initial,resolution,current,prefix),
    ensures part2_cold_framed(|events|private_standard_resolutions_run(context,metadata,0,initial,events),Ok(current)),
{
    assert forall|events|private_standard_resolutions_run(context,metadata,0,initial,prefix+events)==Some((Ok(current),events)) by {
        assert(private_standard_resolutions_run(context,metadata,0,initial,prefix+events)==private_standard_resolutions_run(context,metadata,resolution,current,events));
        reveal_with_fuel(private_standard_resolutions_run,1);
    }
    assert(part2_cold_prefix(|events|private_standard_resolutions_run(context,metadata,0,initial,events),prefix,Ok(current)));
}

}
