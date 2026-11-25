use super::*;
verus! {

pub struct PrivateHtSubbandContext {
    pub geometry:crate::decode::SubbandGeometry,
    pub band:[u32;4],pub block:[u32;2],
    pub style:crate::tier1::Tier1CodingStyle,
    pub allowed:bool,pub bound:u8,pub blocks:u64,pub work:u64,
}

pub struct PrivateHtBlockRows {
    pub decoders:Seq<PrivateHtDecoderState>,
    pub placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
}

pub struct PrivateHtSubbandState {
    pub geometry:crate::decode::SubbandGeometry,
    pub rows:PrivateHtBlockRows,
    pub across:u32,pub down:u32,
}

pub struct PrivateHtPlanState {
    pub component:Part1PreparePlan,
    pub grid:Part1PacketGrid,
    pub precinct:PrivateHtPrecinctState,
}

pub(crate) open spec fn private_block_rows_wf(rows:PrivateHtBlockRows)->bool {
    rows.decoders.len()==rows.placements.len()
        && forall|i:int|0<=i<rows.decoders.len() ==> #[trigger] private_ht_state_wf(rows.decoders[i])
}

pub(crate) open spec fn private_rows_public(rows:PrivateHtBlockRows,total:u64)->Part2PlannedCodeBlocks {
    Part2PlannedCodeBlocks {
        decoders:rows.decoders.map_values(|d:PrivateHtDecoderState|d.logical),placements:rows.placements,
        decoder_index:rows.placements.len() as usize,planned_code_blocks:total,
    }
}

pub(crate) open spec fn private_rows_public_outcome(result:Result<PrivateHtBlockRows,crate::DecodeError>,total:u64)
    ->Result<Part2PlannedCodeBlocks,crate::DecodeError> {
    match result{Err(error)=>Err(error),Ok(rows)=>Ok(private_rows_public(rows,total))}
}

pub(crate) open spec fn private_subband_lattice(context:PrivateHtSubbandContext)->Result<Part2PlannedSubbandLattice,crate::DecodeError> {
    let g=context.geometry;
    if g.x0 as nat+g.width as nat>u32::MAX || g.y0 as nat+g.height as nat>u32::MAX {
        Err(part1_block_placement_error(true))
    }else{
        match part2_planned_subband_lattice(
            context.band,context.block,g,
        ){
            Err(error)=>Err(error),Ok(None)=>Err(part1_block_placement_error(false)),Ok(Some(lattice))=>Ok(lattice),
        }
    }
}

pub(crate) open spec fn private_subband_count(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice)->Result<usize,crate::DecodeError> {
    let count=lattice.blocks[0] as nat*lattice.blocks[1] as nat;
    if count>u64::MAX{Err(part1_block_placement_error(true))}
    else if count>context.blocks{Err(crate::DecodeError::LimitExceeded{resource:crate::Resource::CodeBlocks,limit:context.blocks,actual:count as u64})}
    else if count>context.work{Err(crate::DecodeError::LimitExceeded{resource:crate::Resource::WorkUnits,limit:context.work,actual:count as u64})}
    else if count>usize::MAX{Err(part1_block_placement_error(true))}
    else{Ok(count as usize)}
}

pub(crate) open spec fn private_subband_owner_context(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,count:usize)->PrivateOwnerCapacityContext {
    PrivateOwnerCapacityContext::Blocks {
        geometry:context.geometry,grid:lattice.grid,clip:lattice.clip,shape:lattice.blocks,
        style:context.style,allowed:context.allowed,bound:context.bound,count,
    }
}

pub(crate) open spec fn private_block_context(context:PrivateHtSubbandContext,geometry:(u32,u32,u16,u16))->PrivateHtInitialContext {
    PrivateHtInitialContext {
        width:geometry.2,height:geometry.3,bitplanes:context.geometry.significant_bitplanes,
        style:context.style,allowed:context.allowed,bound:context.bound,
    }
}

pub(crate) open spec fn private_block_placement(context:PrivateHtSubbandContext,geometry:(u32,u32,u16,u16),index:usize)
    ->Result<crate::decode::ProgressionCodeBlockPlacement,crate::DecodeError> {
    if geometry.0<context.geometry.x0 || geometry.1<context.geometry.y0 {Err(part1_block_placement_error(true))}
    else{Ok(crate::decode::ProgressionCodeBlockPlacement {
        precinct_index:0,decoder_index:index,subband_index:0,
        x:(geometry.0-context.geometry.x0) as u32,y:(geometry.1-context.geometry.y0) as u32,
    })}
}

pub(crate) open spec fn private_block_after_append(context:PrivateHtSubbandContext,before:PrivateHtBlockRows,
    geometry:(u32,u32,u16,u16),decoder:PrivateHtDecoderState,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtBlockRows> {
    part2_jpip_snapshot_bind(Some((private_block_placement(context,geometry,before.placements.len() as usize),events)),
        |placement:crate::decode::ProgressionCodeBlockPlacement,rest|private_block_after_placement(before,decoder,placement,rest))
}

pub(crate) open spec fn private_block_after_placement(before:PrivateHtBlockRows,decoder:PrivateHtDecoderState,
    placement:crate::decode::ProgressionCodeBlockPlacement,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtBlockRows> {
    part2_jpip_snapshot_bind(private_owner_capacity_run(
        PrivateOwnerCapacityContext::PlacementAppend{source:before.placements,next:placement},events),
        |_:(),rest|Some((Ok(PrivateHtBlockRows {
            decoders:before.decoders.push(decoder),placements:before.placements.push(placement),
        }),rest)))
}

pub(crate) open spec fn private_block_after_initial(context:PrivateHtSubbandContext,before:PrivateHtBlockRows,
    geometry:(u32,u32,u16,u16),decoder:PrivateHtDecoderState,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtBlockRows> {
    part2_jpip_snapshot_bind(private_owner_capacity_run(
        PrivateOwnerCapacityContext::BlockAppend{source:before.decoders,next:decoder},events),
        |_:(),rest|private_block_after_append(context,before,geometry,decoder,rest))
}

#[verifier::opaque]
pub(crate) open spec fn private_block_run(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    before:PrivateHtBlockRows,column:u32,row:u32,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtBlockRows> {
    match part2_planned_codeblock_geometry(lattice.grid,lattice.clip,[column,row]){
        Err(error)=>Some((Err(error),events)),
        Ok(geometry)=>part2_jpip_snapshot_bind(private_decoder_initial_calls_run(private_block_context(context,geometry),events),
            |decoder:PrivateHtDecoderState,rest|private_block_after_initial(context,before,geometry,decoder,rest)),
    }
}

pub(crate) open spec fn private_block_value(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    before:PrivateHtBlockRows,column:u32,row:u32)->Result<PrivateHtBlockRows,crate::DecodeError> {
    match part2_planned_codeblock_geometry(lattice.grid,lattice.clip,[column,row]){
        Err(error)=>Err(error),Ok(geometry)=>match private_ht_initial_value(private_block_context(context,geometry)){
            Err(error)=>Err(error),Ok(decoder)=>match private_block_placement(context,geometry,before.placements.len() as usize){
                Err(error)=>Err(error),Ok(placement)=>Ok(PrivateHtBlockRows {
                    decoders:before.decoders.push(decoder),placements:before.placements.push(placement),
                }),
            },
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_block_columns_value(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    before:PrivateHtBlockRows,row:u32,column:u32)->Result<PrivateHtBlockRows,crate::DecodeError>
    decreases lattice.blocks[0] as nat-column as nat,
{
    if column>=lattice.blocks[0]{Ok(before)}
    else{match private_block_value(context,lattice,before,column,row){
        Err(error)=>Err(error),Ok(after)=>private_block_columns_value(context,lattice,after,row,(column+1) as u32),
    }}
}

#[verifier::opaque]
pub(crate) open spec fn private_block_rows_value(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    before:PrivateHtBlockRows,row:u32)->Result<PrivateHtBlockRows,crate::DecodeError>
    decreases lattice.blocks[1] as nat-row as nat,
{
    if row>=lattice.blocks[1]{Ok(before)}
    else{match private_block_columns_value(context,lattice,before,row,0){
        Err(error)=>Err(error),Ok(after)=>private_block_rows_value(context,lattice,after,(row+1) as u32),
    }}
}

#[verifier::opaque]
pub(crate) open spec fn private_block_columns(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    before:PrivateHtBlockRows,row:u32,column:u32,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtBlockRows>
    decreases lattice.blocks[0] as nat-column as nat,
{
    if column>=lattice.blocks[0]{Some((Ok(before),events))}
    else{part2_jpip_snapshot_bind(private_block_run(context,lattice,before,column,row,events),
        |after:PrivateHtBlockRows,rest|private_block_columns(context,lattice,after,row,(column+1) as u32,rest))}
}

#[verifier::opaque]
pub(crate) open spec fn private_block_rows(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    before:PrivateHtBlockRows,row:u32,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtBlockRows>
    decreases lattice.blocks[1] as nat-row as nat,
{
    if row>=lattice.blocks[1]{Some((Ok(before),events))}
    else{part2_jpip_snapshot_bind(private_block_columns(context,lattice,before,row,0,events),
        |after:PrivateHtBlockRows,rest|private_block_rows(context,lattice,after,(row+1) as u32,rest))}
}

pub(crate) open spec fn private_subband_after_owner(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtSubbandState> {
    part2_jpip_snapshot_bind(private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,events),
        |rows:PrivateHtBlockRows,rest|Some((Ok(PrivateHtSubbandState {
            geometry:context.geometry,rows,across:lattice.blocks[0],down:lattice.blocks[1],
        }),rest)))
}

pub(crate) open spec fn private_subband_run(context:PrivateHtSubbandContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtSubbandState> {
    match private_subband_lattice(context){
        Err(error)=>Some((Err(error),events)),Ok(lattice)=>match private_subband_count(context,lattice){
            Err(error)=>Some((Err(error),events)),Ok(count)=>part2_jpip_snapshot_bind(
                private_owner_capacity_run(private_subband_owner_context(context,lattice,count),events),
                |_:(),rest|private_subband_after_owner(context,lattice,rest)),
        },
    }
}

pub(crate) open spec fn private_subband_result(context:PrivateHtSubbandContext,result:Result<PrivateHtSubbandState,crate::DecodeError>)->bool {
    part2_cold_framed(|events|private_subband_run(context,events),result)
}

pub(crate) open spec fn private_subband_value(context:PrivateHtSubbandContext)->Result<PrivateHtSubbandState,crate::DecodeError> {
    match private_subband_lattice(context){
        Err(error)=>Err(error),Ok(lattice)=>match private_subband_count(context,lattice){
            Err(error)=>Err(error),Ok(_)=>match private_block_rows_value(context,lattice,
                PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0){
                Err(error)=>Err(error),Ok(rows)=>Ok(PrivateHtSubbandState {
                    geometry:context.geometry,rows,across:lattice.blocks[0],down:lattice.blocks[1],
                }),
            },
        },
    }
}

pub(crate) open spec fn private_columns_prefix(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    initial:PrivateHtBlockRows,row:u32,column:u32,current:PrivateHtBlockRows,prefix:Seq<Part2JpipSnapshotEvent>)->bool {
    forall|tail| #[trigger] private_block_columns(context,lattice,initial,row,0,prefix+tail)
        ==private_block_columns(context,lattice,current,row,column,tail)
}

pub(crate) proof fn private_columns_advance(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    initial:PrivateHtBlockRows,row:u32,column:u32,current:PrivateHtBlockRows,prefix:Seq<Part2JpipSnapshotEvent>,after:PrivateHtBlockRows)
    ->(extended:Seq<Part2JpipSnapshotEvent>)
    requires column<lattice.blocks[0],private_columns_prefix(context,lattice,initial,row,column,current,prefix),
        part2_cold_framed(|events|private_block_run(context,lattice,current,column,row,events),Ok(after)),
    ensures private_columns_prefix(context,lattice,initial,row,(column+1) as u32,after,extended),
{
    assert forall|tail| #[trigger] private_block_columns(context,lattice,initial,row,0,prefix+tail)==
        part2_jpip_snapshot_bind(private_block_run(context,lattice,current,column,row,tail),
            |next,rest|private_block_columns(context,lattice,next,row,(column+1) as u32,rest)) by {
        assert(private_block_columns(context,lattice,initial,row,0,prefix+tail)==private_block_columns(context,lattice,current,row,column,tail));
        reveal_with_fuel(private_block_columns,1);
    }
    part2_decode_prefix_advance(
        |events|private_block_columns(context,lattice,initial,row,0,events),
        |events|private_block_run(context,lattice,current,column,row,events),
        |next,rest|private_block_columns(context,lattice,next,row,(column+1) as u32,rest),prefix,after)
}

pub(crate) proof fn private_columns_error(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    initial:PrivateHtBlockRows,row:u32,column:u32,current:PrivateHtBlockRows,prefix:Seq<Part2JpipSnapshotEvent>,error:crate::DecodeError)
    requires column<lattice.blocks[0],private_columns_prefix(context,lattice,initial,row,column,current,prefix),
        part2_cold_framed(|events|private_block_run(context,lattice,current,column,row,events),Err(error)),
    ensures part2_cold_framed(|events|private_block_columns(context,lattice,initial,row,0,events),Err(error)),
{
    assert forall|tail| #[trigger] private_block_columns(context,lattice,initial,row,0,prefix+tail)==
        part2_jpip_snapshot_bind(private_block_run(context,lattice,current,column,row,tail),
            |next,rest|private_block_columns(context,lattice,next,row,(column+1) as u32,rest)) by {
        assert(private_block_columns(context,lattice,initial,row,0,prefix+tail)==private_block_columns(context,lattice,current,row,column,tail));
        reveal_with_fuel(private_block_columns,1);
    }
    part2_decode_prefix_error(
        |events|private_block_columns(context,lattice,initial,row,0,events),
        |events|private_block_run(context,lattice,current,column,row,events),
        |next,rest|private_block_columns(context,lattice,next,row,(column+1) as u32,rest),prefix,error);
}

pub(crate) proof fn private_columns_finish(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    initial:PrivateHtBlockRows,row:u32,current:PrivateHtBlockRows,prefix:Seq<Part2JpipSnapshotEvent>)
    requires private_columns_prefix(context,lattice,initial,row,lattice.blocks[0],current,prefix),
    ensures part2_cold_framed(|events|private_block_columns(context,lattice,initial,row,0,events),Ok(current)),
{
    assert forall|tail|private_block_columns(context,lattice,initial,row,0,prefix+tail)==Some((Ok(current),tail)) by {
        assert(private_block_columns(context,lattice,initial,row,0,prefix+tail)==private_block_columns(context,lattice,current,row,lattice.blocks[0],tail));
        reveal_with_fuel(private_block_columns,1);
    }
    assert(part2_cold_prefix(|events|private_block_columns(context,lattice,initial,row,0,events),prefix,Ok(current)));
}

pub(crate) open spec fn private_rows_prefix(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    row:u32,current:PrivateHtBlockRows,prefix:Seq<Part2JpipSnapshotEvent>)->bool {
    forall|tail| #[trigger] private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,prefix+tail)
        ==private_block_rows(context,lattice,current,row,tail)
}

pub(crate) proof fn private_rows_advance(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    row:u32,current:PrivateHtBlockRows,prefix:Seq<Part2JpipSnapshotEvent>,after:PrivateHtBlockRows)->(extended:Seq<Part2JpipSnapshotEvent>)
    requires row<lattice.blocks[1],private_rows_prefix(context,lattice,row,current,prefix),
        part2_cold_framed(|events|private_block_columns(context,lattice,current,row,0,events),Ok(after)),
    ensures private_rows_prefix(context,lattice,(row+1) as u32,after,extended),
{
    assert forall|tail| #[trigger] private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,prefix+tail)==
        part2_jpip_snapshot_bind(private_block_columns(context,lattice,current,row,0,tail),
            |next,rest|private_block_rows(context,lattice,next,(row+1) as u32,rest)) by {
        assert(private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,prefix+tail)==
            private_block_rows(context,lattice,current,row,tail));
        reveal_with_fuel(private_block_rows,1);
    }
    part2_decode_prefix_advance(
        |events|private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,events),
        |events|private_block_columns(context,lattice,current,row,0,events),
        |next,rest|private_block_rows(context,lattice,next,(row+1) as u32,rest),prefix,after)
}

pub(crate) proof fn private_rows_error(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    row:u32,current:PrivateHtBlockRows,prefix:Seq<Part2JpipSnapshotEvent>,error:crate::DecodeError)
    requires row<lattice.blocks[1],private_rows_prefix(context,lattice,row,current,prefix),
        part2_cold_framed(|events|private_block_columns(context,lattice,current,row,0,events),Err(error)),
    ensures part2_cold_framed(|events|private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,events),Err(error)),
{
    assert forall|tail| #[trigger] private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,prefix+tail)==
        part2_jpip_snapshot_bind(private_block_columns(context,lattice,current,row,0,tail),
            |next,rest|private_block_rows(context,lattice,next,(row+1) as u32,rest)) by {
        assert(private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,prefix+tail)==
            private_block_rows(context,lattice,current,row,tail));
        reveal_with_fuel(private_block_rows,1);
    }
    part2_decode_prefix_error(
        |events|private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,events),
        |events|private_block_columns(context,lattice,current,row,0,events),
        |next,rest|private_block_rows(context,lattice,next,(row+1) as u32,rest),prefix,error);
}

pub(crate) proof fn private_rows_finish(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    current:PrivateHtBlockRows,prefix:Seq<Part2JpipSnapshotEvent>)
    requires private_rows_prefix(context,lattice,lattice.blocks[1],current,prefix),
    ensures part2_cold_framed(|events|private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,events),Ok(current)),
{
    assert forall|tail|private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,prefix+tail)==Some((Ok(current),tail)) by {
        assert(private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,prefix+tail)==
            private_block_rows(context,lattice,current,lattice.blocks[1],tail));
        reveal_with_fuel(private_block_rows,1);
    }
    assert(part2_cold_prefix(|events|private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,events),prefix,Ok(current)));
}

pub(crate) proof fn private_subband_rows_observed(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,count:usize,
    result:Result<PrivateHtBlockRows,crate::DecodeError>)
    requires private_subband_lattice(context)==Ok(lattice),private_subband_count(context,lattice)==Ok(count),
        private_owner_capacity_result(private_subband_owner_context(context,lattice,count),Ok(())),
        part2_cold_framed(|events|private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,events),result),
    ensures private_subband_result(context,match result{Err(error)=>Err(error),Ok(rows)=>Ok(PrivateHtSubbandState {
        geometry:context.geometry,rows,across:lattice.blocks[0],down:lattice.blocks[1],
    })}),
{
    let outcome=match result{Err(error)=>Err(error),Ok(rows)=>Ok(PrivateHtSubbandState {
        geometry:context.geometry,rows,across:lattice.blocks[0],down:lattice.blocks[1],
    })};
    if let Ok(rows)=result {part2_cold_pure(Ok(PrivateHtSubbandState {
        geometry:context.geometry,rows,across:lattice.blocks[0],down:lattice.blocks[1],
    }));}
    part2_cold_bind(
        |events|private_block_rows(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,events),
        |rows,rest|Some((Ok(PrivateHtSubbandState {
            geometry:context.geometry,rows,across:lattice.blocks[0],down:lattice.blocks[1],
        }),rest)),result,outcome);
    part2_cold_bind(|events|private_owner_capacity_run(private_subband_owner_context(context,lattice,count),events),
        |_:(),rest|private_subband_after_owner(context,lattice,rest),Ok(()),outcome);
}

pub(crate) open spec fn private_plan_public_view(plan:PrivateHtPlanState,tile:u16,first:Part2OwnedTilePart)->Part2ProgressionTilePlan {
    Part2ProgressionTilePlan {
        tile,coding_style:first.coding_style,coding_styles:first.component_coding_styles,
        grid:plan.grid,precincts:seq![plan.precinct.logical],components:seq![plan.component],
    }
}

    pub(crate) open spec fn private_plan_region(size:&crate::codestream::ImageSize,tile:u16,metadata:Part2ComponentPlanMetadata)
        ->Result<([u32;4],[u32;2]),crate::DecodeError> {
        match part2_resolution_plan_metadata(size,metadata.coding_style,0,(tile,0),[metadata.bounds.x0,metadata.bounds.y0]){
            Err(error)=>Err(error),Ok(data)=>match part2_planned_precinct_origin(data.first_precinct,data.geometry.precincts_across,0,data.band_size){
                Err(error)=>Err(error),Ok(origin)=>Ok(([origin[0],origin[1],data.band_size[0],data.band_size[1]],data.block_size)),
            },
        }
    }

    pub(crate) open spec fn private_plan_subband_context(metadata:Part2ComponentPlanMetadata,region:([u32;4],[u32;2]),caps:Option<(u32,Seq<u16>)>,
        limits:&crate::ResourceLimits)->PrivateHtSubbandContext {
        PrivateHtSubbandContext {
            geometry:metadata.subbands[0],band:region.0,block:region.1,style:metadata.tier1_style,
            allowed:part2_profile_multiple_sets(caps),bound:part2_profile_magnitude_bound(caps),
            blocks:crate::limits::resource_code_block_limit(limits),work:crate::limits::resource_work_limit(limits),
        }
    }

    pub(crate) open spec fn private_plan_precinct_context(metadata:Part2ComponentPlanMetadata,band:PrivateHtSubbandState,
        limits:&crate::ResourceLimits)->PrivatePrecinctInitialContext {
        PrivatePrecinctInitialContext {
            across:band.across,down:band.down,maximum_zero:band.geometry.significant_bitplanes,
            style:metadata.tier1_style,decoders:band.rows.decoders,
            blocks:crate::limits::resource_code_block_limit(limits),work:crate::limits::resource_work_limit(limits),
            tag_nodes:crate::limits::resource_tag_tree_node_limit(limits),
        }
    }

    pub(crate) open spec fn private_plan_finish(metadata:Part2ComponentPlanMetadata,grid:Part1PacketGrid,
        band:PrivateHtSubbandState,precinct:PrivateHtPrecinctState)->PrivateHtPlanState {
        PrivateHtPlanState {
            component:Part1PreparePlan {
                component:0,x:metadata.x,y:metadata.y,width:metadata.width,height:metadata.height,
                resolution:metadata.output_resolution,subbands:metadata.subbands,placements:band.rows.placements,
            },grid,precinct,
        }
    }

    pub(crate) open spec fn private_plan_after_subband(metadata:Part2ComponentPlanMetadata,grid:Part1PacketGrid,
        band:PrivateHtSubbandState,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtPlanState> {
        part2_jpip_snapshot_bind(private_precinct_initial_run(private_plan_precinct_context(metadata,band,limits),events),
            |precinct:PrivateHtPrecinctState,rest|Some((Ok(private_plan_finish(metadata,grid,band,precinct)),rest)))
    }

    pub(crate) open spec fn private_plan_after_metadata(size:&crate::codestream::ImageSize,tile:u16,metadata:Part2ComponentPlanMetadata,grid:Part1PacketGrid,
        caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtPlanState> {
        if metadata.subbands.len()!=1{Some((Err(part1_block_placement_error(false)),events))}
        else{match private_plan_region(size,tile,metadata){
            Err(error)=>Some((Err(error),events)),Ok(region)=>part2_jpip_snapshot_bind(
                private_subband_run(private_plan_subband_context(metadata,region,caps,limits),events),
                |band:PrivateHtSubbandState,rest|private_plan_after_subband(metadata,grid,band,limits,rest)),
        }}
    }

    pub(crate) open spec fn private_plan_after_grid(size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,
        grid:Part1PacketGrid,caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtPlanState> {
        part2_jpip_snapshot_bind(part2_component_metadata_run(size,&first.component_coding_styles,
            first.component_quantizations,&first.roi_shifts,0,(tile,0),part2_profile_force_ht(caps),events),
            |metadata:Part2ComponentPlanMetadata,rest|private_plan_after_metadata(size,tile,metadata,grid,caps,limits,rest))
    }

    pub(crate) open spec fn private_plan_run(size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,
        caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtPlanState> {
        match part2_selection_tile_bounds(crate::codestream::selection_geometry_view(size),tile){
            Err(error)=>Some((Err(error),events)),
            Ok(_)=>part2_jpip_snapshot_bind(part2_spatial_derived_grid_run(size,&first.component_coding_styles,
                first.coding_style.layers,limits,Some(tile),0,events),
                |grid:Part1PacketGrid,rest|private_plan_after_grid(size,tile,first,grid,caps,limits,rest)),
        }
    }

    pub(crate) open spec fn private_plan_result(size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,
        caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits,result:Result<PrivateHtPlanState,crate::DecodeError>)->bool {
        part2_cold_framed(|events|private_plan_run(size,tile,first,caps,limits,events),result)
    }

    pub(crate) open spec fn private_plan_value(size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,
        caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits)->Result<PrivateHtPlanState,crate::DecodeError> {
        match part2_selection_tile_bounds(crate::codestream::selection_geometry_view(size),tile){
            Err(error)=>Err(error),
            Ok(_)=>match part2_spatial_packet_grid_from_components(size,&first.component_coding_styles,
                first.coding_style.layers,limits,Some(tile),0){
                Err(error)=>Err(error),
                Ok(grid)=>match part2_component_plan_metadata_owned(size,&first.component_coding_styles,
                    first.component_quantizations,&first.roi_shifts,0,(tile,0),part2_profile_force_ht(caps)){
                    Err(error)=>Err(error),Ok(metadata)=>if metadata.subbands.len()!=1{Err(part1_block_placement_error(false))}
                        else{match private_plan_region(size,tile,metadata){
                            Err(error)=>Err(error),Ok(region)=>match private_subband_value(private_plan_subband_context(metadata,region,caps,limits)){
                            Err(error)=>Err(error),Ok(band)=>match private_precinct_initial_value(private_plan_precinct_context(metadata,band,limits)){
                                Err(error)=>Err(error),Ok(precinct)=>Ok(private_plan_finish(metadata,grid,band,precinct)),
                            },
                        }}},
                },
            },
        }
    }

    pub(crate) proof fn private_plan_grid_fields(size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,
        caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits,grid:Part1PacketGrid)
        requires private_ht_eligible(size,tile,seq![first],caps,None),
            part2_spatial_packet_grid_from_components(size,&first.component_coding_styles,first.coding_style.layers,limits,Some(tile),0)==Ok(grid),
        ensures private_grid_shape(grid),
    {
        let style=crate::codestream::component_coding_style_result(&first.component_coding_styles,0).get_Ok_0();
        crate::codestream::resolution_selectors_known_fields(style);
        reveal_with_fuel(part2_component_resolution_counts_run,2);
        reveal_with_fuel(part2_packet_grid_components_run,4);
        reveal_with_fuel(part2_packet_grid_resolutions_run,4);
        reveal_with_fuel(part1_grid_count_summary_run,2);
        reveal_with_fuel(part1_grid_resolution_summary,2);
        assert(part2_component_resolution_counts(1,&first.component_coding_styles,0)==Ok((1u8,seq![1u8],seq![1u8])));
        if let Ok(base)=part2_packet_grid_from_components(size,&first.component_coding_styles,first.coding_style.layers,limits,Some(tile),0){
            assert(base.precinct_counts==seq![1u32]);
            assert(base.precinct_offsets==seq![0usize,1usize]);
            assert(base.layers>0 && base.components==1 && base.resolutions==1);
            assert(base.component_resolutions==seq![1u8]);
            assert(base.maximum_precincts_per_resolution==1);
            let summary=part1_grid_count_summary(seq![1u32],seq![1u8],1,1).get_Ok_0();
            assert(summary.total==1);
            assert(base.packet_count==(summary.total as int*base.layers as int) as u64);
            assert(summary.total as int*base.layers as int==base.layers as int) by(nonlinear_arith)
                requires summary.total==1;
            assert(base.packet_count==base.layers as u64);
            assert(private_grid_shape(base));
        }
}

pub(crate) proof fn private_block_normal(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
before:PrivateHtBlockRows,column:u32,row:u32)
ensures part2_cold_framed(|events|private_block_run(context,lattice,before,column,row,events),
    private_block_value(context,lattice,before,column,row)),
{
    reveal(private_block_run);
let result=private_block_value(context,lattice,before,column,row);
match part2_planned_codeblock_geometry(lattice.grid,lattice.clip,[column,row]){
    Err(_)=>{part2_cold_pure(result);},
    Ok(geometry)=>{
        let initialized=private_ht_initial_value(private_block_context(context,geometry));
        private_ht_initial_normal(private_block_context(context,geometry));
        private_decoder_initial_calls_observed(private_block_context(context,geometry),initialized);
        if let Ok(decoder)=initialized{
            let placement=private_block_placement(context,geometry,before.placements.len() as usize);
            if let Ok(place)=placement{
                let capacity=PrivateOwnerCapacityContext::PlacementAppend{source:before.placements,next:place};
                private_owner_capacity_observed(capacity,Ok(()));
                part2_cold_pure(result);
                part2_cold_bind(|events|private_owner_capacity_run(capacity,events),
                    |_:(),rest|Some((Ok(PrivateHtBlockRows{decoders:before.decoders.push(decoder),placements:before.placements.push(place)}),rest)),Ok(()),result);
                part2_decode_eta(|events|private_block_after_placement(before,decoder,place,events),result);
            }else{part2_cold_pure(result);}
            let capacity=PrivateOwnerCapacityContext::BlockAppend{source:before.decoders,next:decoder};
            private_owner_capacity_observed(capacity,Ok(()));
            part2_cold_pure(placement);
            part2_cold_bind(|events|Some((placement,events)),
                |place,rest|private_block_after_placement(before,decoder,place,rest),placement,result);
            part2_decode_eta(|events|private_block_after_append(context,before,geometry,decoder,events),result);
            part2_cold_bind(|events|private_owner_capacity_run(capacity,events),
                |_:(),rest|private_block_after_append(context,before,geometry,decoder,rest),Ok(()),result);
            part2_decode_eta(|events|private_block_after_initial(context,before,geometry,decoder,events),result);
        }
        part2_cold_bind(|events|private_decoder_initial_calls_run(private_block_context(context,geometry),events),
            |decoder,rest|private_block_after_initial(context,before,geometry,decoder,rest),initialized,result);
    },
}
}

pub(crate) proof fn private_columns_normal(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
before:PrivateHtBlockRows,row:u32,column:u32)
ensures part2_cold_framed(|events|private_block_columns(context,lattice,before,row,column,events),
    private_block_columns_value(context,lattice,before,row,column)),
decreases lattice.blocks[0] as nat-column as nat,
{
reveal_with_fuel(private_block_columns,1);reveal_with_fuel(private_block_columns_value,1);
let result=private_block_columns_value(context,lattice,before,row,column);
if column>=lattice.blocks[0]{part2_cold_pure(result);}else{
    let next=private_block_value(context,lattice,before,column,row);
    private_block_normal(context,lattice,before,column,row);
    if let Ok(after)=next{
        private_columns_normal(context,lattice,after,row,(column+1) as u32);
        part2_decode_eta(|events|private_block_columns(context,lattice,after,row,(column+1) as u32,events),result);
    }
    part2_cold_bind(|events|private_block_run(context,lattice,before,column,row,events),
        |after,rest|private_block_columns(context,lattice,after,row,(column+1) as u32,rest),next,result);
}
}

pub(crate) proof fn private_rows_normal(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
before:PrivateHtBlockRows,row:u32)
ensures part2_cold_framed(|events|private_block_rows(context,lattice,before,row,events),
    private_block_rows_value(context,lattice,before,row)),
decreases lattice.blocks[1] as nat-row as nat,
{
reveal_with_fuel(private_block_rows,1);reveal_with_fuel(private_block_rows_value,1);
let result=private_block_rows_value(context,lattice,before,row);
if row>=lattice.blocks[1]{part2_cold_pure(result);}else{
    let next=private_block_columns_value(context,lattice,before,row,0);
    private_columns_normal(context,lattice,before,row,0);
    if let Ok(after)=next{
        private_rows_normal(context,lattice,after,(row+1) as u32);
        part2_decode_eta(|events|private_block_rows(context,lattice,after,(row+1) as u32,events),result);
    }
    part2_cold_bind(|events|private_block_columns(context,lattice,before,row,0,events),
        |after,rest|private_block_rows(context,lattice,after,(row+1) as u32,rest),next,result);
}
}

pub(crate) proof fn private_subband_normal(context:PrivateHtSubbandContext)
ensures private_subband_result(context,private_subband_value(context)),
{
let result=private_subband_value(context);
match private_subband_lattice(context){
    Err(_)=>{part2_cold_pure(result);},
    Ok(lattice)=>match private_subband_count(context,lattice){
        Err(_)=>{part2_cold_pure(result);},
        Ok(count)=>{
            let rows=private_block_rows_value(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0);
            private_rows_normal(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0);
            private_owner_capacity_observed(private_subband_owner_context(context,lattice,count),Ok(()));
            private_subband_rows_observed(context,lattice,count,rows);
        },
    },
}
}

pub(crate) proof fn private_plan_normal(size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,
caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits)
ensures private_plan_result(size,tile,first,caps,limits,private_plan_value(size,tile,first,caps,limits)),
{
let result=private_plan_value(size,tile,first,caps,limits);
match part2_selection_tile_bounds(crate::codestream::selection_geometry_view(size),tile){
    Err(_)=>{part2_cold_pure(result);},
    Ok(_)=>{
        let grid=part2_spatial_packet_grid_from_components(size,&first.component_coding_styles,first.coding_style.layers,limits,Some(tile),0);
        part2_spatial_derived_grid_normal(size,&first.component_coding_styles,first.coding_style.layers,limits,Some(tile),0);
        reveal(part2_spatial_derived_grid_result);
        if let Ok(shape)=grid{
            let metadata=part2_component_plan_metadata_owned(size,&first.component_coding_styles,first.component_quantizations,&first.roi_shifts,0,(tile,0),part2_profile_force_ht(caps));
            part2_component_metadata_normal(size,&first.component_coding_styles,first.component_quantizations,&first.roi_shifts,0,(tile,0),part2_profile_force_ht(caps));
            reveal(part2_component_metadata_result);
            if let Ok(meta)=metadata{
                if meta.subbands.len()!=1{part2_cold_pure(result);}else if let Ok(region)=private_plan_region(size,tile,meta){
                let band=private_subband_value(private_plan_subband_context(meta,region,caps,limits));
                private_subband_normal(private_plan_subband_context(meta,region,caps,limits));
                    if let Ok(value)=band{
                        let context=private_plan_precinct_context(meta,value,limits);
                        let precinct=private_precinct_initial_value(context);
                        private_precinct_initial_normal(context);
                        if precinct.is_ok(){part2_cold_pure(result);}
                        part2_cold_bind(|events|private_precinct_initial_run(context,events),
                            |precinct,rest|Some((Ok(private_plan_finish(meta,shape,value,precinct)),rest)),precinct,result);
                        part2_decode_eta(|events|private_plan_after_subband(meta,shape,value,limits,events),result);
                    }
                    part2_cold_bind(|events|private_subband_run(private_plan_subband_context(meta,region,caps,limits),events),
                        |band,rest|private_plan_after_subband(meta,shape,band,limits,rest),band,result);
                }else{part2_cold_pure(result);}
                part2_decode_eta(|events|private_plan_after_metadata(size,tile,meta,shape,caps,limits,events),result);
            }
            part2_cold_bind(|events|part2_component_metadata_run(size,&first.component_coding_styles,first.component_quantizations,&first.roi_shifts,0,(tile,0),part2_profile_force_ht(caps),events),
                |meta,rest|private_plan_after_metadata(size,tile,meta,shape,caps,limits,rest),metadata,result);
            part2_decode_eta(|events|private_plan_after_grid(size,tile,first,shape,caps,limits,events),result);
        }
        part2_cold_bind(|events|part2_spatial_derived_grid_run(size,&first.component_coding_styles,first.coding_style.layers,limits,Some(tile),0,events),
            |grid,rest|private_plan_after_grid(size,tile,first,grid,caps,limits,rest),grid,result);
    },
}
}

pub(crate) proof fn private_columns_value_fields(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
before:PrivateHtBlockRows,row:u32,column:u32)
requires private_block_rows_wf(before),
ensures match private_block_columns_value(context,lattice,before,row,column){Err(_)=>true,Ok(after)=>private_block_rows_wf(after)},
decreases lattice.blocks[0] as nat-column as nat,
{
reveal_with_fuel(private_block_columns_value,1);
if column<lattice.blocks[0]{
    if let Ok(geometry)=part2_planned_codeblock_geometry(lattice.grid,lattice.clip,[column,row]){
        if let Ok(decoder)=private_ht_initial_value(private_block_context(context,geometry)){
            private_ht_initial_fields(private_block_context(context,geometry),decoder);
            if let Ok(placement)=private_block_placement(context,geometry,before.placements.len() as usize){
                private_columns_value_fields(context,lattice,PrivateHtBlockRows {
                    decoders:before.decoders.push(decoder),placements:before.placements.push(placement),
                },row,(column+1) as u32);
            }
        }
    }
}
}

pub(crate) proof fn private_rows_value_fields(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
before:PrivateHtBlockRows,row:u32)
requires private_block_rows_wf(before),
ensures match private_block_rows_value(context,lattice,before,row){Err(_)=>true,Ok(after)=>private_block_rows_wf(after)},
decreases lattice.blocks[1] as nat-row as nat,
{
reveal_with_fuel(private_block_rows_value,1);
if row<lattice.blocks[1]{
    private_columns_value_fields(context,lattice,before,row,0);
    if let Ok(after)=private_block_columns_value(context,lattice,before,row,0){
        private_rows_value_fields(context,lattice,after,(row+1) as u32);
    }
}
}

pub(crate) proof fn private_plan_value_fields(size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,
caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits,plan:PrivateHtPlanState)
requires private_ht_eligible(size,tile,seq![first],caps,None),private_plan_value(size,tile,first,caps,limits)==Ok(plan),
ensures private_grid_shape(plan.grid),private_precinct_wf(plan.precinct),plan.component.component==0,
{
let grid=part2_spatial_packet_grid_from_components(size,&first.component_coding_styles,first.coding_style.layers,limits,Some(tile),0).get_Ok_0();
private_plan_grid_fields(size,tile,first,caps,limits,grid);
let metadata=part2_component_plan_metadata_owned(size,&first.component_coding_styles,first.component_quantizations,&first.roi_shifts,0,(tile,0),part2_profile_force_ht(caps)).get_Ok_0();
let region=private_plan_region(size,tile,metadata).get_Ok_0();
let context=private_plan_subband_context(metadata,region,caps,limits);
let lattice=private_subband_lattice(context).get_Ok_0();
private_rows_value_fields(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0);
assert forall|i:int|0<=i<plan.precinct.logical.decoders.len() implies #[trigger] private_ht_state_wf(PrivateHtDecoderState {
    logical:plan.precinct.logical.decoders[i],packed:plan.precinct.packed[i],
}) by {
    let band=private_subband_value(context).get_Ok_0();
    assert(private_ht_state_wf(band.rows.decoders[i]));
}
}

pub(crate) proof fn private_plan_metadata_fields(size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,
    caps:Option<(u32,Seq<u16>)>,metadata:Part2ComponentPlanMetadata)
    requires private_ht_eligible(size,tile,seq![first],caps,None),
        part2_component_plan_metadata_owned(size,&first.component_coding_styles,first.component_quantizations,&first.roi_shifts,
            0,(tile,0),part2_profile_force_ht(caps))==Ok(metadata),
    ensures metadata.output_resolution==0,metadata.coding_style.decomposition_levels==0,
        metadata.tier1_style.force_high_throughput,
        matches!(metadata.tier1_style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),
        metadata.subbands.len()==1,
        (match metadata.subbands[0].orientation{crate::tier1::SubbandOrientation::Ll=>true,_=>false}),
        metadata.bounds.x0==0,metadata.bounds.y0==0,
        metadata.subbands[0].x0==0,metadata.subbands[0].y0==0,
        metadata.subbands[0].width>0,metadata.subbands[0].height>0,
{
    let style=crate::codestream::component_coding_style_result(&first.component_coding_styles,0).get_Ok_0();
    crate::codestream::resolution_selectors_known_fields(style);
    reveal_with_fuel(part2_subband_vector_run,2);
    reveal_with_fuel(part2_subband_count_run,2);
    reveal_with_fuel(part2_resolution_scale_prefix,1);
}

pub(crate) proof fn private_plan_resolution_fields(size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,
    caps:Option<(u32,Seq<u16>)>,metadata:Part2ComponentPlanMetadata,data:Part2ResolutionPlanMetadata)
    requires private_ht_eligible(size,tile,seq![first],caps,None),
        part2_component_plan_metadata_owned(size,&first.component_coding_styles,first.component_quantizations,&first.roi_shifts,
            0,(tile,0),part2_profile_force_ht(caps))==Ok(metadata),
        part2_resolution_plan_metadata(size,metadata.coding_style,0,(tile,0),[metadata.bounds.x0,metadata.bounds.y0])==Ok(data),
    ensures data.first_subband==0,data.subband_count==1,data.precincts_in_resolution==1,
        data.first_precinct==[0u32,0u32],data.band_size[0]>0,data.band_size[1]>0,
        part2_planned_subband_lattice([0,0,data.band_size[0],data.band_size[1]],data.block_size,metadata.subbands[0])!=Ok(None),
{
    private_plan_metadata_fields(size,tile,first,caps,metadata);
    crate::codestream::resolution_selectors_known_fields(metadata.coding_style);
}

pub(crate) proof fn private_block_reference(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    before:PrivateHtBlockRows,column:u32,row:u32,total:u64)
    requires matches!(context.geometry.orientation,crate::tier1::SubbandOrientation::Ll),
        matches!(context.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),context.style.force_high_throughput,
        before.decoders.len()==before.placements.len(),before.placements.len()<usize::MAX,
    ensures private_rows_public_outcome(private_block_value(context,lattice,before,column,row),total)==
        part2_planned_codeblock_cell(lattice.grid,lattice.clip,[column,row],context.geometry,context.style,
            (context.allowed,context.bound,true),(0,0),private_rows_public(before,total)),
{
    if let Ok(geometry)=part2_planned_codeblock_geometry(lattice.grid,lattice.clip,[column,row]){
        private_ht_initial_equivalent(private_block_context(context,geometry));
        if let Ok(decoder)=private_ht_initial_value(private_block_context(context,geometry)){
            assert(before.decoders.push(decoder).map_values(|d:PrivateHtDecoderState|d.logical)
                =~= before.decoders.map_values(|d:PrivateHtDecoderState|d.logical).push(decoder.logical));
        }
    }
}

pub(crate) proof fn private_columns_reference(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    before:PrivateHtBlockRows,row:u32,column:u32,total:u64)
    requires matches!(context.geometry.orientation,crate::tier1::SubbandOrientation::Ll),
        matches!(context.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),context.style.force_high_throughput,
        row<lattice.blocks[1],column<=lattice.blocks[0],
        before.decoders.len()==before.placements.len(),
        before.placements.len()==row as nat*lattice.blocks[0] as nat+column as nat,
        lattice.blocks[0] as nat*lattice.blocks[1] as nat<=usize::MAX,
    ensures private_rows_public_outcome(private_block_columns_value(context,lattice,before,row,column),total)==
        part2_planned_codeblock_columns(lattice.grid,lattice.clip,lattice.blocks[0],context.geometry,context.style,
            (context.allowed,context.bound,true),(0,0),row,column as nat,private_rows_public(before,total)),
        match private_block_columns_value(context,lattice,before,row,column){Err(_)=>true,Ok(after)=>
            after.decoders.len()==after.placements.len() && after.placements.len()==(row as nat+1)*lattice.blocks[0] as nat},
    decreases lattice.blocks[0] as nat-column as nat,
{
    reveal_with_fuel(private_block_columns_value,1);reveal_with_fuel(part2_planned_codeblock_columns,1);
    assert((row as nat)*(lattice.blocks[0] as nat)+(lattice.blocks[0] as nat)==
        (row as nat+1)*(lattice.blocks[0] as nat)) by(nonlinear_arith);
    if column<lattice.blocks[0]{
        assert(before.placements.len()<usize::MAX) by(nonlinear_arith)
            requires row<lattice.blocks[1],column<lattice.blocks[0],
                before.placements.len()==row as nat*lattice.blocks[0] as nat+column as nat,
                lattice.blocks[0] as nat*lattice.blocks[1] as nat<=usize::MAX;
        private_block_reference(context,lattice,before,column,row,total);
        if let Ok(after)=private_block_value(context,lattice,before,column,row){
            private_columns_reference(context,lattice,after,row,(column+1) as u32,total);
        }
    }
}

pub(crate) proof fn private_rows_reference(context:PrivateHtSubbandContext,lattice:Part2PlannedSubbandLattice,
    before:PrivateHtBlockRows,row:u32,total:u64)
    requires matches!(context.geometry.orientation,crate::tier1::SubbandOrientation::Ll),
        matches!(context.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),context.style.force_high_throughput,
        row<=lattice.blocks[1],before.decoders.len()==before.placements.len(),
        before.placements.len()==row as nat*lattice.blocks[0] as nat,
        lattice.blocks[0] as nat*lattice.blocks[1] as nat<=usize::MAX,
    ensures private_rows_public_outcome(private_block_rows_value(context,lattice,before,row),total)==
        part2_planned_codeblock_rows(lattice.grid,lattice.clip,lattice.blocks,context.geometry,context.style,
            (context.allowed,context.bound,true),(0,0),row as nat,private_rows_public(before,total)),
        match private_block_rows_value(context,lattice,before,row){Err(_)=>true,Ok(after)=>
            after.decoders.len()==after.placements.len() && after.placements.len()==lattice.blocks[1] as nat*lattice.blocks[0] as nat},
    decreases lattice.blocks[1] as nat-row as nat,
{
    reveal_with_fuel(private_block_rows_value,1);reveal_with_fuel(part2_planned_codeblock_rows,1);
    if row<lattice.blocks[1]{
        private_columns_reference(context,lattice,before,row,0,total);
        if let Ok(after)=private_block_columns_value(context,lattice,before,row,0){
            private_rows_reference(context,lattice,after,(row+1) as u32,total);
        }
    }
}

    pub(crate) proof fn private_plan_reference(size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,
        caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits)
        requires private_ht_eligible(size,tile,seq![first],caps,None),
        ensures (match private_plan_value(size,tile,first,caps,limits){
            Err(error)=>Err(error),Ok(plan)=>Ok(private_plan_public_view(plan,tile,first)),
        })==part2_progression_tile_plan_owned(size,first.coding_style,&first.component_coding_styles,
            first.component_quantizations,&first.roi_shifts,(tile,0),
            (part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps),true),limits),
    {
        crate::codestream::selection_geometry_known_fields(size);
        let style=crate::codestream::component_coding_style_result(&first.component_coding_styles,0).get_Ok_0();
        crate::codestream::resolution_selectors_known_fields(style);
        reveal_with_fuel(part2_tile_plan_components,2);
        if let Ok(metadata)=part2_component_plan_metadata_owned(size,&first.component_coding_styles,first.component_quantizations,
            &first.roi_shifts,0,(tile,0),part2_profile_force_ht(caps)){
            private_plan_metadata_fields(size,tile,first,caps,metadata);
            private_component_reference(size,tile,first,caps,limits,metadata);
            if let Ok(component)=part2_planned_component_owned(size,&first.component_coding_styles,first.component_quantizations,&first.roi_shifts,
                0,(tile,0),(part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps),true),
                Seq::empty(),0,limits){
                assert(Seq::<Part1PreparePlan>::empty().push(component.component) =~= seq![component.component]);
            }
        }

    pub(crate) open spec fn private_subband_public(band:PrivateHtSubbandState)->Part2PlannedSubbandExecution {
        Part2PlannedSubbandExecution {
            execution:Some(Part2PacketSubbandExecution {
                orientation:band.geometry.orientation,across:band.across,down:band.down,
                maximum_zero:band.geometry.significant_bitplanes,decoders:band.rows.decoders.map_values(|d:PrivateHtDecoderState|d.logical),
            }),placements:band.rows.placements,decoder_index:band.rows.placements.len() as usize,
            planned_code_blocks:band.rows.decoders.len() as u64,
        }
    }

    pub(crate) proof fn private_subband_reference(context:PrivateHtSubbandContext,limits:&crate::ResourceLimits)
        requires context.blocks==crate::limits::resource_code_block_limit(limits),context.work==crate::limits::resource_work_limit(limits),
            (match context.geometry.orientation{crate::tier1::SubbandOrientation::Ll=>true,_=>false}),
            matches!(context.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),context.style.force_high_throughput,
            part2_planned_subband_lattice(context.band,context.block,context.geometry)!=Ok(None),
        ensures (match private_subband_value(context){Err(error)=>Err(error),Ok(band)=>Ok(private_subband_public(band))})==
            part2_planned_subband_execution(context.band,context.block,context.geometry,context.style,
                (context.allowed,context.bound,true),(0,0,0),Seq::empty(),0,true,limits),
    {
        if let Ok(lattice)=private_subband_lattice(context){
            if let Ok(count)=private_subband_count(context,lattice){
                private_rows_reference(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0,count as u64);
                assert(Seq::<PrivateHtDecoderState>::empty().map_values(|decoder:PrivateHtDecoderState|decoder.logical) =~= Seq::empty());
                assert((lattice.blocks[0] as nat)*(lattice.blocks[1] as nat)==
                    (lattice.blocks[1] as nat)*(lattice.blocks[0] as nat)) by(nonlinear_arith);
                let rows=private_block_rows_value(context,lattice,PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()},0);
                assert(private_rows_public_outcome(rows,count as u64)==part2_planned_codeblocks(
                    lattice.grid,lattice.clip,lattice.blocks,context.geometry,context.style,(context.allowed,context.bound,true),
                    (0,0,0),Seq::empty(),0,true,limits));
            }
        }
    }

    pub(crate) open spec fn private_planned_precinct_value(metadata:Part2ComponentPlanMetadata,region:([u32;4],[u32;2]),
        caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits)->Result<Part2PlannedPrecinct,crate::DecodeError> {
        match private_subband_value(private_plan_subband_context(metadata,region,caps,limits)){
            Err(error)=>Err(error),Ok(band)=>match private_precinct_initial_value(private_plan_precinct_context(metadata,band,limits)){
                Err(error)=>Err(error),Ok(precinct)=>Ok(Part2PlannedPrecinct {
                    precinct:precinct.logical,placements:band.rows.placements,planned_code_blocks:band.rows.decoders.len() as u64,
                }),
            },
        }
    }

    pub(crate) proof fn private_planned_precinct_reference(metadata:Part2ComponentPlanMetadata,region:([u32;4],[u32;2]),
        caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits)
        requires metadata.subbands.len()==1,
            (match metadata.subbands[0].orientation{crate::tier1::SubbandOrientation::Ll=>true,_=>false}),
            matches!(metadata.tier1_style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),metadata.tier1_style.force_high_throughput,
            part2_planned_subband_lattice(region.0,region.1,metadata.subbands[0])!=Ok(None),
        ensures private_planned_precinct_value(metadata,region,caps,limits)==part2_planned_precinct(region.0,region.1,metadata.subbands,(0,1),
            metadata.tier1_style,(part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),true),(0,0,0,0),Seq::empty(),0,true,limits),
    {
        let context=private_plan_subband_context(metadata,region,caps,limits);
        private_subband_reference(context,limits);
        reveal_with_fuel(part2_planned_precinct_rows,2);
        if let Ok(band)=private_subband_value(context){
            private_precinct_reference(private_plan_precinct_context(metadata,band,limits),limits);
        }
    }

    pub(crate) open spec fn private_component_public_value(metadata:Part2ComponentPlanMetadata,region:([u32;4],[u32;2]),
        caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits)->Result<Part2PlannedComponent,crate::DecodeError> {
        match private_planned_precinct_value(metadata,region,caps,limits){
            Err(error)=>Err(error),Ok(precinct)=>Ok(Part2PlannedComponent {
                component:Part1PreparePlan {
                    component:0,x:metadata.x,y:metadata.y,width:metadata.width,height:metadata.height,
                    resolution:metadata.output_resolution,subbands:metadata.subbands,placements:precinct.placements,
                },precincts:seq![precinct.precinct],planned_code_blocks:precinct.planned_code_blocks,
            }),
        }
    }

    pub(crate) proof fn private_component_reference(size:&crate::codestream::ImageSize,tile:u16,first:Part2OwnedTilePart,
        caps:Option<(u32,Seq<u16>)>,limits:&crate::ResourceLimits,metadata:Part2ComponentPlanMetadata)
        requires private_ht_eligible(size,tile,seq![first],caps,None),
            part2_component_plan_metadata_owned(size,&first.component_coding_styles,first.component_quantizations,&first.roi_shifts,
                0,(tile,0),part2_profile_force_ht(caps))==Ok(metadata),
        ensures (match private_plan_region(size,tile,metadata){
            Err(error)=>Err(error),Ok(region)=>private_component_public_value(metadata,region,caps,limits),
        })==part2_planned_component_owned(size,&first.component_coding_styles,first.component_quantizations,&first.roi_shifts,
            0,(tile,0),(part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps),true),
            Seq::empty(),0,limits),
    {
        private_plan_metadata_fields(size,tile,first,caps,metadata);
        reveal_with_fuel(part2_component_plan_resolutions,2);
        reveal_with_fuel(part2_component_plan_precincts,2);
        if let Ok(data)=part2_resolution_plan_metadata(size,metadata.coding_style,0,(tile,0),[metadata.bounds.x0,metadata.bounds.y0]){
            private_plan_resolution_fields(size,tile,first,caps,metadata,data);
            if let Ok(region)=private_plan_region(size,tile,metadata){
                private_planned_precinct_reference(metadata,region,caps,limits);
            }
        }
    }
    }
}
