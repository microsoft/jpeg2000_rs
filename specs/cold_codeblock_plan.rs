//! Ordered real configured-decoder cells, columns and rows.
use super::*;
verus! {
pub(crate) open spec fn part2_tier1_cell_context(grid:[u32;4],clip:[u32;4],block:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),before:Part2PlannedCodeBlocks,geometry:(u32,u32,u16,u16))->Part2Tier1CallContext {
    Part2Tier1CallContext {width:geometry.2,height:geometry.3,significant:subband.significant_bitplanes,orientation:subband.orientation,style,
        allowed:policy.0,bound:policy.1,pack_ht_checkpoint:policy.2,grid,clip,block,indices,before}
}
pub(crate) open spec fn part2_codeblock_growth_context(grid:[u32;4],clip:[u32;4],block:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),before:Part2PlannedCodeBlocks,
    geometry:(u32,u32,u16,u16),placements:bool)->Part2PlanningCapacityContext {
    Part2PlanningCapacityContext::CodeBlockGrowth {
        cell:part2_tier1_cell_context(grid,clip,block,subband,style,policy,indices,before,geometry),
        subband,geometry,placements,
    }
}
pub(crate) open spec fn part2_codeblock_after_decoder_growth_run(grid:[u32;4],clip:[u32;4],block:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),before:Part2PlannedCodeBlocks,
    geometry:(u32,u32,u16,u16),events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedCodeBlocks> {
    if geometry.0<subband.x0 || geometry.1<subband.y0 {Some((Err(part1_block_placement_error(true)),events))}
    else {part2_jpip_snapshot_bind(
        part2_planning_capacity_run(part2_codeblock_growth_context(grid,clip,block,subband,style,policy,indices,before,geometry,true),events),
        |_:(),rest|Some((part2_planned_codeblock_cell(grid,clip,block,subband,style,policy,indices,before),rest)))}
}
pub(crate) open spec fn part2_codeblock_after_decoder_run(grid:[u32;4],clip:[u32;4],block:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),before:Part2PlannedCodeBlocks,
    geometry:(u32,u32,u16,u16),events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedCodeBlocks> {
    part2_jpip_snapshot_bind(
        part2_planning_capacity_run(part2_codeblock_growth_context(grid,clip,block,subband,style,policy,indices,before,geometry,false),events),
        |_:(),rest|part2_codeblock_after_decoder_growth_run(grid,clip,block,subband,style,policy,indices,before,geometry,rest))
}
pub(crate) open spec fn part2_codeblock_cell_run(grid:[u32;4],clip:[u32;4],block:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),before:Part2PlannedCodeBlocks,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedCodeBlocks> {
    match part2_planned_codeblock_geometry(grid,clip,block) {
        Err(error)=>Some((Err(error),events)),
        Ok(geometry)=>part2_jpip_snapshot_bind(part2_tier1_call_run(part2_tier1_cell_context(grid,clip,block,subband,style,policy,indices,before,geometry),events),
            |_:Tier1DecoderState,rest|part2_codeblock_after_decoder_run(grid,clip,block,subband,style,policy,indices,before,geometry,rest)),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_codeblock_cell_result(grid:[u32;4],clip:[u32;4],block:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),before:Part2PlannedCodeBlocks,result:Result<Part2PlannedCodeBlocks,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_codeblock_cell_run(grid,clip,block,subband,style,policy,indices,before,events),result)
}
pub(crate) proof fn part2_codeblock_after_decoder_normal(grid:[u32;4],clip:[u32;4],block:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),before:Part2PlannedCodeBlocks,geometry:(u32,u32,u16,u16))
    requires part2_planned_codeblock_geometry(grid,clip,block)==Ok(geometry),
        part2_tier1_configured_decoder(geometry.2,geometry.3,subband.significant_bitplanes,subband.orientation,style,policy.0,policy.1).is_ok(),
    ensures part2_cold_framed(
        |events|part2_codeblock_after_decoder_run(grid,clip,block,subband,style,policy,indices,before,geometry,events),
        part2_planned_codeblock_cell(grid,clip,block,subband,style,policy,indices,before)),
{
    reveal(part2_planning_capacity_result);
    let result=part2_planned_codeblock_cell(grid,clip,block,subband,style,policy,indices,before);
    let first=part2_codeblock_growth_context(grid,clip,block,subband,style,policy,indices,before,geometry,false);
    let last=part2_codeblock_growth_context(grid,clip,block,subband,style,policy,indices,before,geometry,true);
    part2_planning_capacity_observed(first,Ok(()));
    if geometry.0<subband.x0 || geometry.1<subband.y0 {part2_cold_pure(result);}
    else {
        part2_planning_capacity_observed(last,Ok(()));
        part2_cold_pure(result);
        part2_cold_bind(|events|part2_planning_capacity_run(last,events),
            |_:(),rest|Some((result,rest)),Ok(()),result);
        part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_planning_capacity_run(last,events),
            |_:(),rest|Some((result,rest))),result);
    }
    part2_cold_bind(|events|part2_planning_capacity_run(first,events),
        |_:(),rest|part2_codeblock_after_decoder_growth_run(grid,clip,block,subband,style,policy,indices,before,geometry,rest),Ok(()),result);
    part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_planning_capacity_run(first,events),
        |_:(),rest|part2_codeblock_after_decoder_growth_run(grid,clip,block,subband,style,policy,indices,before,geometry,rest)),result);
}
pub(crate) proof fn part2_codeblock_cell_normal(grid:[u32;4],clip:[u32;4],block:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),before:Part2PlannedCodeBlocks)
    ensures part2_codeblock_cell_result(grid,clip,block,subband,style,policy,indices,before,part2_planned_codeblock_cell(grid,clip,block,subband,style,policy,indices,before)),
{
    reveal(part2_codeblock_cell_result);
    let result=part2_planned_codeblock_cell(grid,clip,block,subband,style,policy,indices,before);
    match part2_planned_codeblock_geometry(grid,clip,block){
        Err(_)=>{part2_cold_pure::<Part2PlannedCodeBlocks>(result);},
        Ok(geometry)=>{
            let context=part2_tier1_cell_context(grid,clip,block,subband,style,policy,indices,before,geometry);
            part2_tier1_call_normal(context);
            let decoder=part2_with_ht_checkpoint(part2_tier1_configured_decoder(geometry.2,geometry.3,subband.significant_bitplanes,subband.orientation,style,policy.0,policy.1),policy.2);
            if decoder.is_ok(){
                part2_codeblock_after_decoder_normal(grid,clip,block,subband,style,policy,indices,before,geometry);
                part2_decode_eta(|events|part2_codeblock_after_decoder_run(grid,clip,block,subband,style,policy,indices,before,geometry,events),result);
            }
            part2_cold_bind(|events|part2_tier1_call_run(context,events),
                |_:Tier1DecoderState,rest|part2_codeblock_after_decoder_run(grid,clip,block,subband,style,policy,indices,before,geometry,rest),decoder,result);
        },
    }
}
pub(crate) proof fn part2_codeblock_cell_decoder_observed(grid:[u32;4],clip:[u32;4],block:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),before:Part2PlannedCodeBlocks,geometry:(u32,u32,u16,u16),result:Result<Tier1DecoderState,crate::DecodeError>)
    requires part2_planned_codeblock_geometry(grid,clip,block)==Ok(geometry),
        part2_tier1_configured_checkpoint_result(geometry.2,geometry.3,subband.significant_bitplanes,subband.orientation,style,policy.0,policy.1,policy.2,result),
    ensures match result {Err(error)=>part2_codeblock_cell_result(grid,clip,block,subband,style,policy,indices,before,Err(error)),Ok(_)=>true},
{
    let context=part2_tier1_cell_context(grid,clip,block,subband,style,policy,indices,before,geometry);
    part2_tier1_call_observed(context,result);
    if let Err(error)=result {
        reveal(part2_codeblock_cell_result);
        part2_cold_bind(|events|part2_tier1_call_run(context,events),
            |_:Tier1DecoderState,rest|part2_codeblock_after_decoder_run(grid,clip,block,subband,style,policy,indices,before,geometry,rest),Err(error),Err(error));
    }
}
pub(crate) proof fn part2_codeblock_cell_growth_refused(grid:[u32;4],clip:[u32;4],block:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),before:Part2PlannedCodeBlocks,
    geometry:(u32,u32,u16,u16),decoder:Tier1DecoderState,placements:bool,error:crate::DecodeError)
    requires part2_planned_codeblock_geometry(grid,clip,block)==Ok(geometry),
        part2_tier1_configured_checkpoint_result(geometry.2,geometry.3,subband.significant_bitplanes,subband.orientation,style,policy.0,policy.1,policy.2,Ok(decoder)),
        part2_planning_capacity_result(part2_codeblock_growth_context(grid,clip,block,subband,style,policy,indices,before,geometry,placements),Err(error)),
        placements ==> geometry.0>=subband.x0 && geometry.1>=subband.y0
            && part2_planning_capacity_result(part2_codeblock_growth_context(grid,clip,block,subband,style,policy,indices,before,geometry,false),Ok(())),
    ensures part2_codeblock_cell_result(grid,clip,block,subband,style,policy,indices,before,Err(error)),
{
    reveal(part2_codeblock_cell_result);
    reveal(part2_planning_capacity_result);
    let context=part2_tier1_cell_context(grid,clip,block,subband,style,policy,indices,before,geometry);
    part2_tier1_call_observed(context,Ok(decoder));
    let result=part2_planned_codeblock_cell(grid,clip,block,subband,style,policy,indices,before);
    let first=part2_codeblock_growth_context(grid,clip,block,subband,style,policy,indices,before,geometry,false);
    let last=part2_codeblock_growth_context(grid,clip,block,subband,style,policy,indices,before,geometry,true);
    if placements {
        part2_cold_bind(|events|part2_planning_capacity_run(last,events),
            |_:(),rest|Some((result,rest)),Err(error),Err(error));
        part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_planning_capacity_run(last,events),
            |_:(),rest|Some((result,rest))),Err(error));
    }
    part2_cold_bind(|events|part2_planning_capacity_run(first,events),
        |_:(),rest|part2_codeblock_after_decoder_growth_run(grid,clip,block,subband,style,policy,indices,before,geometry,rest),
        if placements {Ok(())}else{Err(error)},Err(error));
    part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_planning_capacity_run(first,events),
        |_:(),rest|part2_codeblock_after_decoder_growth_run(grid,clip,block,subband,style,policy,indices,before,geometry,rest)),Err(error));
    part2_cold_bind(|events|part2_tier1_call_run(context,events),
        |_:Tier1DecoderState,rest|part2_codeblock_after_decoder_run(grid,clip,block,subband,style,policy,indices,before,geometry,rest),
        Ok(decoder),Err(error));
}
pub(crate) proof fn part2_codeblock_cell_frames(grid:[u32;4],clip:[u32;4],block:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),before:Part2PlannedCodeBlocks,result:Result<Part2PlannedCodeBlocks,crate::DecodeError>)
    requires part2_codeblock_cell_result(grid,clip,block,subband,style,policy,indices,before,result),
    ensures part2_cold_framed(|events|part2_codeblock_cell_run(grid,clip,block,subband,style,policy,indices,before,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedCodeBlocks>|
            (forall|events| #[trigger] other(events)==part2_codeblock_cell_run(grid,clip,block,subband,style,policy,indices,before,events))
            ==> #[trigger] part2_cold_framed(other,result),
{reveal(part2_codeblock_cell_result);part2_decode_eta(|events|part2_codeblock_cell_run(grid,clip,block,subband,style,policy,indices,before,events),result);}
#[verifier::opaque]
pub(crate) open spec fn part2_codeblock_columns_run(grid:[u32;4],clip:[u32;4],across:u32,subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),row:u32,column:nat,before:Part2PlannedCodeBlocks,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedCodeBlocks>
    decreases if column<across{(across as int-column) as nat}else{0nat},
{
    if column>=across{Some((Ok(before),events))}else{
        part2_jpip_snapshot_bind(part2_codeblock_cell_run(grid,clip,[column as u32,row],subband,style,policy,indices,before,events),
            |after:Part2PlannedCodeBlocks,rest|part2_codeblock_columns_run(grid,clip,across,subband,style,policy,indices,row,column+1,after,rest))
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_codeblock_rows_run(grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),row:nat,before:Part2PlannedCodeBlocks,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedCodeBlocks>
    decreases if row<blocks[1]{(blocks[1] as int-row) as nat}else{0nat},
{
    if row>=blocks[1]{Some((Ok(before),events))}else{
        part2_jpip_snapshot_bind(part2_codeblock_columns_run(grid,clip,blocks[0],subband,style,policy,indices,row as u32,0,before,events),
            |after:Part2PlannedCodeBlocks,rest|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,indices,row+1,after,rest))
    }
}
pub(crate) proof fn part2_codeblock_columns_normal(grid:[u32;4],clip:[u32;4],across:u32,subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),row:u32,column:nat,before:Part2PlannedCodeBlocks)
    ensures part2_cold_framed(|events|part2_codeblock_columns_run(grid,clip,across,subband,style,policy,indices,row,column,before,events),
        part2_planned_codeblock_columns(grid,clip,across,subband,style,policy,indices,row,column,before)),
    decreases if column<across{(across as int-column) as nat}else{0nat},
{
    reveal_with_fuel(part2_codeblock_columns_run,1);reveal_with_fuel(part2_planned_codeblock_columns,1);reveal(part2_codeblock_cell_result);
    let result=part2_planned_codeblock_columns(grid,clip,across,subband,style,policy,indices,row,column,before);
    if column>=across{part2_cold_pure::<Part2PlannedCodeBlocks>(result);}else{
        let block=[column as u32,row];
        part2_codeblock_cell_normal(grid,clip,block,subband,style,policy,indices,before);
        let cell=part2_planned_codeblock_cell(grid,clip,block,subband,style,policy,indices,before);
        if let Ok(value)=cell{
            part2_codeblock_columns_normal(grid,clip,across,subband,style,policy,indices,row,column+1,value);
            part2_decode_eta(|events|part2_codeblock_columns_run(grid,clip,across,subband,style,policy,indices,row,column+1,value,events),
                part2_planned_codeblock_columns(grid,clip,across,subband,style,policy,indices,row,column+1,value));
        }
        part2_cold_bind(|events|part2_codeblock_cell_run(grid,clip,block,subband,style,policy,indices,before,events),
            |after:Part2PlannedCodeBlocks,rest|part2_codeblock_columns_run(grid,clip,across,subband,style,policy,indices,row,column+1,after,rest),cell,result);
    }
}
pub(crate) proof fn part2_codeblock_rows_normal(grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),row:nat,before:Part2PlannedCodeBlocks)
    ensures part2_cold_framed(|events|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,indices,row,before,events),
        part2_planned_codeblock_rows(grid,clip,blocks,subband,style,policy,indices,row,before)),
    decreases if row<blocks[1]{(blocks[1] as int-row) as nat}else{0nat},
{
    reveal_with_fuel(part2_codeblock_rows_run,1);reveal_with_fuel(part2_planned_codeblock_rows,1);
    let result=part2_planned_codeblock_rows(grid,clip,blocks,subband,style,policy,indices,row,before);
    if row>=blocks[1]{part2_cold_pure::<Part2PlannedCodeBlocks>(result);}else{
        part2_codeblock_columns_normal(grid,clip,blocks[0],subband,style,policy,indices,row as u32,0,before);
        let columns=part2_planned_codeblock_columns(grid,clip,blocks[0],subband,style,policy,indices,row as u32,0,before);
        if let Ok(value)=columns{
            part2_codeblock_rows_normal(grid,clip,blocks,subband,style,policy,indices,row+1,value);
            part2_decode_eta(|events|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,indices,row+1,value,events),
                part2_planned_codeblock_rows(grid,clip,blocks,subband,style,policy,indices,row+1,value));
        }
        part2_cold_bind(|events|part2_codeblock_columns_run(grid,clip,blocks[0],subband,style,policy,indices,row as u32,0,before,events),
            |after:Part2PlannedCodeBlocks,rest|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,indices,row+1,after,rest),columns,result);
    }
}
pub(crate) proof fn part2_codeblock_owner_start(grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool,limits:&crate::ResourceLimits,next:u64)->(prefix:Seq<Part2JpipSnapshotEvent>)
    requires part2_codeblock_owner_admit(blocks,total,selected,limits)==Ok(next),
        part2_planning_capacity_result(part2_codeblock_owner_context(grid,clip,blocks,subband,style,policy,indices,placements,total,selected),Ok(())),
    ensures part2_cold_phase(|events|part2_codeblock_owner_run(grid,clip,blocks,subband,style,policy,indices,placements,total,selected,limits,events),prefix,
        |events|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,(indices.0,indices.1),0,
            Part2PlannedCodeBlocks {decoders:Seq::empty(),placements,decoder_index:indices.2,planned_code_blocks:next},events)),
{
    reveal(part2_planning_capacity_result);
    let context=part2_codeblock_owner_context(grid,clip,blocks,subband,style,policy,indices,placements,total,selected);
    let prefix=part2_cold_witness(|events|part2_planning_capacity_run(context,events),Ok(()));
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_codeblock_owner_run(grid,clip,blocks,subband,style,policy,indices,placements,total,selected,limits,prefix+tail)
        ==part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,(indices.0,indices.1),0,
            Part2PlannedCodeBlocks {decoders:Seq::empty(),placements,decoder_index:indices.2,planned_code_blocks:next},tail) by{
        part2_cold_prefix_at(|events|part2_planning_capacity_run(context,events),prefix,Ok(()),tail);
    }
    prefix
}
pub(crate) proof fn part2_codeblock_rows_step(grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),row:nat,before:Part2PlannedCodeBlocks)
    requires row<blocks[1],
    ensures forall|events:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,indices,row,before,events)
        ==part2_jpip_snapshot_bind(part2_codeblock_columns_run(grid,clip,blocks[0],subband,style,policy,indices,row as u32,0,before,events),
            |after:Part2PlannedCodeBlocks,rest|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,indices,row+1,after,rest)),
{reveal_with_fuel(part2_codeblock_rows_run,1);}
pub(crate) proof fn part2_codeblock_columns_step(grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),row:u32,column:nat,before:Part2PlannedCodeBlocks)
    requires column<blocks[0],
    ensures forall|events:Seq<Part2JpipSnapshotEvent>|
        part2_jpip_snapshot_bind(#[trigger] part2_codeblock_columns_run(grid,clip,blocks[0],subband,style,policy,indices,row,column,before,events),
            |after:Part2PlannedCodeBlocks,rest|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,indices,row as nat+1,after,rest))
        ==part2_jpip_snapshot_bind(part2_codeblock_cell_run(grid,clip,[column as u32,row],subband,style,policy,indices,before,events),
            |after:Part2PlannedCodeBlocks,rest|part2_jpip_snapshot_bind(part2_codeblock_columns_run(grid,clip,blocks[0],subband,style,policy,indices,row,column+1,after,rest),
                |last:Part2PlannedCodeBlocks,tail|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,indices,row as nat+1,last,tail))),
{
    reveal_with_fuel(part2_codeblock_columns_run,1);
    assert forall|events:Seq<Part2JpipSnapshotEvent>|
        part2_jpip_snapshot_bind(#[trigger] part2_codeblock_columns_run(grid,clip,blocks[0],subband,style,policy,indices,row,column,before,events),
            |after:Part2PlannedCodeBlocks,rest|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,indices,row as nat+1,after,rest))
        ==part2_jpip_snapshot_bind(part2_codeblock_cell_run(grid,clip,[column as u32,row],subband,style,policy,indices,before,events),
            |after:Part2PlannedCodeBlocks,rest|part2_jpip_snapshot_bind(part2_codeblock_columns_run(grid,clip,blocks[0],subband,style,policy,indices,row,column+1,after,rest),
                |last:Part2PlannedCodeBlocks,tail|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,indices,row as nat+1,last,tail))) by{
        part2_cold_bind_associative(part2_codeblock_cell_run(grid,clip,[column as u32,row],subband,style,policy,indices,before,events),
            |after:Part2PlannedCodeBlocks,rest|part2_codeblock_columns_run(grid,clip,blocks[0],subband,style,policy,indices,row,column+1,after,rest),
            |after:Part2PlannedCodeBlocks,rest|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,indices,row as nat+1,after,rest));
    }
}
pub(crate) proof fn part2_codeblock_columns_end(grid:[u32;4],clip:[u32;4],across:u32,subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize),row:u32,column:nat,before:Part2PlannedCodeBlocks)
    requires column>=across,
    ensures forall|events:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_codeblock_columns_run(grid,clip,across,subband,style,policy,indices,row,column,before,events)==Some((Ok(before),events)),
{reveal_with_fuel(part2_codeblock_columns_run,1);}
pub(crate) proof fn part2_codeblock_owner_join(grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8,bool),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool,limits:&crate::ResourceLimits,
    root:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedCodeBlocks>,result:Result<Part2PlannedCodeBlocks,crate::DecodeError>)
    requires part2_cold_framed(root,result),forall|events| #[trigger] root(events)==part2_codeblock_owner_run(grid,clip,blocks,subband,style,policy,indices,placements,total,selected,limits,events),
    ensures part2_codeblock_owner_result(grid,clip,blocks,subband,style,policy,indices,placements,total,selected,limits,result),
{
    reveal(part2_codeblock_owner_result);
    part2_cold_framed_extensional(root,|events|part2_codeblock_owner_run(grid,clip,blocks,subband,style,policy,indices,placements,total,selected,limits,events),result);
}
}
