//! Complete tile POC scope, bounded layer frontiers and declaration novelty.
use super::*;
verus! {
pub(crate) open spec fn part1_poc_charge(work: u64, limits: &crate::ResourceLimits)
    -> (Result<(), crate::DecodeError>, u64) {
    if work == u64::MAX {
        (Err(part1_codestream_malformed(0, crate::MalformedKind::ArithmeticOverflow)), work)
    } else {
        let next = (work+1) as u64;
        (if next > crate::limits::resource_work_limit(limits) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits,
                limit: crate::limits::resource_work_limit(limits), actual: next })
        } else { Ok(()) }, next)
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_poc_frontier_records(
    records: Seq<crate::codestream::ProgressionChange>, coordinate: (u16,u8),
    end: usize, index: usize, frontier: u16, work: u64, limits: &crate::ResourceLimits,
) -> (Result<u16,crate::DecodeError>,u64)
    decreases end as int - index as int,
{
    if index >= end { (Ok(frontier),work) }
    else {
        let charge=part1_poc_charge(work,limits);
        match charge.0 {
            Err(error)=>(Err(error),charge.1),
            Ok(())=>if index >= records.len() {
                (Err(part1_codestream_malformed(0,crate::MalformedKind::InvalidProgressionOrderChange)),charge.1)
            } else {
                let record=records[index as int];
                let next=if crate::codestream::progression_change_contains(record,0,coordinate.1,coordinate.0)
                    && record.layer_end > frontier {record.layer_end}else{frontier};
                part1_poc_frontier_records(records,coordinate,end,(index+1) as usize,next,charge.1,limits)
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_poc_frontier_run(
    parts: Seq<Part1TilePartPayload>, tile: u16, coordinate: (u16,u8), prefix: (usize,usize),
    index: usize, frontier: u16, work: u64, limits: &crate::ResourceLimits,
) -> (Result<u16,crate::DecodeError>,u64)
    decreases parts.len() - index as int,
{
    if index >= parts.len() || index > prefix.0 { (Ok(frontier),work) } else {
        let charge=part1_poc_charge(work,limits);
        match charge.0 {
            Err(error)=>(Err(error),charge.1),Ok(())=>{
                let part=parts[index as int];
                let marked=if part.tile_index != tile {(Ok(frontier),charge.1)}else{
                    let end=if index==prefix.0 && prefix.1 < part.progression_changes.len() {
                        prefix.1
                    }else{part.progression_changes.len() as usize};
                    part1_poc_frontier_records(part.progression_changes,coordinate,end,0,frontier,charge.1,limits)
                };
                match marked.0 {
                    Err(error)=>marked,
                    Ok(value)=>if index==usize::MAX {
                        (Err(part1_codestream_malformed(0,crate::MalformedKind::ArithmeticOverflow)),marked.1)
                    }else{part1_poc_frontier_run(parts,tile,coordinate,prefix,(index+1) as usize,value,marked.1,limits)},
                }
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_poc_first_run(
    parts: Seq<Part1TilePartPayload>, tile: u16, index: usize, work: u64, limits: &crate::ResourceLimits,
) -> (Result<bool,crate::DecodeError>,u64)
    decreases parts.len() - index as int,
{
    if index >= parts.len() {(Ok(false),work)}else{
        let charge=part1_poc_charge(work,limits);
        match charge.0 {
            Err(error)=>(Err(error),charge.1),
            Ok(())=>if parts[index as int].tile_index==tile && parts[index as int].tile_part_index==0 {
                (Ok(parts[index as int].has_progression_marker),charge.1)
            }else if index==usize::MAX{
                (Err(part1_codestream_malformed(0,crate::MalformedKind::ArithmeticOverflow)),charge.1)
            }else{part1_poc_first_run(parts,tile,(index+1) as usize,charge.1,limits)},
        }
    }
}

pub(crate) open spec fn part1_poc_resolutions(part: Part1TilePartPayload, component: u16)
    -> Result<u8,crate::DecodeError> {
    let styles=crate::codestream::tile_part_native_styles(part.component_coding_styles);
    match crate::codestream::component_coding_style_result(&styles,component) {
        Err(error)=>Err(error),Ok(style)=>if style.decomposition_levels==u8::MAX {
            Err(part1_codestream_malformed(0,crate::MalformedKind::ArithmeticOverflow))
        }else{Ok((style.decomposition_levels+1) as u8)},
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_poc_novel_resolutions(
    parts: Seq<Part1TilePartPayload>, index: usize, record_index: usize,
    component: u16, resolution: u8, resolutions: u8, work: u64, limits: &crate::ResourceLimits,
) -> (Result<bool,crate::DecodeError>,u64)
    decreases resolutions - resolution,
{
    let part=parts[index as int];let record=part.progression_changes[record_index as int];
    if resolution >= record.resolution_end || resolution >= resolutions {(Ok(false),work)}else{
        let before=part1_poc_frontier_run(parts,part.tile_index,(component,resolution),(index,record_index),0,0,work,limits);
        match before.0 {
            Err(error)=>(Err(error),before.1),
            Ok(value)=>if (if record.layer_end < part.coding_style.layers {record.layer_end}else{part.coding_style.layers}) > value {(Ok(true),before.1)}
                else{part1_poc_novel_resolutions(parts,index,record_index,component,(resolution+1) as u8,resolutions,before.1,limits)},
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_poc_novel_components(
    parts: Seq<Part1TilePartPayload>, index: usize, record_index: usize,
    component: u16, work: u64, limits: &crate::ResourceLimits,
) -> (Result<bool,crate::DecodeError>,u64)
    decreases parts[index as int].progression_changes[record_index as int].component_end - component,
{
    let part=parts[index as int];let record=part.progression_changes[record_index as int];
    if component >= record.component_end || component >= part.component_coding_styles.0 {(Ok(false),work)}else{
        match part1_poc_resolutions(part,component) {
            Err(error)=>(Err(error),work),
            Ok(resolutions)=>{
                let found=part1_poc_novel_resolutions(parts,index,record_index,component,record.resolution_start,resolutions,work,limits);
                match found.0 {
                    Err(error)=>found,Ok(true)=>found,
                    Ok(false)=>part1_poc_novel_components(parts,index,record_index,(component+1) as u16,found.1,limits),
                }
            },
        }
    }
}

pub(crate) open spec fn part1_poc_novel_record(parts: Seq<Part1TilePartPayload>,index:usize,record_index:usize,work:u64,limits:&crate::ResourceLimits)
    ->(Result<bool,crate::DecodeError>,u64) {
    if index>=parts.len(){(Err(part1_codestream_malformed(0,crate::MalformedKind::InvalidTilePart)),work)}
    else if record_index>=parts[index as int].progression_changes.len(){
        (Err(part1_codestream_malformed(0,crate::MalformedKind::InvalidProgressionOrderChange)),work)
    }else{part1_poc_novel_components(parts,index,record_index,
        parts[index as int].progression_changes[record_index as int].component_start,work,limits)}
}

#[verifier::opaque]
pub(crate) open spec fn part1_poc_complete_resolutions(
    parts:Seq<Part1TilePartPayload>,index:usize,component:u16,resolution:u8,resolutions:u8,work:u64,limits:&crate::ResourceLimits,
) ->(Result<(),crate::DecodeError>,u64)
    decreases resolutions - resolution,
{
    if resolution>=resolutions{(Ok(()),work)}else{
        let part=parts[index as int];
        let covered=part1_poc_frontier_run(parts,part.tile_index,(component,resolution),(parts.len() as usize,0),0,0,work,limits);
        match covered.0 {
            Err(error)=>(Err(error),covered.1),
            Ok(value)=>if value<part.coding_style.layers{
                (Err(part1_codestream_malformed(0,crate::MalformedKind::InvalidProgressionOrderChange)),covered.1)
            }else{part1_poc_complete_resolutions(parts,index,component,(resolution+1) as u8,resolutions,covered.1,limits)},
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_poc_complete_components(
    parts:Seq<Part1TilePartPayload>,index:usize,component:u16,work:u64,limits:&crate::ResourceLimits,
) ->(Result<(),crate::DecodeError>,u64)
    decreases parts[index as int].component_coding_styles.0 - component,
{
    let part=parts[index as int];
    if component>=part.component_coding_styles.0{(Ok(()),work)}else{
        match part1_poc_resolutions(part,component) {
            Err(error)=>(Err(error),work),
            Ok(resolutions)=>{
                let covered=part1_poc_complete_resolutions(parts,index,component,0,resolutions,work,limits);
                match covered.0 {
                    Err(error)=>covered,
                    Ok(())=>part1_poc_complete_components(parts,index,(component+1) as u16,covered.1,limits),
                }
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_poc_coverage_records(
    parts:Seq<Part1TilePartPayload>,index:usize,record:usize,work:u64,limits:&crate::ResourceLimits,
) ->(Result<(),crate::DecodeError>,u64)
    decreases parts[index as int].progression_changes.len() - record as int,
{
    if record>=parts[index as int].progression_changes.len(){(Ok(()),work)}else{
        let novel=part1_poc_novel_record(parts,index,record,work,limits);
        match novel.0 {
            Err(error)=>(Err(error),novel.1),
            Ok(false)=>(Err(part1_codestream_malformed(0,crate::MalformedKind::InvalidProgressionOrderChange)),novel.1),
            Ok(true)=>if record==usize::MAX{
                (Err(part1_codestream_malformed(0,crate::MalformedKind::ArithmeticOverflow)),novel.1)
            }else{part1_poc_coverage_records(parts,index,(record+1) as usize,novel.1,limits)},
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_poc_coverage_run(parts:Seq<Part1TilePartPayload>,index:usize,work:u64,limits:&crate::ResourceLimits)
    ->(Result<(),crate::DecodeError>,u64)
    decreases parts.len() - index as int,
{
    if index>=parts.len(){(Ok(()),work)}else{
        let charge=part1_poc_charge(work,limits);
        match charge.0 {
            Err(error)=>charge,Ok(())=>{
                let part=parts[index as int];
                let complete=if part.tile_part_index==0 && part.progression_changes.len()>0{
                    part1_poc_complete_components(parts,index,0,charge.1,limits)
                }else{(Ok(()),charge.1)};
                match complete.0 {
                    Err(error)=>complete,Ok(())=>{
                        let records=if part.has_progression_marker{
                            let first=part1_poc_first_run(parts,part.tile_index,0,complete.1,limits);
                            match first.0 {
                                Err(error)=>(Err(error),first.1),
                                Ok(false)=>(Err(part1_codestream_malformed(0,crate::MalformedKind::InvalidMarkerOrder)),first.1),
                                Ok(true)=>part1_poc_coverage_records(parts,index,0,first.1,limits),
                            }
                        }else{complete};
                        match records.0 {
                            Err(error)=>records,
                            Ok(())=>if index==usize::MAX{
                                (Err(part1_codestream_malformed(0,crate::MalformedKind::ArithmeticOverflow)),records.1)
                            }else{part1_poc_coverage_run(parts,(index+1) as usize,records.1,limits)},
                        }
                    },
                }
            },
        }
    }
}

pub(crate) open spec fn part1_complete_poc_coverage(parts:Seq<Part1TilePartPayload>,limits:&crate::ResourceLimits)
    ->Result<(),crate::DecodeError> {
    part1_poc_coverage_run(parts,0,0,limits).0
}
}
