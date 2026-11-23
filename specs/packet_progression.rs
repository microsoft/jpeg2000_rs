use super::ht_reader_error;
use vstd::prelude::*;

verus! {

pub struct Part1PacketGrid {
    pub layers: u16,
    pub components: u16,
    pub resolutions: u8,
    pub component_resolutions: Seq<u8>,
    pub maximum_precincts_per_resolution: u32,
    pub precinct_counts: Seq<u32>,
    pub precinct_offsets: Seq<usize>,
    pub candidate_count: u64,
    pub packet_count: u64,
    pub spatial: Option<super::Part1PacketSpatialGrid>,
    pub maximum_work_units: u64,
}

pub struct Part1PacketIterator {
    pub grid: Part1PacketGrid,
    pub order: crate::codestream::ProgressionOrder,
    pub candidate_index: u64,
    pub emitted: u64,
}

pub open spec fn part1_packet_iterator_initial(
    grid: Part1PacketGrid, order: crate::codestream::ProgressionOrder,
) -> Part1PacketIterator {
    Part1PacketIterator { grid, order, candidate_index: 0, emitted: 0 }
}

pub struct Part1ProgressionPacketIterator {
    pub grid: Part1PacketGrid,
    pub changes: Seq<crate::codestream::ProgressionChange>,
    pub default: Option<Part1PacketIterator>,
    pub window_index: usize,
    pub window_candidate: u64,
    pub window_candidates: u64,
    pub emitted: u64,
}

pub struct Part1GridCountState {
    pub index: usize,
    pub component: usize,
    pub resolution: usize,
    pub total: u64,
    pub maximum: u32,
    pub offsets: Seq<usize>,
}

#[verifier::opaque]
pub open spec fn part1_grid_count_summary_run(
    counts: Seq<u32>, component_resolutions: Seq<u8>, resolutions: u8, state: Part1GridCountState,
) -> Result<Part1GridCountState,crate::DecodeError>
    decreases counts.len() - state.index as nat,
{
    if state.total as nat > usize::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else {
        let state = Part1GridCountState { offsets:state.offsets.push(state.total as usize), ..state };
        if state.index >= counts.len() { Ok(state) }
        else if state.component >= component_resolutions.len()
            || (state.resolution >= component_resolutions[state.component as int] && counts[state.index as int] != 0) {
            Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
        } else if state.total as nat + counts[state.index as int] as nat > u64::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else {
            let state = Part1GridCountState {
                total:(state.total+counts[state.index as int]) as u64,
                maximum:if counts[state.index as int]>state.maximum { counts[state.index as int] } else { state.maximum },
                ..state
            };
            if state.index == usize::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
            else {
                let state = Part1GridCountState { index:(state.index+1) as usize, ..state };
                if state.resolution == usize::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
                else {
                    let state = Part1GridCountState { resolution:(state.resolution+1) as usize, ..state };
                    if state.resolution == resolutions {
                        if state.component == usize::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
                        else { part1_grid_count_summary_run(counts,component_resolutions,resolutions,Part1GridCountState {
                            resolution:0,component:(state.component+1) as usize,..state
                        }) }
                    } else { part1_grid_count_summary_run(counts,component_resolutions,resolutions,state) }
                }
            }
        }
    }
}

pub open spec fn part1_grid_count_summary(
    counts: Seq<u32>, component_resolutions: Seq<u8>, resolutions: u8, expected: usize,
) -> Result<Part1GridCountState,crate::DecodeError> {
    if expected == usize::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else { part1_grid_count_summary_run(counts,component_resolutions,resolutions,Part1GridCountState {
        index:0,component:0,resolution:0,total:0,maximum:0,offsets:Seq::empty(),
    }) }
}

#[verifier::opaque]
pub open spec fn part1_grid_selected_row(
    counts:Seq<u32>, resolutions:u8, component:usize, resolution:u8, end:u8, total:u64,
) -> Result<u64,crate::DecodeError>
    decreases if resolution>=end {0nat} else {(end-resolution) as nat},
{
    if resolution>=end {Ok(total)}
    else if component as nat * resolutions as nat + resolution as nat > usize::MAX {
        Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
    } else {
        let index=component as int * resolutions as int + resolution as int;
        if index>=counts.len() {Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))}
        else if total as nat + counts[index] as nat > u64::MAX || resolution==u8::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else {part1_grid_selected_row(counts,resolutions,component,(resolution+1) as u8,end,(total+counts[index]) as u64)}
    }
}

#[verifier::opaque]
pub open spec fn part1_grid_selected_components(
    selected:Seq<u8>, component_resolutions:Seq<u8>, counts:Seq<u32>, resolutions:u8, component:usize,total:u64,
) -> Result<u64,crate::DecodeError>
    decreases selected.len()-component as nat,
{
    if component>=selected.len() {Ok(total)}
    else if component>=component_resolutions.len() || selected[component as int]==0
        || selected[component as int]>component_resolutions[component as int] {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
    } else {
        match part1_grid_selected_row(counts,resolutions,component,0,selected[component as int],total) {
            Err(error)=>Err(error),
            Ok(total)=>if component==usize::MAX {Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
                else {part1_grid_selected_components(selected,component_resolutions,counts,resolutions,(component+1) as usize,total)},
        }
    }
}

pub open spec fn part1_grid_selected_precincts(
    selected:Option<Seq<u8>>,component_resolutions:Seq<u8>,counts:Seq<u32>,resolutions:u8,components:u16,total:u64,
) -> Result<u64,crate::DecodeError> {
    match selected {
        None=>Ok(total),
        Some(selected)=>if selected.len()!=components as nat {Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))}
            else {part1_grid_selected_components(selected,component_resolutions,counts,resolutions,0,0)},
    }
}

pub open spec fn part1_packet_grid_new(
    layers:u16,components:u16,component_resolutions:Seq<u8>,counts:Seq<u32>,selected:Option<Seq<u8>>,
    limits:&crate::ResourceLimits,
) -> Result<Part1PacketGrid,crate::DecodeError> {
    match part1_grid_resolution_summary(component_resolutions,0,0,false) {
        Err(error)=>Err(error),
        Ok((resolutions,zero))=>{
            if layers==0 || components==0 || resolutions==0 || component_resolutions.len()!=components as nat || zero {
                Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
            } else if layers>crate::limits::resource_layer_limit(limits) {
                Err(super::part1_packet_reader_limit(crate::Resource::Layers,crate::limits::resource_layer_limit(limits) as u64,layers as u64))
            } else if components>crate::limits::resource_component_limit(limits) {
                Err(super::part1_packet_reader_limit(crate::Resource::Components,crate::limits::resource_component_limit(limits) as u64,components as u64))
            } else if resolutions>crate::limits::resource_resolution_limit(limits) {
                Err(super::part1_packet_reader_limit(crate::Resource::Resolutions,crate::limits::resource_resolution_limit(limits) as u64,resolutions as u64))
            } else if components as nat * resolutions as nat > usize::MAX {
                Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
            } else if counts.len()!=components as nat * resolutions as nat {
                Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
            } else {
                match part1_grid_count_summary(counts,component_resolutions,resolutions,(components as nat*resolutions as nat) as usize) {
                    Err(error)=>Err(error),
                    Ok(summary)=>match part1_grid_selected_precincts(selected,component_resolutions,counts,resolutions,components,summary.total) {
                        Err(error)=>Err(error),
                        Ok(selected_total)=>{
                            if selected_total>crate::limits::resource_precinct_limit(limits) {
                                Err(super::part1_packet_reader_limit(crate::Resource::Precincts,crate::limits::resource_precinct_limit(limits),selected_total))
                            } else if summary.total as nat * layers as nat>u64::MAX
                                || selected_total as nat * layers as nat>u64::MAX {
                                Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
                            } else if selected_total as nat * layers as nat>crate::limits::resource_packet_limit(limits) {
                                Err(super::part1_packet_reader_limit(crate::Resource::Packets,crate::limits::resource_packet_limit(limits),(selected_total*layers) as u64))
                            } else {
                                let first=layers as nat*components as nat;
                                let second=first*resolutions as nat;
                                let candidates=second*summary.maximum as nat;
                                if first>u64::MAX || second>u64::MAX || candidates>u64::MAX {
                                    Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
                                } else if candidates>crate::limits::resource_work_limit(limits) {
                                    Err(super::part1_packet_reader_limit(crate::Resource::WorkUnits,crate::limits::resource_work_limit(limits),candidates as u64))
                                } else {Ok(Part1PacketGrid {
                                    layers,components,resolutions,component_resolutions,precinct_counts:counts,
                                    precinct_offsets:summary.offsets,maximum_precincts_per_resolution:summary.maximum,
                                    packet_count:(summary.total*layers) as u64,candidate_count:candidates as u64,
                                    spatial:None,maximum_work_units:crate::limits::resource_work_limit(limits),
                                })}
                            }
                        },
                    },
                }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_progression_admission(
    grid: Part1PacketGrid, records: Seq<crate::codestream::ProgressionChange>,
    index: usize, work: u64, maximum: u64,
) -> Result<(), crate::DecodeError>
    decreases records.len() - index as nat,
{
    if index >= records.len() { Ok(()) }
    else {
        match part1_packet_window_count(grid, records[index as int]) {
            Err(error) => Err(error),
            Ok(amount) => if work as nat + amount as nat > u64::MAX {
                Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
            } else if work as nat + amount as nat > maximum {
                Err(super::part1_packet_reader_limit(crate::Resource::WorkUnits, maximum, (work + amount) as u64))
            } else if index == usize::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
            else { part1_progression_admission(grid, records, (index+1) as usize, (work+amount) as u64, maximum) },
        }
    }
}

pub open spec fn part1_progression_iterator_initial(
    grid: Part1PacketGrid, order: crate::codestream::ProgressionOrder,
    records: Seq<crate::codestream::ProgressionChange>, maximum_work: u64,
) -> Result<Part1ProgressionPacketIterator, crate::DecodeError> {
    match part1_progression_admission(grid, records, 0, 0, maximum_work) {
        Err(error) => Err(error),
        Ok(()) => {
            let first = if records.len() == 0 { Ok(0u64) } else { part1_packet_window_count(grid, records[0]) };
            match first {
                Err(error) => Err(error),
                Ok(count) => Ok(Part1ProgressionPacketIterator {
                    grid, changes:records, default:if records.len()==0 {
                        Some(Part1PacketIterator { grid, order, candidate_index:0, emitted:0 })
                    } else { None },
                    window_index:0, window_candidate:0, window_candidates:count, emitted:0,
                }),
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_progression_prior_contains(
    records: Seq<crate::codestream::ProgressionChange>, end: usize, index: usize,
    coordinate: crate::packet::PacketCoordinate,
) -> Result<bool, crate::DecodeError>
    decreases if index >= end { 0nat } else { (end-index) as nat },
{
    if index >= end { Ok(false) }
    else if index >= records.len() { Err(ht_reader_error(crate::MalformedKind::InvalidProgressionOrderChange)) }
    else if crate::codestream::progression_change_contains(records[index as int],
        coordinate.layer, coordinate.resolution, coordinate.component) { Ok(true) }
    else if index == usize::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else { part1_progression_prior_contains(records, end, (index+1) as usize, coordinate) }
}

pub open spec fn part1_progression_candidate_step(
    state: Part1ProgressionPacketIterator, record: crate::codestream::ProgressionChange,
) -> (Result<Option<crate::packet::PacketCoordinate>,crate::DecodeError>,Part1ProgressionPacketIterator) {
    if state.window_candidate == u64::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),state) }
    else {
        let candidate = state.window_candidate;
        let state = Part1ProgressionPacketIterator { window_candidate:(candidate+1) as u64, ..state };
        match part1_packet_window_candidate(state.grid, record, candidate) {
            Err(error) => (Err(error),state),
            Ok(coordinate) => match part1_packet_grid_precinct_count(state.grid, coordinate.component, coordinate.resolution) {
                Err(error) => (Err(error),state),
                Ok(count) => if coordinate.precinct >= count { (Ok(None),state) }
                else {
                    match part1_progression_prior_contains(state.changes, state.window_index, 0, coordinate) {
                        Err(error) => (Err(error),state),
                        Ok(true) => (Ok(None),state),
                        Ok(false) => if state.emitted == u64::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),state) }
                        else {
                            let state = Part1ProgressionPacketIterator { emitted:(state.emitted+1) as u64, ..state };
                            if state.emitted > state.grid.packet_count {
                                (Err(ht_reader_error(crate::MalformedKind::InvalidProgressionOrderChange)),state)
                            } else { (Ok(Some(coordinate)),state) }
                        },
                    }
                },
            },
        }
    }
}

pub open spec fn part1_progression_next_window(state: Part1ProgressionPacketIterator)
    -> (Result<(),crate::DecodeError>,Part1ProgressionPacketIterator) {
    if state.window_index == usize::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),state) }
    else {
        let state = Part1ProgressionPacketIterator { window_index:(state.window_index+1) as usize, window_candidate:0, ..state };
        let next = if state.window_index < state.changes.len() {
            part1_packet_window_count(state.grid, state.changes[state.window_index as int])
        } else { Ok(0u64) };
        match next {
            Err(error) => (Err(error),state),
            Ok(count) => (Ok(()),Part1ProgressionPacketIterator { window_candidates:count, ..state }),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_progression_windows_next(state: Part1ProgressionPacketIterator)
    -> (Result<Option<crate::packet::PacketCoordinate>,crate::DecodeError>,Part1ProgressionPacketIterator)
    decreases state.changes.len() - state.window_index as nat,
        if state.window_candidate >= state.window_candidates { 0nat }
        else { (state.window_candidates-state.window_candidate) as nat },
{
    if state.window_index >= state.changes.len() {
        if state.emitted != state.grid.packet_count { (Err(ht_reader_error(crate::MalformedKind::InvalidProgressionOrderChange)),state) }
        else { (Ok(None),state) }
    } else if state.window_candidate < state.window_candidates {
        let step = part1_progression_candidate_step(state,state.changes[state.window_index as int]);
        match step.0 { Ok(None) => part1_progression_windows_next(step.1), _ => step }
    } else {
        let step = part1_progression_next_window(state);
        match step.0 { Ok(()) => part1_progression_windows_next(step.1), Err(error) => (Err(error),step.1) }
    }
}

pub open spec fn part1_progression_iterator_next(state: Part1ProgressionPacketIterator)
    -> (Result<Option<crate::packet::PacketCoordinate>,crate::DecodeError>,Part1ProgressionPacketIterator) {
    match state.default {
        None => part1_progression_windows_next(state),
        Some(default) => {
            let step = part1_packet_iterator_next(default);
            let state = Part1ProgressionPacketIterator { default:Some(step.1), ..state };
            match step.0 {
                Err(error) => (Err(error),state),
                Ok(coordinate) => (Ok(coordinate),Part1ProgressionPacketIterator { emitted:step.1.emitted, ..state }),
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_grid_resolution_summary(
    values: Seq<u8>, index: usize, maximum: u8, zero: bool,
) -> Result<(u8,bool), crate::DecodeError>
    decreases values.len() - index as nat,
{
    if index >= values.len() { Ok((maximum,zero)) }
    else if index == usize::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else { part1_grid_resolution_summary(values, (index+1) as usize,
        if values[index as int] > maximum { values[index as int] } else { maximum },
        zero || values[index as int] == 0) }
}

pub open spec fn part1_packet_grid_total_precincts(grid: Part1PacketGrid) -> Result<u64, crate::DecodeError> {
    if grid.layers == 0 { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else { Ok((grid.packet_count / grid.layers as u64) as u64) }
}

pub open spec fn part1_packet_grid_precinct_count(
    grid: Part1PacketGrid, component: u16, resolution: u8,
) -> Result<u32, crate::DecodeError> {
    if component >= grid.components || resolution >= grid.resolutions
        || component as nat >= grid.component_resolutions.len() {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
    } else if resolution >= grid.component_resolutions[component as int] {
        Ok(0)
    } else if component as nat * grid.resolutions as nat + resolution as nat > usize::MAX {
        Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
    } else {
        let index = component as int * grid.resolutions as int + resolution as int;
        if index >= grid.precinct_counts.len() { Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle)) }
        else { Ok(grid.precinct_counts[index]) }
    }
}

pub open spec fn part1_packet_grid_precinct_index(
    grid: Part1PacketGrid, component: u16, resolution: u8, precinct: u32,
) -> Result<usize, crate::DecodeError> {
    match part1_packet_grid_precinct_count(grid, component, resolution) {
        Err(error) => Err(error),
        Ok(count) => if precinct >= count { Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle)) }
        else if component as nat * grid.resolutions as nat + resolution as nat > usize::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else {
            let index = component as int * grid.resolutions as int + resolution as int;
            if index >= grid.precinct_offsets.len() { Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle)) }
            else if precinct as nat > usize::MAX || grid.precinct_offsets[index] as nat + precinct as nat > usize::MAX {
                Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
            } else { Ok((grid.precinct_offsets[index] + precinct) as usize) }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_selected_row(
    grid: Part1PacketGrid, component: u16, resolution: u8, count: u8, total: u64,
) -> Result<u64, crate::DecodeError>
    decreases if resolution >= count { 0nat } else { (count - resolution) as nat },
{
    if resolution >= count { Ok(total) }
    else {
        match part1_packet_grid_precinct_count(grid, component, resolution) {
            Err(error) => Err(error),
            Ok(amount) => if total as nat + amount as nat > u64::MAX || resolution == u8::MAX {
                Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
            } else { part1_packet_selected_row(grid, component, (resolution + 1) as u8,
                count, (total + amount) as u64) },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_selected_count_run(
    grid: Part1PacketGrid, counts: Seq<u8>, component: u16, total: u64,
) -> Result<u64, crate::DecodeError>
    decreases if component >= grid.components { 0nat } else { (grid.components - component) as nat },
{
    if component >= grid.components {
        if total as nat * grid.layers as nat > u64::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else { Ok((total * grid.layers) as u64) }
    } else if component as nat >= counts.len() || counts[component as int] == 0
        || component as nat >= grid.component_resolutions.len()
        || counts[component as int] > grid.component_resolutions[component as int] {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
    } else {
        match part1_packet_selected_row(grid, component, 0, counts[component as int], total) {
            Err(error) => Err(error),
            Ok(total) => if component == u16::MAX {
                Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
            } else { part1_packet_selected_count_run(grid, counts, (component + 1) as u16, total) },
        }
    }
}

pub open spec fn part1_packet_grid_selected_count(grid: Part1PacketGrid, counts: Seq<u8>)
    -> Result<u64, crate::DecodeError> {
    if counts.len() != grid.components as nat {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
    } else { part1_packet_selected_count_run(grid, counts, 0, 0) }
}

pub open spec fn part1_packet_unravel(index: u64, dimensions: Seq<u64>) -> Result<Seq<u64>, crate::DecodeError> {
    if dimensions.len() != 4 || dimensions[0] == 0 || dimensions[1] == 0 || dimensions[2] == 0 || dimensions[3] == 0 {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
    } else {
        let third = index % dimensions[3];
        let index = index / dimensions[3];
        let second = index % dimensions[2];
        let index = index / dimensions[2];
        let first = index % dimensions[1];
        let index = index / dimensions[1];
        if index >= dimensions[0] { Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle)) }
        else { Ok(seq![index as u64, first as u64, second as u64, third as u64]) }
    }
}

pub open spec fn part1_packet_candidate_dimensions(
    grid: Part1PacketGrid, order: crate::codestream::ProgressionOrder,
) -> Seq<u64> {
    let l = grid.layers as u64;
    let r = grid.resolutions as u64;
    let c = grid.components as u64;
    let p = super::part1_packet_position_count(grid, order);
    match order {
        crate::codestream::ProgressionOrder::Lrcp => seq![l,r,c,p],
        crate::codestream::ProgressionOrder::Rlcp => seq![r,l,c,p],
        crate::codestream::ProgressionOrder::Rpcl => seq![r,p,c,l],
        crate::codestream::ProgressionOrder::Pcrl => seq![p,c,r,l],
        crate::codestream::ProgressionOrder::Cprl => seq![c,p,r,l],
    }
}

pub open spec fn part1_packet_candidate(
    grid: Part1PacketGrid, order: crate::codestream::ProgressionOrder, candidate: u64,
) -> Result<crate::packet::PacketCoordinate, crate::DecodeError> {
    match part1_packet_unravel(candidate, part1_packet_candidate_dimensions(grid, order)) {
        Err(error) => Err(error),
        Ok(v) => {
            let (l,r,c,p) = match order {
                crate::codestream::ProgressionOrder::Lrcp => (v[0],v[1],v[2],v[3]),
                crate::codestream::ProgressionOrder::Rlcp => (v[1],v[0],v[2],v[3]),
                crate::codestream::ProgressionOrder::Rpcl => (v[3],v[0],v[2],v[1]),
                crate::codestream::ProgressionOrder::Pcrl => (v[3],v[2],v[1],v[0]),
                crate::codestream::ProgressionOrder::Cprl => (v[3],v[2],v[0],v[1]),
            };
            if l > u16::MAX || r > u8::MAX || c > u16::MAX {
                Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
            } else {
                match super::part1_packet_candidate_precinct(grid,order,c,r,p) {
                    Err(error)=>Err(error),
                    Ok(precinct)=>Ok(crate::packet::PacketCoordinate {
                        layer:l as u16, resolution:r as u8, component:c as u16, precinct,
                    }),
                }
            }
        },
    }
}

pub open spec fn part1_packet_window_bounds(grid: Part1PacketGrid, record: crate::codestream::ProgressionChange)
    -> crate::codestream::ProgressionChange {
    crate::codestream::ProgressionChange {
        layer_end: if record.layer_end < grid.layers { record.layer_end } else { grid.layers },
        resolution_end: if record.resolution_end < grid.resolutions { record.resolution_end } else { grid.resolutions },
        component_end: if record.component_end < grid.components { record.component_end } else { grid.components },
        ..record
    }
}

pub open spec fn part1_packet_window_count(grid: Part1PacketGrid, record: crate::codestream::ProgressionChange)
    -> Result<u64, crate::DecodeError> {
    let record = part1_packet_window_bounds(grid, record);
    if record.resolution_end < record.resolution_start {
        Err(ht_reader_error(crate::MalformedKind::InvalidProgressionOrderChange))
    } else {
        let first = record.layer_end as nat * (record.resolution_end - record.resolution_start) as nat;
        let components = if record.component_end < record.component_start { 0nat }
            else { (record.component_end - record.component_start) as nat };
        let second = first * components;
        let third = second * super::part1_packet_position_count(grid,record.progression_order) as nat;
        if first > u64::MAX || second > u64::MAX || third > u64::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else { Ok(third as u64) }
    }
}

pub open spec fn part1_packet_window_candidate(
    grid: Part1PacketGrid, record: crate::codestream::ProgressionChange, candidate: u64,
) -> Result<crate::packet::PacketCoordinate, crate::DecodeError> {
    let record = part1_packet_window_bounds(grid, record);
    if record.resolution_end < record.resolution_start || record.component_end < record.component_start {
        Err(ht_reader_error(crate::MalformedKind::InvalidProgressionOrderChange))
    } else {
        let local_grid = Part1PacketGrid {
            layers:record.layer_end,
            resolutions:(record.resolution_end - record.resolution_start) as u8,
            components:(record.component_end - record.component_start) as u16,
            ..grid
        };
        match part1_packet_unravel(candidate,part1_packet_candidate_dimensions(local_grid,record.progression_order)) {
            Err(error) => Err(error),
            Ok(v) => {
                let (l,r,c,p) = match record.progression_order {
                    crate::codestream::ProgressionOrder::Lrcp => (v[0],v[1],v[2],v[3]),
                    crate::codestream::ProgressionOrder::Rlcp => (v[1],v[0],v[2],v[3]),
                    crate::codestream::ProgressionOrder::Rpcl => (v[3],v[0],v[2],v[1]),
                    crate::codestream::ProgressionOrder::Pcrl => (v[3],v[2],v[1],v[0]),
                    crate::codestream::ProgressionOrder::Cprl => (v[3],v[2],v[0],v[1]),
                };
                let resolution=r as nat+record.resolution_start as nat;
                let component=c as nat+record.component_start as nat;
                if resolution>u64::MAX || component>u64::MAX || l>u16::MAX || resolution>u8::MAX || component>u16::MAX {
                    Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
                }else{match super::part1_packet_candidate_precinct(grid,record.progression_order,component as u64,resolution as u64,p) {
                    Err(error)=>Err(error),
                    Ok(precinct)=>Ok(crate::packet::PacketCoordinate {
                        layer:l as u16,resolution:resolution as u8,component:component as u16,precinct,
                    }),
                }}
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_iterator_next(state: Part1PacketIterator)
    -> (Result<Option<crate::packet::PacketCoordinate>, crate::DecodeError>, Part1PacketIterator)
    decreases match super::part1_packet_candidate_count(state.grid,state.order) {
        Err(_)=>0nat,
        Ok(count)=>if state.candidate_index>=count{0nat}else{(count-state.candidate_index) as nat},
    },
{
    match super::part1_packet_candidate_count(state.grid,state.order) {
    Err(error)=>(Err(error),state),
    Ok(count)=>if state.candidate_index >= count { (Ok(None), state) }
    else {
        let candidate = state.candidate_index;
        let state = Part1PacketIterator { candidate_index:(candidate + 1) as u64, ..state };
        match part1_packet_candidate(state.grid, state.order, candidate) {
            Err(error) => (Err(error),state),
            Ok(coordinate) => match part1_packet_grid_precinct_count(state.grid, coordinate.component, coordinate.resolution) {
                Err(error) => (Err(error),state),
                Ok(count) => if coordinate.precinct >= count { part1_packet_iterator_next(state) }
                else if state.emitted == u64::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),state) }
                else {
                    let state = Part1PacketIterator { emitted:(state.emitted + 1) as u64, ..state };
                    if state.emitted > state.grid.packet_count { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),state) }
                    else { (Ok(Some(coordinate)),state) }
                },
            },
        }}
    }
}

}
