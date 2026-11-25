use super::{
    DecodedLayoutTile, ImageSize, PacketGrid, PlannedTileComponent, PreparedTileComponent,
    ProgressionCodeBlockPlacement, Resource, ResourceLimits, SubbandGeometry, TilePartPayload,
    WaveletTransform, arithmetic_overflow, codestream, invalid_decode,
};
use crate::DecodeError;
use crate::packet::{PrivateHtPrecinct, new_private_ht_precinct};
use crate::tier1::{PrivateHtDecoder, new_private_ht_decoder};
use crate::tier1::{Tier1BlockCoding, Tier1CodingStyle};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

struct PrivateHtSubband {
    geometry: SubbandGeometry,
    blocks: Vec<PrivateHtDecoder>,
    placements: Vec<ProgressionCodeBlockPlacement>,
    across: u32,
    down: u32,
}

struct PrivateHtPlan {
    component: PlannedTileComponent,
    grid: PacketGrid,
    precinct: PrivateHtPrecinct,
}

struct PrivateHtStandardPlan {
    component: PlannedTileComponent,
    grid: PacketGrid,
    precincts: Vec<PrivateHtPrecinct>,
}

struct PrivateHtStandardBlocks {
    blocks: Vec<PrivateHtDecoder>,
    placements: Vec<ProgressionCodeBlockPlacement>,
    next: usize,
    total: u64,
}

struct PrivateHtStandardPrecinctBuilder {
    executions: Vec<crate::packet::PrivateHtSubbandExecution>,
    placements: Vec<ProgressionCodeBlockPlacement>,
    next: usize,
    total: u64,
}

struct PrivateHtStandardPlannedPrecinct {
    precinct: PrivateHtPrecinct,
    placements: Vec<ProgressionCodeBlockPlacement>,
    total: u64,
}

struct PrivateHtStandardPlanBuffers {
    precincts: Vec<PrivateHtPrecinct>,
    placements: Vec<ProgressionCodeBlockPlacement>,
    total: u64,
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires state.invariant(),state.blocks.len()<usize::MAX,
        style.force_high_throughput,matches!(style.block_coding,Tier1BlockCoding::HighThroughput),
    ensures crate::specs::part2_cold_framed(|events|crate::specs::private_standard_cell_run(
        private_standard_context(lattice,geometry,style,profile,indices),state.view(),block,events),private_standard_blocks_outcome(result)),
    private_standard_blocks_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        private_standard_blocks_outcome(result)==crate::specs::private_standard_cell_value(
            private_standard_context(lattice,geometry,style,profile,indices),state.view(),block),
    match result{Ok(value)=>value.invariant() && value.blocks.len()==state.blocks.len()+1,Err(_)=>true},
))]
fn append_standard_block(
    lattice: super::PlannedSubbandLattice,
    block: [u32; 2],
    geometry: SubbandGeometry,
    style: Tier1CodingStyle,
    profile: &codestream::CodestreamProfile,
    indices: (usize, usize),
    state: PrivateHtStandardBlocks,
) -> Result<PrivateHtStandardBlocks, DecodeError> {
    let mut state = state;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost context=private_standard_context(lattice,geometry,style,profile,indices);
        let ghost before=state.view();
        let ghost root=|events|crate::specs::private_standard_cell_run(context,before,block,events);
        let ghost mut prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(private_standard_context);reveal(PrivateHtStandardBlocks::view);reveal(PrivateHtStandardBlocks::invariant);
        reveal(crate::specs::private_standard_cell_run);
    }
    let derived =
        super::planning::derive_planned_codeblock_geometry(lattice.grid, lattice.clip, block);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=derived {crate::specs::part2_cold_pure::<crate::specs::PrivateStandardBlocksState>(Err(error));}
    }
    let (x, y, width, height) = derived?;
    let initialized = new_private_ht_decoder(
        width,
        height,
        geometry.significant_bitplanes,
        geometry.orientation,
        style,
        profile.part15_allows_multiple_ht_sets(),
        profile.part15_magnitude_bound(),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let ctor=crate::specs::private_standard_cell_context(context,(x,y,width,height));
        crate::specs::private_decoder_initial_calls_observed(ctor,crate::tier1::private_decoder_outcome(initialized));
        let child=|events|crate::specs::private_decoder_initial_calls_run(ctor,events);
        let next=|decoder,rest|crate::specs::private_standard_cell_after_initial(context,before,(x,y,width,height),decoder,rest);
        if let Err(error)=initialized {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(value)=crate::tier1::private_decoder_outcome(initialized){
            prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,value);
        }
    }
    let decoder = initialized?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost decoded=decoder.storage_view();}
    let reserved = crate::allocation::reserve_additional(&mut state.blocks, 1);
    #[cfg(verus_keep_ghost)]
    proof! {
        let capacity=crate::specs::PrivateOwnerCapacityContext::BlockAppend {source:before.blocks,next:decoded};
        crate::specs::private_owner_capacity_observed(capacity,crate::allocation::inspection_capacity_outcome(reserved));
        let child=|events|crate::specs::private_owner_capacity_run(capacity,events);
        let next=|_:(),rest|crate::specs::private_standard_cell_after_append(context,before,(x,y,width,height),decoded,rest);
        if let Err(error)=reserved{crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if reserved.is_ok(){prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,());}
    }
    reserved?;
    state.blocks.push(decoder);
    let placement = match private_placement(geometry, x, y, state.next) {
        Err(error) => Err(error),
        Ok(mut value) => {
            value.precinct_index = indices.0;
            value.subband_index = indices.1;
            Ok(value)
        }
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(placement==crate::specs::private_standard_placement(context,before,(x,y,width,height)));
        crate::specs::part2_cold_pure(placement);
        let child=|events|Some((crate::specs::private_standard_placement(context,before,(x,y,width,height)),events));
        let next=|place,rest|crate::specs::private_standard_cell_after_placement(before,decoded,place,rest);
        if let Err(error)=placement{crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(place)=placement{prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,place);}
    }
    let placement = placement?;
    let reserved = crate::allocation::reserve_additional(&mut state.placements, 1);
    #[cfg(verus_keep_ghost)]
    proof! {
        let capacity=crate::specs::PrivateOwnerCapacityContext::PlacementAppend {source:before.placements,next:placement};
        crate::specs::private_owner_capacity_observed(capacity,crate::allocation::inspection_capacity_outcome(reserved));
        let child=|events|crate::specs::private_owner_capacity_run(capacity,events);
        let next=|_:(),rest|Some((crate::specs::private_standard_cell_finish(before,decoded,placement),rest));
        if let Err(error)=reserved{crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if reserved.is_ok(){prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,());}
    }
    reserved?;
    state.placements.push(placement);
    let next = state.next.checked_add(1).ok_or_else(arithmetic_overflow);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=next{assert(crate::specs::part2_cold_prefix(root,prefix,Err(error)));}
    }
    state.next = next?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(state.blocks@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view()) =~= before.blocks.push(decoded));
        assert(state.placements@ =~= before.placements.push(placement));
        assert(state.view()==crate::specs::private_standard_cell_finish(before,decoded,placement).get_Ok_0());
        assert(crate::specs::part2_cold_prefix(root,prefix,Ok(state.view())));
    }
    Ok(state)
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires style.force_high_throughput,matches!(style.block_coding,Tier1BlockCoding::HighThroughput),
    ensures crate::specs::part2_cold_framed(|events|crate::specs::private_standard_blocks_run(
        private_standard_context(lattice,geometry,style,profile,(indices.0,indices.1)),
        placements@,indices.2,starting_total,limits,events),private_standard_blocks_outcome(result)),
    private_standard_blocks_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        private_standard_blocks_outcome(result)==crate::specs::private_standard_blocks_value(
            private_standard_context(lattice,geometry,style,profile,(indices.0,indices.1)),
            placements@,indices.2,starting_total,limits),
    match result{Ok(value)=>value.invariant(),Err(_)=>true},
))]
fn plan_standard_blocks(
    lattice: super::PlannedSubbandLattice,
    geometry: SubbandGeometry,
    style: Tier1CodingStyle,
    profile: &codestream::CodestreamProfile,
    indices: (usize, usize, usize),
    placements: Vec<ProgressionCodeBlockPlacement>,
    starting_total: u64,
    limits: &ResourceLimits,
) -> Result<PrivateHtStandardBlocks, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost context=private_standard_context(lattice,geometry,style,profile,(indices.0,indices.1));
        let ghost original_placements=placements@;
        let ghost original_total=starting_total;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(private_standard_context);reveal(super::planned_subband_lattice_view);
        reveal(PrivateHtStandardBlocks::view);reveal(PrivateHtStandardBlocks::invariant);
    }
    let counted = u64::from(lattice.blocks[0])
        .checked_mul(u64::from(lattice.blocks[1]))
        .ok_or_else(arithmetic_overflow);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=counted {crate::specs::part2_cold_pure::<crate::specs::PrivateStandardBlocksState>(Err(error));}
    }
    let count = counted?;
    let added = starting_total
        .checked_add(count)
        .ok_or_else(arithmetic_overflow);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=added {crate::specs::part2_cold_pure::<crate::specs::PrivateStandardBlocksState>(Err(error));}
    }
    let total = added?;
    if total > limits.maximum_code_blocks() {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateStandardBlocksState>(
        Err(DecodeError::LimitExceeded {resource:Resource::CodeBlocks,limit:crate::limits::resource_code_block_limit(limits),actual:total}));}
        return Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlocks,
            limit: limits.maximum_code_blocks(),
            actual: total,
        });
    }
    if total > limits.maximum_work_units() {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateStandardBlocksState>(
        Err(DecodeError::LimitExceeded {resource:Resource::WorkUnits,limit:crate::limits::resource_work_limit(limits),actual:total}));}
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: total,
        });
    }
    if count > usize::MAX as u64 {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateStandardBlocksState>(Err(crate::specs::part1_block_placement_error(true)));}
        return Err(arithmetic_overflow());
    }
    let capacity = count as usize;
    let reserved = if capacity == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(capacity)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::private_standard_blocks_admit(context,original_total,limits)==Ok((capacity,total)));
        let response=match reserved {Err(error)=>Err(error),Ok(_)=>Ok(())};
        if capacity==0{crate::specs::part2_cold_pure::<()>(Ok(()));}
        else{crate::specs::private_owner_capacity_observed(crate::specs::private_standard_blocks_capacity(context,capacity),response);}
        crate::specs::private_standard_blocks_capacity_observed(context,capacity,response);
        if let Err(error)=reserved{
            crate::specs::part2_cold_bind(|events|crate::specs::private_standard_blocks_capacity_run(context,capacity,events),
                |_:(),rest|crate::specs::private_standard_rows_run(context,crate::specs::private_standard_blocks_initial(
                    original_placements,indices.2,total),0,rest),Err(error),Err(error));
        }
    }
    let mut state = PrivateHtStandardBlocks {
        blocks: reserved?,
        placements,
        next: indices.2,
        total,
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial=state.view();
        let ghost mut row_prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(state.blocks@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view()) =~= Seq::empty());
        assert(initial==crate::specs::private_standard_blocks_initial(original_placements,indices.2,total));
    }
    let mut row = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row<=lattice.blocks[1],state.invariant(),state.total==total,
            original_placements==placements@,original_total==starting_total,
            context==private_standard_context(lattice,geometry,style,profile,(indices.0,indices.1)),
            initial==crate::specs::private_standard_blocks_initial(original_placements,indices.2,total),
            capacity as nat==lattice.blocks[0] as nat*lattice.blocks[1] as nat,
            state.blocks.len() as nat==row as nat*lattice.blocks[0] as nat,
            style.force_high_throughput,matches!(style.block_coding,Tier1BlockCoding::HighThroughput),
            crate::specs::private_standard_blocks_admit(context,original_total,limits)==Ok((capacity,total)),
            crate::specs::part2_cold_framed(|events|crate::specs::private_standard_blocks_capacity_run(context,capacity,events),Ok(())),
            crate::specs::private_standard_rows_prefix(context,initial,row as nat,state.view(),row_prefix),
            crate::specs::private_standard_blocks_value(context,original_placements,indices.2,original_total,limits)==
                crate::specs::private_standard_rows_value(context,state.view(),row as nat),
        decreases lattice.blocks[1]-row,
    ))]
    while row < lattice.blocks[1] {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost row_before=state.view();
            let ghost mut column_prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {reveal_with_fuel(crate::specs::private_standard_rows_value,1);}
        let mut column = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant column<=lattice.blocks[0],row<lattice.blocks[1],state.invariant(),state.total==total,
                original_placements==placements@,original_total==starting_total,
                context==private_standard_context(lattice,geometry,style,profile,(indices.0,indices.1)),
                initial==crate::specs::private_standard_blocks_initial(original_placements,indices.2,total),
                capacity as nat==lattice.blocks[0] as nat*lattice.blocks[1] as nat,
                state.blocks.len() as nat==row as nat*lattice.blocks[0] as nat+column as nat,
                style.force_high_throughput,matches!(style.block_coding,Tier1BlockCoding::HighThroughput),
                crate::specs::private_standard_blocks_admit(context,original_total,limits)==Ok((capacity,total)),
                crate::specs::part2_cold_framed(|events|crate::specs::private_standard_blocks_capacity_run(context,capacity,events),Ok(())),
                crate::specs::private_standard_rows_prefix(context,initial,row as nat,row_before,row_prefix),
                crate::specs::private_standard_columns_prefix(context,row_before,row,column as nat,state.view(),column_prefix),
                crate::specs::private_standard_blocks_value(context,original_placements,indices.2,original_total,limits)==
                    match crate::specs::private_standard_columns_value(context,state.view(),row,column as nat){
                        Err(error)=>Err(error),Ok(after)=>crate::specs::private_standard_rows_value(context,after,row as nat+1),
                    },
            decreases lattice.blocks[0]-column,
        ))]
        while column < lattice.blocks[0] {
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before=state.view();}
            #[cfg(verus_keep_ghost)]
            proof! {
                assert((row as nat)*(lattice.blocks[0] as nat)+(column as nat)<capacity) by(nonlinear_arith)
                    requires row<lattice.blocks[1],column<lattice.blocks[0],
                        capacity as nat==lattice.blocks[0] as nat*lattice.blocks[1] as nat;
                reveal_with_fuel(crate::specs::private_standard_columns_value,1);
            }
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint()?;
            let appended = append_standard_block(
                lattice,
                [column, row],
                geometry,
                style,
                profile,
                (indices.0, indices.1),
                state,
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error)=appended{
                    crate::specs::private_standard_column_error(context,row_before,row,column as nat,before,column_prefix,error);
                    crate::specs::private_standard_row_error(context,initial,row as nat,row_before,row_prefix,error);
                    crate::specs::private_standard_blocks_rows_observed(context,original_placements,indices.2,original_total,
                        limits,capacity,total,Err(error));
                }
                if let Ok(after)=private_standard_blocks_outcome(appended){
                    column_prefix=crate::specs::private_standard_column_advance(context,row_before,row,column as nat,before,column_prefix,after);
                }
            }
            state = appended?;
            column += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::private_standard_columns_finish(context,row_before,row,state.view(),column_prefix);
            row_prefix=crate::specs::private_standard_row_advance(context,initial,row as nat,row_before,row_prefix,state.view());
            reveal_with_fuel(crate::specs::private_standard_columns_value,1);
            assert(row as nat*lattice.blocks[0] as nat+lattice.blocks[0] as nat==
                (row as nat+1)*lattice.blocks[0] as nat) by(nonlinear_arith);
        }
        row += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::private_standard_rows_finish(context,initial,state.view(),row_prefix);
        crate::specs::private_standard_blocks_rows_observed(context,original_placements,indices.2,original_total,
            limits,capacity,total,Ok(state.view()));
        reveal_with_fuel(crate::specs::private_standard_rows_value,1);
    }
    Ok(state)
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires style.force_high_throughput,matches!(style.block_coding,Tier1BlockCoding::HighThroughput),
    ensures crate::specs::part2_cold_framed(|events|crate::specs::private_standard_precinct_run(
        private_standard_precinct_context(band,block_size,subbands@,range,style,profile,location,limits),
        placements@,starting_total,events),private_standard_precinct_outcome(result)),
    private_standard_precinct_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        private_standard_precinct_outcome(result)==crate::specs::private_standard_precinct_value(
            private_standard_precinct_context(band,block_size,subbands@,range,style,profile,location,limits),placements@,starting_total),
    match result{Ok(value)=>value.precinct.invariant(),Err(_)=>true},
))]
fn plan_standard_precinct(
    band: [u32; 4],
    block_size: [u32; 2],
    subbands: &[SubbandGeometry],
    range: (usize, usize),
    style: Tier1CodingStyle,
    profile: &codestream::CodestreamProfile,
    location: (u8, u32, usize),
    placements: Vec<ProgressionCodeBlockPlacement>,
    starting_total: u64,
    limits: &ResourceLimits,
) -> Result<PrivateHtStandardPlannedPrecinct, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost context=private_standard_precinct_context(band,block_size,subbands@,range,style,profile,location,limits);
        let ghost original_placements=placements@;
        let ghost original_total=starting_total;
        let ghost root=|events|crate::specs::private_standard_precinct_run(context,original_placements,original_total,events);
        let ghost mut prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(private_standard_precinct_context);reveal(PrivateHtStandardPrecinctBuilder::view);
        reveal(PrivateHtStandardPrecinctBuilder::invariant);
    }
    let reserved = if range.1 == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(range.1)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let response=match reserved {Err(error)=>Err(error),Ok(_)=>Ok(())};
        if range.1==0{crate::specs::part2_cold_pure::<()>(Ok(()));}
        else{crate::specs::private_owner_capacity_observed(crate::specs::PrivateOwnerCapacityContext::StandardExecutions {
            context,placements:original_placements,total:original_total,
        },response);}
        crate::specs::private_standard_executions_observed(context,original_placements,original_total,response);
        let child=|events|crate::specs::private_standard_executions_run(context,original_placements,original_total,events);
        let next=|_:(),rest|crate::specs::private_standard_bands_run(context,0,
            crate::specs::PrivateStandardPrecinctBuffers {executions:Seq::empty(),placements:original_placements,next:0,total:original_total},rest);
        if let Err(error)=reserved {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if reserved.is_ok(){prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,());}
    }
    let mut builder = PrivateHtStandardPrecinctBuilder {
        executions: reserved?,
        placements,
        next: 0,
        total: starting_total,
    };
    let mut local = 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::packet::private_executions_view(builder.executions@) =~= Seq::empty());
        assert(builder.view()==(crate::specs::PrivateStandardPrecinctBuffers {
            executions:Seq::empty(),placements:original_placements,next:0,total:original_total,
        }));
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant local<=range.1,builder.invariant(),builder.executions.len()<=local,
            original_placements==placements@,original_total==starting_total,
            context==private_standard_precinct_context(band,block_size,subbands@,range,style,profile,location,limits),
            forall|events| #[trigger] root(events)==crate::specs::private_standard_precinct_run(context,original_placements,original_total,events),
            style.force_high_throughput,matches!(style.block_coding,Tier1BlockCoding::HighThroughput),
            forall|events| #[trigger] root(prefix+events)==crate::specs::private_standard_bands_run(context,local as nat,builder.view(),events),
            crate::specs::private_standard_precinct_value(context,original_placements,original_total)==
                crate::specs::private_standard_bands_value(context,local as nat,builder.view()),
        decreases range.1-local,
    ))]
    while local < range.1 {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=builder.view();}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::private_standard_bands_run,1);
            reveal_with_fuel(crate::specs::private_standard_bands_value,1);
        }
        let indexed = range.0.checked_add(local).ok_or_else(arithmetic_overflow);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error)=indexed {
                crate::specs::part2_cold_pure::<crate::specs::PrivateStandardPrecinctBuffers>(Err(error));
                crate::specs::part2_decode_prefix_error(root,|events|crate::specs::private_standard_band_run(context,local as nat,before,events),
                    |after,rest|crate::specs::private_standard_bands_run(context,local as nat+1,after,rest),prefix,error);
                crate::specs::part2_cold_framed_extensional(root,|events|crate::specs::private_standard_precinct_run(
                    context,original_placements,original_total,events),Err(error));
            }
        }
        let index = indexed?;
        let selected = subbands.get(index).ok_or_else(invalid_decode);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error)=selected {
                crate::specs::part2_cold_pure::<crate::specs::PrivateStandardPrecinctBuffers>(Err(error));
                crate::specs::part2_decode_prefix_error(root,|events|crate::specs::private_standard_band_run(context,local as nat,before,events),
                    |after,rest|crate::specs::private_standard_bands_run(context,local as nat+1,after,rest),prefix,error);
                crate::specs::part2_cold_framed_extensional(root,|events|crate::specs::private_standard_precinct_run(
                    context,original_placements,original_total,events),Err(error));
            }
        }
        let geometry = *selected?;
        let derived = super::planning::derive_planned_subband_lattice(band, block_size, geometry);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error)=derived {
                crate::specs::part2_cold_pure::<crate::specs::PrivateStandardPrecinctBuffers>(Err(error));
                crate::specs::part2_decode_prefix_error(root,|events|crate::specs::private_standard_band_run(context,local as nat,before,events),
                    |after,rest|crate::specs::private_standard_bands_run(context,local as nat+1,after,rest),prefix,error);
                crate::specs::part2_cold_framed_extensional(root,|events|crate::specs::private_standard_precinct_run(
                    context,original_placements,original_total,events),Err(error));
            }
        }
        if let Some(lattice) = derived? {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost lattice_view=super::planned_subband_lattice_view(lattice);
                let ghost child_context=crate::specs::private_standard_band_context(context,index,geometry,lattice_view);
            }
            let planned = plan_standard_blocks(
                lattice,
                geometry,
                style,
                profile,
                (location.2, index, builder.next),
                builder.placements,
                builder.total,
                limits,
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error)=planned {
                    crate::specs::part2_cold_bind(|events|crate::specs::private_standard_blocks_run(child_context,
                        before.placements,before.next,before.total,limits,events),
                        |blocks,rest|Some((Ok(crate::specs::private_standard_after_band(before,geometry,lattice_view,blocks)),rest)),
                        Err(error),Err(error));
                    crate::specs::part2_decode_prefix_error(root,|events|crate::specs::private_standard_band_run(context,local as nat,before,events),
                        |after,rest|crate::specs::private_standard_bands_run(context,local as nat+1,after,rest),prefix,error);
                    crate::specs::part2_cold_framed_extensional(root,|events|crate::specs::private_standard_precinct_run(
                        context,original_placements,original_total,events),Err(error));
                }
            }
            let blocks = planned?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost child=blocks.view();}
            #[cfg(verus_keep_ghost)]
            proof! {blocks.known_fields();}
            builder.placements = blocks.placements;
            builder.next = blocks.next;
            builder.total = blocks.total;
            let execution = crate::packet::PrivateHtSubbandExecution {
                orientation: geometry.orientation,
                across: lattice.blocks[0],
                down: lattice.blocks[1],
                maximum_zero: geometry.significant_bitplanes,
                decoders: blocks.blocks,
            };
            #[cfg(verus_keep_ghost)]
            proof! {execution.known_fields();assert(execution.invariant());}
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost published=execution.view();}
            builder.executions.push(execution);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::packet::private_executions_view(builder.executions@) =~= before.executions.push(published));
                assert(published==(crate::specs::PrivateHtExecutionState {
                    orientation:geometry.orientation,across:lattice_view.blocks[0],down:lattice_view.blocks[1],
                    maximum_zero:geometry.significant_bitplanes,decoders:child.blocks,
                }));
                assert(builder.view()==crate::specs::private_standard_after_band(before,geometry,lattice_view,child));
                crate::specs::part2_cold_pure::<crate::specs::PrivateStandardPrecinctBuffers>(Ok(builder.view()));
                crate::specs::part2_cold_bind(|events|crate::specs::private_standard_blocks_run(child_context,
                    before.placements,before.next,before.total,limits,events),
                    |blocks,rest|Some((Ok(crate::specs::private_standard_after_band(before,geometry,lattice_view,blocks)),rest)),
                    Ok(child),Ok(builder.view()));
            }
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateStandardPrecinctBuffers>(Ok(builder.view()));}
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            prefix=crate::specs::part2_decode_prefix_advance(root,
                |events|crate::specs::private_standard_band_run(context,local as nat,before,events),
                |after,rest|crate::specs::private_standard_bands_run(context,local as nat+1,after,rest),prefix,builder.view());
        }
        local += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::private_standard_bands_run,1);
        reveal_with_fuel(crate::specs::private_standard_bands_value,1);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before=builder.view();}
    let initialized = crate::packet::new_private_ht_resolution_precinct(
        location.0,
        location.1,
        style,
        builder.executions,
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let child=|events|crate::specs::private_resolution_initial_run(crate::specs::private_standard_precinct_initial_context(context,before),events);
        let next=|precinct,rest|Some((Ok(crate::specs::PrivateStandardPlannedPrecinct {precinct,placements:before.placements,total:before.total}),rest));
        if let Err(error)=initialized {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(value)=crate::packet::private_precinct_outcome(initialized){
            prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,value);
        }
    }
    let precinct = initialized?;
    let result = PrivateHtStandardPlannedPrecinct {
        precinct,
        placements: builder.placements,
        total: builder.total,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(PrivateHtStandardPlannedPrecinct::view);
        assert(crate::specs::part2_cold_prefix(root,prefix,Ok(result.view())));
    }
    Ok(result)
}

enum PrivateHtReadablePrecincts<'a> {
    One(&'a PrivateHtPrecinct),
    Resolutions(&'a [PrivateHtPrecinct]),
}

struct PrivateHtReadable<'a> {
    component: &'a PlannedTileComponent,
    precincts: PrivateHtReadablePrecincts<'a>,
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn private_standard_precinct_context(
        band:[u32;4],block:[u32;2],subbands:Seq<SubbandGeometry>,range:(usize,usize),style:Tier1CodingStyle,
        profile:&codestream::CodestreamProfile,location:(u8,u32,usize),limits:&ResourceLimits,
    )->crate::specs::PrivateStandardPrecinctContext {
        crate::specs::PrivateStandardPrecinctContext {
            band,block,subbands,range,style,
            allowed:crate::specs::part2_profile_multiple_sets(codestream::codestream_profile_capabilities(profile)),
            bound:crate::specs::part2_profile_magnitude_bound(codestream::codestream_profile_capabilities(profile)),
            location,limits:*limits,
        }
    }
    closed spec fn private_standard_plan_context(size:&ImageSize,tile:u16,first:&TilePartPayload<'_>,
        profile:&codestream::CodestreamProfile,limits:&ResourceLimits)->crate::specs::PrivateStandardPlanContext {
        crate::specs::PrivateStandardPlanContext {
            size:*size,tile,first:codestream::tile_part_owned_view(first),
            caps:codestream::codestream_profile_capabilities(profile),limits:*limits,
        }
    }
    impl PrivateHtStandardPrecinctBuilder {
        closed spec fn view(&self)->crate::specs::PrivateStandardPrecinctBuffers {
            crate::specs::PrivateStandardPrecinctBuffers {
                executions:crate::packet::private_executions_view(self.executions@),
                placements:self.placements@,next:self.next,total:self.total,
            }
        }
        closed spec fn invariant(&self)->bool {
            forall|i:int|0<=i<self.executions.len() ==> #[trigger] self.executions@[i].invariant()
        }
    }
    impl PrivateHtStandardPlannedPrecinct {
        closed spec fn view(&self)->crate::specs::PrivateStandardPlannedPrecinct {
            crate::specs::PrivateStandardPlannedPrecinct {
                precinct:self.precinct.storage_view(),placements:self.placements@,total:self.total,
            }
        }
    }
    spec fn private_standard_precinct_outcome(result:Result<PrivateHtStandardPlannedPrecinct,DecodeError>)
        ->Result<crate::specs::PrivateStandardPlannedPrecinct,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok(value.view())}
    }
    impl PrivateHtStandardPlanBuffers {
        closed spec fn view(&self)->crate::specs::PrivateStandardComponentBuffers {
            crate::specs::PrivateStandardComponentBuffers {
                precincts:crate::packet::private_precincts_view(self.precincts@),
                placements:self.placements@,total:self.total,
            }
        }
        closed spec fn invariant(&self)->bool {
            forall|i:int|0<=i<self.precincts.len() ==> #[trigger] self.precincts@[i].invariant()
        }
    }
    impl PrivateHtStandardPlan {
        closed spec fn view(&self)->crate::specs::PrivateStandardPlanState {
            crate::specs::PrivateStandardPlanState {
                component:super::prepare_plan_view(&self.component),grid:crate::packet::packet_grid_view(&self.grid),
                precincts:crate::packet::private_precincts_view(self.precincts@),
            }
        }
        closed spec fn invariant(&self)->bool {
            forall|i:int|0<=i<self.precincts.len() ==> #[trigger] self.precincts@[i].invariant()
        }
    }
    spec fn private_standard_plan_outcome(result:Result<PrivateHtStandardPlan,DecodeError>)
        ->Result<crate::specs::PrivateStandardPlanState,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok(value.view())}
    }
    closed spec fn private_standard_context(
        lattice:super::PlannedSubbandLattice,geometry:SubbandGeometry,style:Tier1CodingStyle,
        profile:&codestream::CodestreamProfile,indices:(usize,usize),
    )->crate::specs::PrivateStandardBlockContext {
        crate::specs::PrivateStandardBlockContext {
            lattice:super::planned_subband_lattice_view(lattice),geometry,style,
            allowed:crate::specs::part2_profile_multiple_sets(codestream::codestream_profile_capabilities(profile)),
            bound:crate::specs::part2_profile_magnitude_bound(codestream::codestream_profile_capabilities(profile)),indices,
        }
    }
    impl PrivateHtStandardBlocks {
        closed spec fn view(&self)->crate::specs::PrivateStandardBlocksState {
            crate::specs::PrivateStandardBlocksState {
                blocks:self.blocks@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view()),
                placements:self.placements@,next:self.next,total:self.total,
            }
        }
        closed spec fn invariant(&self)->bool {
            forall|i:int|0<=i<self.blocks.len() ==> #[trigger] self.blocks@[i].invariant()
        }
        proof fn known_fields(&self)
            ensures self.invariant()==crate::specs::private_standard_blocks_wf(self.view()),
                self.view()==(crate::specs::PrivateStandardBlocksState {
                    blocks:self.blocks@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view()),
                    placements:self.placements@,next:self.next,total:self.total,
                }),
        {
            reveal(PrivateHtStandardBlocks::view);reveal(PrivateHtStandardBlocks::invariant);
            assert forall|i:int|0<=i<self.blocks.len() implies
                self.blocks@[i].invariant()==crate::specs::private_ht_state_wf(self.view().blocks[i]) by {
                self.blocks@[i].known_fields();
            }
        }
    }
    spec fn private_standard_blocks_outcome(result:Result<PrivateHtStandardBlocks,DecodeError>)
        ->Result<crate::specs::PrivateStandardBlocksState,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok(value.view())}
    }
    impl PrivateHtReadable<'_> {
        closed spec fn precincts_view(&self)->Seq<crate::specs::PrivateHtPrecinctState> {
            match self.precincts {
                PrivateHtReadablePrecincts::One(value)=>seq![value.storage_view()],
                PrivateHtReadablePrecincts::Resolutions(values)=>values@.map_values(
                    |value:PrivateHtPrecinct|value.storage_view()),
            }
        }
    }
}

impl PrivateHtReadable<'_> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures match result {
            Ok(value)=>precinct<self.precincts_view().len()
                && decoder<self.precincts_view()[precinct as int].logical.decoders.len()
                && value.view()==self.precincts_view()[precinct as int].logical.decoders[decoder as int],
            Err(error)=>(precinct>=self.precincts_view().len()
                || decoder>=self.precincts_view()[precinct as int].logical.decoders.len())
                && error==if precinct>=self.precincts_view().len(){
                    crate::specs::part1_block_placement_error(false)
                }else{crate::specs::part1_packet_header_error()},
        },
    ))]
    fn decoder(&self, precinct: usize, decoder: usize) -> Result<&PrivateHtDecoder, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(PrivateHtReadable::precincts_view);}
        match self.precincts {
            PrivateHtReadablePrecincts::One(value) => {
                if precinct != 0 {
                    return Err(invalid_decode());
                }
                #[cfg(verus_keep_ghost)]
                proof! {value.known_fields();}
                value.decoder(decoder)
            }
            PrivateHtReadablePrecincts::Resolutions(values) => {
                let value = values.get(precinct).ok_or_else(invalid_decode)?;
                #[cfg(verus_keep_ghost)]
                proof! {value.known_fields();}
                value.decoder(decoder)
            }
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result==crate::specs::private_ht_standard_eligible(size,tile,
        codestream::tile_parts_owned_view(parts@),codestream::codestream_profile_capabilities(profile),discard),
))]
pub(super) fn standard_eligible(
    size: &ImageSize,
    tile: u16,
    parts: &[TilePartPayload<'_>],
    profile: &codestream::CodestreamProfile,
    discard: Option<u8>,
) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::selection_geometry_known_fields(size);
        reveal(codestream::tile_part_owned_view);
    }
    if !super::PRIVATE_HT_PRIMARY_ENABLED
        || size.components != 1
        || parts.len() != 1
        || discard.unwrap_or(0) != 0
        || !profile.part15_requires_all_ht_blocks()
    {
        return false;
    }
    let Some(first) = parts.first() else {
        return false;
    };
    let Ok(style) = first.component_coding_styles.style(0) else {
        return false;
    };
    let Ok(tier1) = style.tier1_coding_style() else {
        return false;
    };
    let Ok(roi) = first.roi_shifts.shift(0) else {
        return false;
    };
    let Ok(bounds) = size.tile_component_bounds(first.tile_index, 0) else {
        return false;
    };
    let Ok(geometry) = super::geometry::derive_component_resolution_geometry_for(
        size,
        style,
        0,
        style.decomposition_levels,
        Some(tile),
    ) else {
        return false;
    };
    matches!(tier1.block_coding, Tier1BlockCoding::HighThroughput)
        && first.tile_index == tile
        && style.decomposition_levels > 0
        && style.decomposition_structure.is_none()
        && !style.precincts_defined
        && !matches!(style.transform, WaveletTransform::Arbitrary(_))
        && codestream::effective_coding_styles_equal(style, first.coding_style)
        && !first.has_functional_header_marker
        && !first.coding_style.multiple_component_transform
        && first.multiple_component_transform.is_none()
        && first.progression_changes.is_empty()
        && !first.packed_packet_headers.is_present()
        && !first.packet_lengths.is_present()
        && roi == 0
        && !first.has_roi_marker
        && bounds.x0 == 0
        && bounds.y0 == 0
        && bounds.x1 > 0
        && bounds.y1 > 0
        && bounds.x1 <= 32768
        && bounds.y1 <= 32768
        && geometry.precincts == 1
        && geometry.precincts_across == 1
        && geometry.precincts_down == 1
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::private_ht_standard_eligible(size,tile,seq![codestream::tile_part_owned_view(first)],
        codestream::codestream_profile_capabilities(profile),None),
    ensures crate::specs::private_standard_plan_result(private_standard_plan_context(size,tile,first,profile,limits),
        private_standard_plan_outcome(result)),
    private_standard_plan_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        private_standard_plan_outcome(result)==crate::specs::private_standard_plan_value(
            private_standard_plan_context(size,tile,first,profile,limits)),
    match result{Ok(value)=>value.invariant() && value.component.component==0,Err(_)=>true},
))]
fn plan_standard(
    size: &ImageSize,
    tile: u16,
    first: &TilePartPayload<'_>,
    profile: &codestream::CodestreamProfile,
    limits: &ResourceLimits,
) -> Result<PrivateHtStandardPlan, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost context=private_standard_plan_context(size,tile,first,profile,limits);
        let ghost root=|events|crate::specs::private_standard_plan_run(context,events);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(private_standard_plan_context);reveal(codestream::tile_part_owned_view);
        codestream::selection_geometry_known_fields(size);
    }
    let bounds = size.tile_bounds(tile);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=bounds {crate::specs::part2_cold_pure::<crate::specs::PrivateStandardPlanState>(Err(error));}}
    bounds?;
    let derived_grid = super::geometry::derive_packet_grid_for_components(
        size,
        &first.component_coding_styles,
        first.coding_style.layers,
        limits,
        Some(tile),
        0,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_spatial_derived_grid_result);
        if let Err(error)=derived_grid{
            crate::specs::part2_cold_bind(|events|crate::specs::part2_spatial_derived_grid_run(size,
                &context.first.component_coding_styles,context.first.coding_style.layers,limits,Some(tile),0,events),
                |grid,rest|crate::specs::private_standard_plan_after_grid(context,grid,rest),Err(error),Err(error));
        }
    }
    let grid = derived_grid?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost grid_value=crate::packet::packet_grid_view(&grid);}
    let derived_metadata = super::planning::prepare_component_plan_metadata(
        size,
        &first.component_coding_styles,
        &first.component_quantizations,
        &first.roi_shifts,
        0,
        (tile, 0),
        profile.part15_requires_all_ht_blocks(),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_component_metadata_result);
        if let Err(error)=derived_metadata{
            crate::specs::part2_cold_bind(|events|crate::specs::part2_component_metadata_run(size,&context.first.component_coding_styles,
                context.first.component_quantizations,&context.first.roi_shifts,0,(tile,0),
                crate::specs::part2_profile_force_ht(context.caps),events),
                |metadata,rest|crate::specs::private_standard_plan_after_metadata(context,grid_value,metadata,rest),Err(error),Err(error));
            crate::specs::part2_decode_eta(|events|crate::specs::private_standard_plan_after_grid(context,grid_value,events),Err(error));
            crate::specs::part2_cold_bind(|events|crate::specs::part2_spatial_derived_grid_run(size,&context.first.component_coding_styles,
                context.first.coding_style.layers,limits,Some(tile),0,events),
                |grid,rest|crate::specs::private_standard_plan_after_grid(context,grid,rest),Ok(grid_value),Err(error));
        }
    }
    let metadata = derived_metadata?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost meta=super::component_plan_metadata_view(&metadata);}
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::private_standard_metadata_fields(context,meta);
        assert(crate::specs::private_standard_plan_prepared(context,grid_value,meta));
        reveal(PrivateHtStandardPlanBuffers::view);reveal(PrivateHtStandardPlanBuffers::invariant);
    }
    let mut builder = PrivateHtStandardPlanBuffers {
        precincts: Vec::new(),
        placements: Vec::new(),
        total: 0,
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial=builder.view();
        let ghost mut resolution_prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::packet::private_precincts_view(builder.precincts@) =~= Seq::empty());
        assert(initial==(crate::specs::PrivateStandardComponentBuffers {precincts:Seq::empty(),placements:Seq::empty(),total:0}));
    }
    let mut resolution = 0_u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant resolution<=metadata.component_coding_style.decomposition_levels as int+1,builder.invariant(),
            metadata.tier1_style.force_high_throughput,matches!(metadata.tier1_style.block_coding,Tier1BlockCoding::HighThroughput),
            context==private_standard_plan_context(size,tile,first,profile,limits),
            meta==super::component_plan_metadata_view(&metadata),grid_value==crate::packet::packet_grid_view(&grid),
            initial==(crate::specs::PrivateStandardComponentBuffers {precincts:Seq::empty(),placements:Seq::empty(),total:0}),
            crate::specs::private_standard_plan_prepared(context,grid_value,meta),
            crate::specs::private_standard_resolutions_prefix(context,meta,initial,resolution as nat,builder.view(),resolution_prefix),
            crate::specs::private_standard_plan_value(context)==match crate::specs::private_standard_resolutions_value(
                context,meta,resolution as nat,builder.view()){
                Err(error)=>Err(error),Ok(after)=>Ok(crate::specs::private_standard_plan_finish(meta,grid_value,after)),
            },
        decreases metadata.component_coding_style.decomposition_levels as int+1-resolution as int,
    ))]
    while resolution <= metadata.component_coding_style.decomposition_levels {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost resolution_before=builder.view();}
        #[cfg(verus_keep_ghost)]
        proof! {reveal_with_fuel(crate::specs::private_standard_resolutions_value,1);}
        let derived_data = super::planning::prepare_resolution_plan_metadata(
            size,
            metadata.component_coding_style,
            0,
            (tile, resolution),
            [metadata.bounds.x0, metadata.bounds.y0],
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error)=derived_data{
                crate::specs::part2_cold_pure::<crate::specs::PrivateStandardComponentBuffers>(Err(error));
                crate::specs::private_standard_resolutions_error(context,meta,initial,resolution as nat,resolution_before,resolution_prefix,error);
                crate::specs::private_standard_plan_resolutions_observed(context,grid_value,meta,Err(error));
            }
        }
        let data = derived_data?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost data_value=super::resolution_plan_metadata_view(&data);
            let ghost mut precinct_prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
        }
        let mut precinct = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant precinct<=data.precincts_in_resolution,builder.invariant(),
                metadata.tier1_style.force_high_throughput,matches!(metadata.tier1_style.block_coding,Tier1BlockCoding::HighThroughput),
                resolution<=metadata.component_coding_style.decomposition_levels,
                context==private_standard_plan_context(size,tile,first,profile,limits),
                meta==super::component_plan_metadata_view(&metadata),grid_value==crate::packet::packet_grid_view(&grid),
                data_value==super::resolution_plan_metadata_view(&data),
                initial==(crate::specs::PrivateStandardComponentBuffers {precincts:Seq::empty(),placements:Seq::empty(),total:0}),
                crate::specs::private_standard_plan_prepared(context,grid_value,meta),
                crate::specs::private_standard_resolutions_prefix(context,meta,initial,resolution as nat,resolution_before,resolution_prefix),
                crate::specs::part2_resolution_plan_metadata(size,meta.coding_style,0,(tile,resolution),[meta.bounds.x0,meta.bounds.y0])==Ok(data_value),
                crate::specs::private_standard_precincts_prefix(context,meta,data_value,resolution,resolution_before,precinct as nat,builder.view(),precinct_prefix),
                crate::specs::private_standard_plan_value(context)==match crate::specs::private_standard_precincts_value(
                    context,meta,data_value,resolution,precinct as nat,builder.view()){
                    Err(error)=>Err(error),Ok(after)=>if resolution==u8::MAX{Err(crate::specs::part1_block_placement_error(true))}
                        else{match crate::specs::private_standard_resolutions_value(context,meta,resolution as nat+1,after){
                            Err(error)=>Err(error),Ok(last)=>Ok(crate::specs::private_standard_plan_finish(meta,grid_value,last)),
                        }},
                },
            decreases data.precincts_in_resolution-precinct,
        ))]
        while precinct < data.precincts_in_resolution {
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before=builder.view();}
            #[cfg(verus_keep_ghost)]
            proof! {reveal_with_fuel(crate::specs::private_standard_precincts_value,1);}
            let derived_origin = super::planning::derive_planned_precinct_origin(
                data.first_precinct,
                data.geometry.precincts_across,
                precinct,
                data.band_size,
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error)=derived_origin {
                    crate::specs::part2_cold_pure::<crate::specs::PrivateStandardComponentBuffers>(Err(error));
                    crate::specs::private_standard_precincts_error(context,meta,data_value,resolution,resolution_before,
                        precinct as nat,before,precinct_prefix,error);
                    crate::specs::private_standard_resolution_precincts_observed(context,meta,data_value,resolution,resolution_before,Err(error));
                    crate::specs::private_standard_resolutions_error(context,meta,initial,resolution as nat,resolution_before,resolution_prefix,error);
                    crate::specs::private_standard_plan_resolutions_observed(context,grid_value,meta,Err(error));
                }
            }
            let origin = derived_origin?;
            let region = [origin[0], origin[1], data.band_size[0], data.band_size[1]];
            let planned_row = plan_standard_precinct(
                region,
                data.block_size,
                &metadata.subbands,
                (data.first_subband, data.subband_count),
                metadata.tier1_style,
                profile,
                (resolution, precinct, builder.precincts.len()),
                builder.placements,
                builder.total,
                limits,
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error)=planned_row{
                    crate::specs::private_standard_precinct_step_observed(context,meta,data_value,resolution,precinct,before,origin,Err(error),Ok(()));
                    crate::specs::private_standard_precincts_error(context,meta,data_value,resolution,resolution_before,
                        precinct as nat,before,precinct_prefix,error);
                    crate::specs::private_standard_resolution_precincts_observed(context,meta,data_value,resolution,resolution_before,Err(error));
                    crate::specs::private_standard_resolutions_error(context,meta,initial,resolution as nat,resolution_before,resolution_prefix,error);
                    crate::specs::private_standard_plan_resolutions_observed(context,grid_value,meta,Err(error));
                }
            }
            let row = planned_row?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost row_value=row.view();}
            builder.placements = row.placements;
            builder.total = row.total;
            let reserved = crate::allocation::reserve_additional(&mut builder.precincts, 1);
            #[cfg(verus_keep_ghost)]
            proof! {
                let capacity=crate::specs::PrivateOwnerCapacityContext::ResolutionAppend {source:before.precincts,next:row_value.precinct};
                crate::specs::private_owner_capacity_observed(capacity,crate::allocation::inspection_capacity_outcome(reserved));
                if let Err(error)=reserved{
                    crate::specs::private_standard_precinct_step_observed(context,meta,data_value,resolution,precinct,before,origin,Ok(row_value),Err(error));
                    crate::specs::private_standard_precincts_error(context,meta,data_value,resolution,resolution_before,
                        precinct as nat,before,precinct_prefix,error);
                    crate::specs::private_standard_resolution_precincts_observed(context,meta,data_value,resolution,resolution_before,Err(error));
                    crate::specs::private_standard_resolutions_error(context,meta,initial,resolution as nat,resolution_before,resolution_prefix,error);
                    crate::specs::private_standard_plan_resolutions_observed(context,grid_value,meta,Err(error));
                }
            }
            reserved?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost prior_precincts=builder.precincts@;}
            builder.precincts.push(row.precinct);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::packet::private_precincts_view(builder.precincts@) =~=
                    crate::packet::private_precincts_view(prior_precincts).push(row_value.precinct));
                assert(builder.view()==crate::specs::private_standard_after_precinct(before,row_value));
                crate::specs::private_standard_precinct_step_observed(context,meta,data_value,resolution,precinct,before,origin,Ok(row_value),Ok(()));
                precinct_prefix=crate::specs::private_standard_precincts_advance(context,meta,data_value,resolution,resolution_before,
                    precinct as nat,before,precinct_prefix,builder.view());
            }
            precinct = precinct.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::private_standard_precincts_finish(context,meta,data_value,resolution,resolution_before,builder.view(),precinct_prefix);
            crate::specs::private_standard_resolution_precincts_observed(context,meta,data_value,resolution,resolution_before,Ok(builder.view()));
            reveal_with_fuel(crate::specs::private_standard_precincts_value,1);
            if resolution==u8::MAX{
                crate::specs::private_standard_resolutions_terminal_error(context,meta,initial,resolution as nat,
                    resolution_before,resolution_prefix,builder.view());
                crate::specs::private_standard_plan_resolutions_observed(context,grid_value,meta,Err(crate::specs::part1_block_placement_error(true)));
            }else{
                resolution_prefix=crate::specs::private_standard_resolutions_advance(context,meta,initial,resolution as nat,
                    resolution_before,resolution_prefix,builder.view());
            }
        }
        resolution = resolution.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost buffers=builder.view();}
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::private_standard_resolutions_finish(context,meta,initial,resolution as nat,buffers,resolution_prefix);
        crate::specs::private_standard_plan_resolutions_observed(context,grid_value,meta,Ok(buffers));
        reveal_with_fuel(crate::specs::private_standard_resolutions_value,1);
    }
    let result = PrivateHtStandardPlan {
        component: PlannedTileComponent {
            component: 0,
            x: metadata.component_x,
            y: metadata.component_y,
            width: metadata.component_width,
            height: metadata.component_height,
            output_resolution: metadata.output_resolution,
            subbands: metadata.subbands,
            placements: builder.placements,
        },
        grid,
        precincts: builder.precincts,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(PrivateHtStandardPlan::view);reveal(PrivateHtStandardPlan::invariant);reveal(super::prepare_plan_view);
        reveal(super::component_plan_metadata_view);
        assert(result.view()==crate::specs::private_standard_plan_finish(meta,grid_value,buffers));
    }
    Ok(result)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::private_component_result(crate::specs::PrivateReconstructionContext {
        plan:super::prepare_plan_view(&plan.component),precinct:crate::packet::private_precincts_view(plan.precincts@),
        style:super::prepare_style_view(coding),maximum:crate::limits::resource_decoded_bytes_limit(limits),
    },super::prepared_component_outcome(result)),
    super::prepared_component_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        super::prepared_component_outcome(result)==crate::specs::part2_prepare_component(super::prepare_plan_view(&plan.component),
            crate::specs::private_ht_precinct_planes(crate::packet::private_precincts_view(plan.precincts@)),
            super::prepare_style_view(coding),None,crate::limits::resource_decoded_bytes_limit(limits)),
))]
fn reconstruct_standard(
    plan: &PrivateHtStandardPlan,
    coding: codestream::CodingStyle,
    limits: &ResourceLimits,
) -> Result<PreparedTileComponent, DecodeError> {
    reconstruct_readable(
        &PrivateHtReadable {
            component: &plan.component,
            precincts: PrivateHtReadablePrecincts::Resolutions(&plan.precincts),
        },
        coding,
        limits,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result==crate::specs::part2_planned_tile_accounting(
        crate::specs::private_standard_plan_public_view(plan.view(),first.tile_index,codestream::tile_part_owned_view(first)),
        crate::packet::packet_selection_view(selection),initial,limits),
))]
fn account_standard_plan(
    plan: &PrivateHtStandardPlan,
    first: &TilePartPayload<'_>,
    selection: Option<&[u8]>,
    initial: (u64, u64, u64),
    limits: &ResourceLimits,
) -> Result<(u64, u64, u64), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(PrivateHtStandardPlan::view);reveal(super::prepare_plan_view);reveal(codestream::tile_part_owned_view);
        reveal_with_fuel(crate::specs::part2_account_plan_blocks,2);
    }
    let packets = initial
        .0
        .checked_add(match selection {
            None => plan.grid.packet_count(),
            Some(counts) => plan.grid.selected_packet_count(counts)?,
        })
        .ok_or_else(arithmetic_overflow)?;
    if packets > limits.maximum_packets() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: limits.maximum_packets(),
            actual: packets,
        });
    }
    let count = if selection.is_some() {
        (packets - initial.0)
            .checked_div(u64::from(first.coding_style.layers))
            .ok_or_else(arithmetic_overflow)?
    } else {
        plan.grid.total_precinct_count()?
    };
    let precincts = initial
        .1
        .checked_add(count)
        .ok_or_else(arithmetic_overflow)?;
    if precincts > limits.maximum_precincts() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Precincts,
            limit: limits.maximum_precincts(),
            actual: precincts,
        });
    }
    let blocks = if selection.is_some() {
        super::execution::count_selected_component_blocks(&plan.component, initial.2)?
    } else {
        initial
            .2
            .checked_add(plan.component.placements.len() as u64)
            .ok_or_else(arithmetic_overflow)?
    };
    if blocks > limits.maximum_code_blocks() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlocks,
            limit: limits.maximum_code_blocks(),
            actual: blocks,
        });
    }
    Ok((packets, precincts, blocks))
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::private_standard_image_admitted(private_image_context(
        size,tile,parts@,profile,discard,metadata,limits,prepared@,initial,mct_work)),
    ensures crate::specs::private_standard_image_result(private_image_context(
        size,tile,parts@,profile,discard,metadata,limits,prepared@,initial,mct_work),super::decoded_layout_tile_outcome(result)),
    super::decoded_layout_tile_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        super::decoded_layout_tile_outcome(result)==crate::specs::private_standard_image_value(private_image_context(
            size,tile,parts@,profile,discard,metadata,limits,prepared@,initial,mct_work)),
))]
pub(super) fn decode_standard(
    size: &ImageSize,
    tile: u16,
    parts: &[TilePartPayload<'_>],
    profile: &codestream::CodestreamProfile,
    discard: Option<u8>,
    metadata: &super::TileDecodeMetadata<'_, '_>,
    limits: &ResourceLimits,
    prepared: Vec<PreparedTileComponent>,
    initial: (u64, u64, u64),
    mct_work: u64,
) -> Result<DecodedLayoutTile, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost context=private_image_context(size,tile,parts@,profile,discard,metadata,limits,prepared@,initial,mct_work);}
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(private_image_context);reveal(super::tile_decode_metadata_view);reveal(codestream::tile_part_owned_view);
        crate::specs::private_ht_standard_selected_metadata(size,tile,context.parts,context.caps,discard,context.metadata);
        assert(context.parts =~= seq![context.metadata.first]);
    }
    let planned = plan_standard(size, tile, metadata.first, profile, limits);
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost planned_value=private_standard_plan_outcome(planned);}
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=planned {
            crate::specs::part2_cold_bind(
                |events|crate::specs::private_standard_plan_run(crate::specs::private_standard_image_plan_context(context),events),
                |plan,rest|crate::specs::private_standard_image_after_plan(context,plan,rest),Err(error),Err(error));
        }
    }
    let plan = planned?;
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::private_standard_plan_value_fields(crate::specs::private_standard_image_plan_context(context),plan.view());}
    let result = decode_standard_planned(
        size, tile, parts, profile, discard, metadata, limits, plan, prepared, initial, mct_work,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let value=planned_value.get_Ok_0();
        crate::specs::part2_decode_eta(|events|crate::specs::private_standard_image_after_plan(context,value,events),super::decoded_layout_tile_outcome(result));
        crate::specs::part2_cold_bind(
            |events|crate::specs::private_standard_plan_run(crate::specs::private_standard_image_plan_context(context),events),
            |plan,rest|crate::specs::private_standard_image_after_plan(context,plan,rest),planned_value,super::decoded_layout_tile_outcome(result));
    }
    result
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::private_standard_image_admitted(private_image_context(
        size,_tile,parts@,_profile,discard,metadata,limits,prepared@,initial,mct_work)),
        planned.invariant(),planned.component.component==0,
        planned.view().grid.components==1,
        planned.view().grid.component_resolutions==seq![(metadata.first.coding_style.decomposition_levels+1) as u8],
    ensures crate::specs::part2_cold_framed(|events|crate::specs::private_standard_image_after_plan(
        private_image_context(size,_tile,parts@,_profile,discard,metadata,limits,prepared@,initial,mct_work),planned.view(),events),
        super::decoded_layout_tile_outcome(result)),
    super::decoded_layout_tile_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        super::decoded_layout_tile_outcome(result)==crate::specs::private_standard_image_after_plan_value(
            private_image_context(size,_tile,parts@,_profile,discard,metadata,limits,prepared@,initial,mct_work),planned.view()),
))]
fn decode_standard_planned(
    size: &ImageSize,
    _tile: u16,
    parts: &[TilePartPayload<'_>],
    _profile: &codestream::CodestreamProfile,
    discard: Option<u8>,
    metadata: &super::TileDecodeMetadata<'_, '_>,
    limits: &ResourceLimits,
    planned: PrivateHtStandardPlan,
    prepared: Vec<PreparedTileComponent>,
    initial: (u64, u64, u64),
    mct_work: u64,
) -> Result<DecodedLayoutTile, DecodeError> {
    let mut prepared = prepared;
    let mut plan = planned;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost context=private_image_context(size,_tile,parts@,_profile,discard,metadata,limits,prepared@,initial,mct_work);
        let ghost original_plan=plan.view();
        let ghost root=|events|crate::specs::private_standard_image_after_plan(context,original_plan,events);
        let ghost mut prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(private_image_context);reveal(super::tile_decode_metadata_view);reveal(codestream::tile_part_owned_view);
        crate::specs::private_ht_standard_selected_metadata(size,_tile,context.parts,context.caps,discard,context.metadata);
        crate::packet::private_resolution_owners_known_fields(plan.precincts@);
    }
    let selection = match discard {
        None => None,
        Some(_) => Some(metadata.resolution_counts.as_slice()),
    };
    let accounted = account_standard_plan(&plan, metadata.first, selection, initial, limits);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=accounted {assert(crate::specs::part2_cold_prefix(root,prefix,Err(error)));}}
    let counters = accounted?;
    let decoded = crate::packet::decode_private_ht_resolution_packets(
        parts,
        &plan.grid,
        &mut plan.precincts,
        selection,
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let after=crate::packet::private_precincts_view(plan.precincts@);
        crate::specs::private_standard_packet_value_observed(context.parts,original_plan.grid,original_plan.precincts,
            crate::specs::private_image_selection(context),limits,(decoded,after));
        let child=|events|crate::specs::private_standard_packet_value_run(context.parts,original_plan.grid,original_plan.precincts,
            crate::specs::private_image_selection(context),limits,events);
        let next=|precincts,rest|crate::specs::private_standard_image_after_packets(context,original_plan,counters,precincts,rest);
        if let Err(error)=decoded {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if decoded.is_ok(){prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,after);}
    }
    decoded?;
    let coding = metadata.first.component_coding_styles.style(0);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=coding {assert(crate::specs::part2_cold_prefix(root,prefix,Err(error)));}}
    let coding = coding?;
    let reconstructed = reconstruct_standard(&plan, coding, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        let reconstruction=crate::specs::private_standard_image_reconstruction(context,original_plan,
            crate::packet::private_precincts_view(plan.precincts@),super::prepare_style_view(coding));
        crate::specs::private_component_calls_observed(reconstruction,super::prepared_component_outcome(reconstructed));
        let child=|events|crate::specs::private_component_calls_run(reconstruction,events);
        let next=|value,rest|crate::specs::private_image_after_component(context,counters,value,rest);
        if let Err(error)=reconstructed {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(value)=super::prepared_component_outcome(reconstructed){
            prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,value);
        }
    }
    let component = reconstructed?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost value=super::prepared_component_view(component);}
    let start = prepared.len();
    let reserved = crate::allocation::reserve_additional(&mut prepared, 1);
    #[cfg(verus_keep_ghost)]
    proof! {
        let capacity=crate::specs::PrivateOwnerCapacityContext::PreparedAppend {source:context.prepared,next:value};
        crate::specs::private_owner_capacity_observed(capacity,crate::allocation::inspection_capacity_outcome(reserved));
        let child=|events|crate::specs::private_owner_capacity_run(capacity,events);
        let next=|_:(),rest|Some((crate::specs::private_image_finish(context,counters,value),rest));
        if let Err(error)=reserved {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if reserved.is_ok(){prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,());}
    }
    reserved?;
    prepared.push(component);
    let mut work = mct_work;
    let suffix = prepared.get_mut(start..).ok_or_else(invalid_decode)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(super::prepared_components_view(suffix@) =~= seq![value]);
        reveal(super::tile_mct_option);
    }
    let finished = super::execution::finish_prepared_tile(
        suffix,
        size,
        None,
        metadata.standard,
        limits,
        &mut work,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::private_image_inactive_finish(seq![value],codestream::image_size_component_count(size),
            codestream::image_size_component_infos(size),metadata.standard,mct_work,
            crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),
            (finished,super::prepared_components_view(suffix@),work));
        assert(super::prepared_components_view(prepared@) =~= context.prepared+seq![value]);
        assert(crate::specs::part2_cold_prefix(root,prefix,crate::specs::private_image_finish(context,counters,value)));
    }
    finished?;
    Ok(DecodedLayoutTile {
        prepared,
        counters,
        mct_work: work,
    })
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn private_native_subband_context(geometry:SubbandGeometry,band:[u32;4],block:[u32;2],
        style:Tier1CodingStyle,profile:&codestream::CodestreamProfile,limits:&ResourceLimits)->crate::specs::PrivateHtSubbandContext {
        crate::specs::PrivateHtSubbandContext {
            geometry,band,block,style,allowed:crate::specs::part2_profile_multiple_sets(codestream::codestream_profile_capabilities(profile)),
            bound:crate::specs::part2_profile_magnitude_bound(codestream::codestream_profile_capabilities(profile)),
            blocks:crate::limits::resource_code_block_limit(limits),work:crate::limits::resource_work_limit(limits),
        }
    }
    closed spec fn private_rows_view(decoders:Seq<PrivateHtDecoder>,placements:Seq<ProgressionCodeBlockPlacement>)
        ->crate::specs::PrivateHtBlockRows {
        crate::specs::PrivateHtBlockRows {
            decoders:decoders.map_values(|decoder:PrivateHtDecoder|decoder.storage_view()),placements,
        }
    }
    impl PrivateHtSubband {
        closed spec fn view(&self)->crate::specs::PrivateHtSubbandState {
            crate::specs::PrivateHtSubbandState {
                geometry:self.geometry,rows:private_rows_view(self.blocks@,self.placements@),
                across:self.across,down:self.down,
            }
        }
        closed spec fn invariant(&self)->bool {
            self.blocks.len()==self.placements.len()
                && forall|i:int|0<=i<self.blocks.len() ==> #[trigger] self.blocks@[i].invariant()
        }
    }
    spec fn private_subband_outcome(result:Result<PrivateHtSubband,DecodeError>)
        ->Result<crate::specs::PrivateHtSubbandState,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok(value.view())}
    }
    spec fn private_subband_rows_outcome(result:Result<PrivateHtSubband,DecodeError>)
        ->Result<crate::specs::PrivateHtBlockRows,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok(value.view().rows)}
    }
    impl PrivateHtPlan {
        closed spec fn view(&self)->crate::specs::PrivateHtPlanState {
            crate::specs::PrivateHtPlanState {
                component:super::prepare_plan_view(&self.component),
                grid:crate::packet::packet_grid_view(&self.grid),precinct:self.precinct.storage_view(),
            }
        }
        closed spec fn invariant(&self)->bool {
            self.precinct.invariant()
        }
    }
    spec fn private_reconstruction_context(plan:&PrivateHtReadable<'_>,coding:codestream::CodingStyle,limits:&ResourceLimits)
        ->crate::specs::PrivateReconstructionContext {
        crate::specs::PrivateReconstructionContext {
            plan:super::prepare_plan_view(plan.component),precinct:plan.precincts_view(),
            style:super::prepare_style_view(coding),maximum:crate::limits::resource_decoded_bytes_limit(limits),
        }
    }
    spec fn private_plan_outcome(result:Result<PrivateHtPlan,DecodeError>)
        ->Result<crate::specs::PrivateHtPlanState,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok(value.view())}
    }
    pub(super) open spec fn private_image_context(size:&ImageSize,tile:u16,parts:Seq<TilePartPayload<'_>>,
        profile:&codestream::CodestreamProfile,discard:Option<u8>,metadata:&super::TileDecodeMetadata<'_,'_>,
        limits:&ResourceLimits,prepared:Seq<PreparedTileComponent>,initial:(u64,u64,u64),work:u64)->crate::specs::PrivateImageContext {
        crate::specs::PrivateImageContext {
            size:*size,tile,parts:codestream::tile_parts_owned_view(parts),caps:codestream::codestream_profile_capabilities(profile),
            discard,metadata:super::tile_decode_metadata_view(metadata),limits:*limits,
            prepared:super::prepared_components_view(prepared),initial,work,
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result==crate::specs::private_ht_eligible(size,tile,
        codestream::tile_parts_owned_view(parts@),codestream::codestream_profile_capabilities(profile),discard),
))]
pub(super) fn eligible(
    size: &ImageSize,
    tile: u16,
    parts: &[TilePartPayload<'_>],
    profile: &codestream::CodestreamProfile,
    discard: Option<u8>,
) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::selection_geometry_known_fields(size);
        reveal(codestream::tile_part_owned_view);
    }
    if !super::PRIVATE_HT_PRIMARY_ENABLED
        || size.components != 1
        || parts.len() != 1
        || discard.unwrap_or(0) != 0
        || !profile.part15_requires_all_ht_blocks()
    {
        return false;
    }
    let Some(first) = parts.first() else {
        return false;
    };
    let Ok(style) = first.component_coding_styles.style(0) else {
        return false;
    };
    let Ok(tier1) = style.tier1_coding_style() else {
        return false;
    };
    let Ok(roi) = first.roi_shifts.shift(0) else {
        return false;
    };
    let Ok(bounds) = size.tile_component_bounds(first.tile_index, 0) else {
        return false;
    };
    let Ok(geometry) =
        super::geometry::derive_component_resolution_geometry_for(size, style, 0, 0, Some(tile))
    else {
        return false;
    };
    matches!(tier1.block_coding, Tier1BlockCoding::HighThroughput)
        && first.tile_index == tile
        && style.decomposition_levels == 0
        && style.decomposition_structure.is_none()
        && !style.precincts_defined
        && !matches!(style.transform, WaveletTransform::Arbitrary(_))
        && !first.coding_style.multiple_component_transform
        && first.multiple_component_transform.is_none()
        && first.progression_changes.is_empty()
        && !first.packed_packet_headers.is_present()
        && !first.packet_lengths.is_present()
        && roi == 0
        && !first.has_roi_marker
        && bounds.x0 == 0
        && bounds.y0 == 0
        && bounds.x1 > 0
        && bounds.y1 > 0
        && bounds.x1 <= 32768
        && bounds.y1 <= 32768
        && geometry.precincts == 1
        && geometry.precincts_across == 1
        && geometry.precincts_down == 1
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result==if x<geometry.x0 || y<geometry.y0 {
        Err(crate::specs::part1_block_placement_error(true))
    }else{Ok(ProgressionCodeBlockPlacement {
        precinct_index:0,decoder_index:index,subband_index:0,
        x:(x-geometry.x0) as u32,y:(y-geometry.y0) as u32,
    })},
))]
fn private_placement(
    geometry: SubbandGeometry,
    x: u32,
    y: u32,
    index: usize,
) -> Result<ProgressionCodeBlockPlacement, DecodeError> {
    Ok(ProgressionCodeBlockPlacement {
        precinct_index: 0,
        decoder_index: index,
        subband_index: 0,
        x: x.checked_sub(geometry.x0).ok_or_else(arithmetic_overflow)?,
        y: y.checked_sub(geometry.y0).ok_or_else(arithmetic_overflow)?,
    })
}

#[allow(
    clippy::too_many_arguments,
    reason = "This private entry preserves the original tile's counters and publication owner."
)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::private_image_admitted(private_image_context(size,tile,parts@,profile,discard,metadata,limits,prepared@,initial,mct_work)),
    ensures crate::specs::private_image_result(private_image_context(size,tile,parts@,profile,discard,metadata,limits,prepared@,initial,mct_work),
            super::decoded_layout_tile_outcome(result)),
        super::decoded_layout_tile_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
            super::decoded_layout_tile_outcome(result)==crate::specs::private_image_value(
                private_image_context(size,tile,parts@,profile,discard,metadata,limits,prepared@,initial,mct_work)),
))]
pub(super) fn decode(
    size: &ImageSize,
    tile: u16,
    parts: &[TilePartPayload<'_>],
    profile: &codestream::CodestreamProfile,
    discard: Option<u8>,
    metadata: &super::TileDecodeMetadata<'_, '_>,
    limits: &ResourceLimits,
    prepared: Vec<PreparedTileComponent>,
    initial: (u64, u64, u64),
    mct_work: u64,
) -> Result<DecodedLayoutTile, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost context=private_image_context(size,tile,parts@,profile,discard,metadata,limits,prepared@,initial,mct_work);}
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(private_image_context);reveal(super::tile_decode_metadata_view);
        crate::specs::private_ht_selected_metadata(size,tile,context.parts,context.caps,discard,context.metadata);
    }
    let planned = plan(size, tile, metadata.first, profile, limits);
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost planned_value=private_plan_outcome(planned);}
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=planned{
            crate::specs::part2_cold_bind(
                |events|crate::specs::private_plan_run(size,tile,context.metadata.first,context.caps,limits,events),
                |plan,rest|crate::specs::private_image_after_plan(context,plan,rest),Err(error),Err(error));
        }
    }
    let plan = planned?;
    let result = decode_planned(
        size, tile, parts, profile, discard, metadata, limits, plan, prepared, initial, mct_work,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let value=planned_value.get_Ok_0();
        crate::specs::part2_decode_eta(|events|crate::specs::private_image_after_plan(context,value,events),super::decoded_layout_tile_outcome(result));
        crate::specs::part2_cold_bind(
            |events|crate::specs::private_plan_run(size,tile,context.metadata.first,context.caps,limits,events),
            |plan,rest|crate::specs::private_image_after_plan(context,plan,rest),planned_value,super::decoded_layout_tile_outcome(result));
    }
    result
}

#[allow(
    clippy::too_many_arguments,
    reason = "This concrete private planning step binds the real lattice, style, limits and owned buffers."
)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires state.invariant(),state.blocks.len()<usize::MAX,
    ensures crate::specs::part2_cold_framed(|events|crate::specs::private_block_run(
        private_native_subband_context(state.geometry,_region.0,_region.1,style,profile,_limits),
        super::planned_subband_lattice_view(lattice),state.view().rows,block[0],block[1],events),
        private_subband_rows_outcome(result)),
        private_subband_rows_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
            private_subband_rows_outcome(result)==crate::specs::private_block_value(
                private_native_subband_context(state.geometry,_region.0,_region.1,style,profile,_limits),
                super::planned_subband_lattice_view(lattice),state.view().rows,block[0],block[1]),
        match result{Ok(value)=>value.invariant() && value.geometry==state.geometry
            && value.across==state.across && value.down==state.down
            && value.blocks.len()==state.blocks.len()+1,Err(_)=>true},
    ))]
fn append_private_block(
    lattice: super::PlannedSubbandLattice,
    block: [u32; 2],
    _region: ([u32; 4], [u32; 2]),
    style: Tier1CodingStyle,
    profile: &codestream::CodestreamProfile,
    _limits: &ResourceLimits,
    state: PrivateHtSubband,
) -> Result<PrivateHtSubband, DecodeError> {
    let mut state = state;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost ctx=private_native_subband_context(state.geometry,_region.0,_region.1,style,profile,_limits);
        let ghost before=state.view().rows;
        let ghost grid=super::planned_subband_lattice_view(lattice);
        let ghost root=|events|crate::specs::private_block_run(ctx,grid,before,block[0],block[1],events);
        let ghost mut prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(PrivateHtSubband::view);reveal(PrivateHtSubband::invariant);reveal(private_rows_view);
        reveal(private_native_subband_context);
        reveal(crate::specs::private_block_run);
    }
    let derived =
        super::planning::derive_planned_codeblock_geometry(lattice.grid, lattice.clip, block);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=derived {crate::specs::part2_cold_pure::<crate::specs::PrivateHtBlockRows>(Err(error));}}
    let geometry = derived?;
    let (x, y, width, height) = geometry;
    let initialized = new_private_ht_decoder(
        width,
        height,
        state.geometry.significant_bitplanes,
        state.geometry.orientation,
        style,
        profile.part15_allows_multiple_ht_sets(),
        profile.part15_magnitude_bound(),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let context=crate::specs::private_block_context(ctx,geometry);
        crate::specs::private_decoder_initial_calls_observed(context,crate::tier1::private_decoder_outcome(initialized));
        let child=|events|crate::specs::private_decoder_initial_calls_run(context,events);
        let next=|decoder,rest|crate::specs::private_block_after_initial(ctx,before,geometry,decoder,rest);
        if let Err(error)=initialized {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(value)=crate::tier1::private_decoder_outcome(initialized) {
            prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,value);
        }
    }
    let decoder = initialized?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost decoded=decoder.storage_view();let ghost raw_decoders=state.blocks@;}
    let reserved = crate::allocation::reserve_additional(&mut state.blocks, 1);
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::storage_reservation_result);
        assert(crate::specs::storage_reservation_result(raw_decoders,state.blocks@,reserved));
        let context=crate::specs::PrivateOwnerCapacityContext::BlockAppend{source:before.decoders,next:decoded};
        crate::specs::private_owner_capacity_observed(context,crate::allocation::inspection_capacity_outcome(reserved));
        let child=|events|crate::specs::private_owner_capacity_run(context,events);
        let next=|_:(),rest|crate::specs::private_block_after_append(ctx,before,geometry,decoded,rest);
        if let Err(error)=reserved {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if reserved.is_ok(){prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,());}
    }
    reserved?;
    state.blocks.push(decoder);
    let placement = private_placement(state.geometry, x, y, state.placements.len());
    #[cfg(verus_keep_ghost)]
    proof! {
        let child=|events|Some((crate::specs::private_block_placement(ctx,geometry,before.placements.len() as usize),events));
        let next=|place,rest|crate::specs::private_block_after_placement(before,decoded,place,rest);
        crate::specs::part2_cold_pure(placement);
        if let Err(error)=placement {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(place)=placement {prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,place);}
    }
    let placement = placement?;
    let reserved = crate::allocation::reserve_additional(&mut state.placements, 1);
    #[cfg(verus_keep_ghost)]
    proof! {
        let context=crate::specs::PrivateOwnerCapacityContext::PlacementAppend{source:before.placements,next:placement};
        crate::specs::private_owner_capacity_observed(context,crate::allocation::inspection_capacity_outcome(reserved));
        let child=|events|crate::specs::private_owner_capacity_run(context,events);
        let next=|_:(),rest|Some((Ok(crate::specs::PrivateHtBlockRows {
            decoders:before.decoders.push(decoded),placements:before.placements.push(placement),
        }),rest));
        if let Err(error)=reserved {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if reserved.is_ok(){prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,());}
    }
    reserved?;
    state.placements.push(placement);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(state.blocks@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view()) =~= before.decoders.push(decoded));
        assert(state.placements@ =~= before.placements.push(placement));
        assert(crate::specs::part2_cold_prefix(root,prefix,Ok(state.view().rows)));
    }
    Ok(state)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::private_subband_result(private_native_subband_context(geometry,band,block,style,profile,limits),
        private_subband_outcome(result)),
        private_subband_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
            private_subband_outcome(result)==crate::specs::private_subband_value(private_native_subband_context(geometry,band,block,style,profile,limits)),
        match result{Ok(value)=>value.invariant()
            && value.blocks.len() as nat==value.across as nat*value.down as nat,Err(_)=>true},
))]
fn plan_subband(
    geometry: SubbandGeometry,
    style: Tier1CodingStyle,
    band: [u32; 4],
    block: [u32; 2],
    profile: &codestream::CodestreamProfile,
    limits: &ResourceLimits,
) -> Result<PrivateHtSubband, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost ctx=private_native_subband_context(geometry,band,block,style,profile,limits);}
    #[cfg(verus_keep_ghost)]
    proof! {reveal(private_native_subband_context);}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::private_subband_normal(ctx);}
    let derived = super::planning::derive_planned_subband_lattice(band, block, geometry);
    #[cfg(verus_keep_ghost)]
    proof! {
        if derived.is_err() || derived==Ok(None) {
            crate::specs::part2_cold_pure::<crate::specs::PrivateHtSubbandState>(
                match derived{Err(error)=>Err(error),Ok(_)=>Err(crate::specs::part1_block_placement_error(false))});
        }
    }
    let lattice = derived?.ok_or_else(invalid_decode)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost grid=super::planned_subband_lattice_view(lattice);}
    let count = u64::from(lattice.blocks[0])
        .checked_mul(u64::from(lattice.blocks[1]))
        .ok_or_else(arithmetic_overflow)?;
    if count > limits.maximum_code_blocks() {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateHtSubbandState>(
        Err(DecodeError::LimitExceeded{resource:Resource::CodeBlocks,limit:ctx.blocks,actual:count}));}
        return Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlocks,
            limit: limits.maximum_code_blocks(),
            actual: count,
        });
    }
    if count > limits.maximum_work_units() {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateHtSubbandState>(
        Err(DecodeError::LimitExceeded{resource:Resource::WorkUnits,limit:ctx.work,actual:count}));}
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: count,
        });
    }
    if count > usize::MAX as u64 {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_cold_pure::<crate::specs::PrivateHtSubbandState>(Err(crate::specs::part1_block_placement_error(true)));}
        return Err(arithmetic_overflow());
    }
    let capacity = count as usize;
    let reserved = crate::allocation::empty_with_capacity(capacity);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::private_subband_lattice(ctx)==Ok(grid));
        assert(crate::specs::private_subband_count(ctx,grid)==Ok(capacity));
        let context=crate::specs::private_subband_owner_context(ctx,grid,capacity);
        crate::specs::private_owner_capacity_observed(context,match reserved{Ok(_)=>Ok(()),Err(error)=>Err(error)});
        if let Err(error)=reserved {
            crate::specs::part2_cold_bind(
                |events|crate::specs::private_owner_capacity_run(context,events),
                |_:(),rest|crate::specs::private_subband_after_owner(ctx,grid,rest),Err(error),Err(error));
        }
    }
    let blocks = reserved?;
    let mut state = PrivateHtSubband {
        geometry,
        blocks,
        placements: Vec::new(),
        across: lattice.blocks[0],
        down: lattice.blocks[1],
    };
    #[cfg(verus_keep_ghost)]
    proof! {reveal(PrivateHtSubband::view);reveal(PrivateHtSubband::invariant);reveal(private_rows_view);}
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(state.blocks@.map_values(|decoder:PrivateHtDecoder|decoder.storage_view()) =~= Seq::empty());
        assert(state.view().rows==crate::specs::PrivateHtBlockRows{decoders:Seq::empty(),placements:Seq::empty()});
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost mut row_prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();}
    let mut row = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row <= lattice.blocks[1],state.invariant(),state.geometry==geometry,
            ctx==private_native_subband_context(geometry,band,block,style,profile,limits),
            grid==super::planned_subband_lattice_view(lattice),
            state.across==lattice.blocks[0],state.down==lattice.blocks[1],
            capacity as nat==lattice.blocks[0] as nat*lattice.blocks[1] as nat,
            state.blocks.len() as nat==row as nat*lattice.blocks[0] as nat,
            crate::specs::private_rows_prefix(ctx,grid,row,state.view().rows,row_prefix),
            crate::specs::private_subband_lattice(ctx)==Ok(grid),
            crate::specs::private_subband_count(ctx,grid)==Ok(capacity),
            crate::specs::private_owner_capacity_result(crate::specs::private_subband_owner_context(ctx,grid,capacity),Ok(())),
            crate::specs::private_subband_value(ctx)==match crate::specs::private_block_rows_value(ctx,grid,state.view().rows,row){
                Err(error)=>Err(error),Ok(rows)=>Ok(crate::specs::PrivateHtSubbandState {
                    geometry,rows,across:lattice.blocks[0],down:lattice.blocks[1],
                }),
            },
        decreases lattice.blocks[1] - row,
    ))]
    while row < lattice.blocks[1] {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost row_before=state.view().rows;
            let ghost mut column_prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {reveal_with_fuel(crate::specs::private_block_rows_value,1);}
        let mut column = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant column <= lattice.blocks[0], row < lattice.blocks[1],
                ctx==private_native_subband_context(geometry,band,block,style,profile,limits),
                grid==super::planned_subband_lattice_view(lattice),
                state.invariant(),state.geometry==geometry,
                state.across==lattice.blocks[0],state.down==lattice.blocks[1],
                capacity as nat==lattice.blocks[0] as nat*lattice.blocks[1] as nat,
                state.blocks.len() as nat==row as nat*lattice.blocks[0] as nat+column as nat,
                crate::specs::private_columns_prefix(ctx,grid,row_before,row,column,state.view().rows,column_prefix),
                crate::specs::private_rows_prefix(ctx,grid,row,row_before,row_prefix),
                crate::specs::private_subband_lattice(ctx)==Ok(grid),
                crate::specs::private_subband_count(ctx,grid)==Ok(capacity),
                crate::specs::private_owner_capacity_result(crate::specs::private_subband_owner_context(ctx,grid,capacity),Ok(())),
                crate::specs::private_subband_value(ctx)==match crate::specs::private_block_columns_value(ctx,grid,state.view().rows,row,column){
                    Err(error)=>Err(error),Ok(after_row)=>match crate::specs::private_block_rows_value(ctx,grid,after_row,(row+1) as u32){
                        Err(error)=>Err(error),Ok(rows)=>Ok(crate::specs::PrivateHtSubbandState {
                            geometry,rows,across:lattice.blocks[0],down:lattice.blocks[1],
                        }),
                    },
                },
            decreases lattice.blocks[0] - column,
        ))]
        while column < lattice.blocks[0] {
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint()?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before=state.view().rows;}
            #[cfg(verus_keep_ghost)]
            proof! {
                assert((row as nat)*(lattice.blocks[0] as nat)+(column as nat)<capacity) by(nonlinear_arith)
                    requires row<lattice.blocks[1],column<lattice.blocks[0],
                        capacity as nat==lattice.blocks[0] as nat*lattice.blocks[1] as nat;
                reveal_with_fuel(crate::specs::private_block_columns_value,1);
            }
            let appended = append_private_block(
                lattice,
                [column, row],
                (band, block),
                style,
                profile,
                limits,
                state,
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error)=appended{
                    crate::specs::private_columns_error(ctx,grid,row_before,row,column,before,column_prefix,error);
                    crate::specs::private_rows_error(ctx,grid,row,row_before,row_prefix,error);
                    crate::specs::private_subband_rows_observed(ctx,grid,capacity,Err(error));
                }
                if let Ok(after)=private_subband_rows_outcome(appended){
                    column_prefix=crate::specs::private_columns_advance(ctx,grid,row_before,row,column,before,column_prefix,after);
                }
            }
            state = appended?;
            column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::private_columns_finish(ctx,grid,row_before,row,state.view().rows,column_prefix);
            row_prefix=crate::specs::private_rows_advance(ctx,grid,row,row_before,row_prefix,state.view().rows);
            reveal_with_fuel(crate::specs::private_block_columns_value,1);
            assert((row as nat)*(lattice.blocks[0] as nat)+(lattice.blocks[0] as nat)==
                (row as nat+1)*(lattice.blocks[0] as nat)) by(nonlinear_arith);
        }
        row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::private_rows_finish(ctx,grid,state.view().rows,row_prefix);
        crate::specs::private_subband_rows_observed(ctx,grid,capacity,Ok(state.view().rows));
        reveal_with_fuel(crate::specs::private_block_rows_value,1);
        assert(state.blocks.len() as nat==state.across as nat*state.down as nat) by(nonlinear_arith)
            requires state.blocks.len() as nat==row as nat*lattice.blocks[0] as nat,
                row==lattice.blocks[1],state.across==lattice.blocks[0],state.down==lattice.blocks[1];
    }
    Ok(state)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result==crate::specs::private_plan_region(size,tile,super::component_plan_metadata_view(metadata)),
))]
fn private_region(
    size: &ImageSize,
    tile: u16,
    metadata: &super::PlannedComponentMetadata,
) -> Result<([u32; 4], [u32; 2]), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {reveal(super::component_plan_metadata_view);}
    let data = super::planning::prepare_resolution_plan_metadata(
        size,
        metadata.component_coding_style,
        0,
        (tile, 0),
        [metadata.bounds.x0, metadata.bounds.y0],
    )?;
    let origin = super::planning::derive_planned_precinct_origin(
        data.first_precinct,
        data.geometry.precincts_across,
        0,
        data.band_size,
    )?;
    Ok((
        [origin[0], origin[1], data.band_size[0], data.band_size[1]],
        data.block_size,
    ))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::private_ht_eligible(size,tile,seq![codestream::tile_part_owned_view(first)],
        codestream::codestream_profile_capabilities(profile),None),
    ensures crate::specs::private_plan_result(size,tile,codestream::tile_part_owned_view(first),
            codestream::codestream_profile_capabilities(profile),limits,private_plan_outcome(result)),
        private_plan_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
            private_plan_outcome(result)==crate::specs::private_plan_value(size,tile,codestream::tile_part_owned_view(first),
                codestream::codestream_profile_capabilities(profile),limits),
        match result{Ok(value)=>value.invariant() && crate::specs::private_grid_shape(value.view().grid)
            && value.component.output_resolution==0 && value.precinct.view().resolution==0
            && value.precinct.view().precinct==0,Err(_)=>true},
))]
fn plan(
    size: &ImageSize,
    tile: u16,
    first: &TilePartPayload<'_>,
    profile: &codestream::CodestreamProfile,
    limits: &ResourceLimits,
) -> Result<PrivateHtPlan, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost part=codestream::tile_part_owned_view(first);
        let ghost caps=codestream::codestream_profile_capabilities(profile);
        let ghost root=|events|crate::specs::private_plan_run(size,tile,part,caps,limits,events);
        let ghost mut prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::selection_geometry_known_fields(size);
        reveal(codestream::tile_part_owned_view);
    }
    size.tile_bounds(tile)?;
    let derived_grid = super::geometry::derive_packet_grid_for_components(
        size,
        &first.component_coding_styles,
        first.coding_style.layers,
        limits,
        Some(tile),
        0,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_spatial_derived_grid_result);
        let child=|events|crate::specs::part2_spatial_derived_grid_run(size,&part.component_coding_styles,
            part.coding_style.layers,limits,Some(tile),0,events);
        let next=|grid,rest|crate::specs::private_plan_after_grid(size,tile,part,grid,caps,limits,rest);
        if let Err(error)=derived_grid {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(grid)=crate::packet::packet_grid_outcome(derived_grid){
            prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,grid);
        }
    }
    let grid = derived_grid?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost grid_value=crate::packet::packet_grid_view(&grid);}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::private_plan_grid_fields(size,tile,part,caps,limits,grid_value);}
    let derived_metadata = super::planning::prepare_component_plan_metadata(
        size,
        &first.component_coding_styles,
        &first.component_quantizations,
        &first.roi_shifts,
        0,
        (tile, 0),
        profile.part15_requires_all_ht_blocks(),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_component_metadata_result);
        let child=|events|crate::specs::part2_component_metadata_run(size,&part.component_coding_styles,
            part.component_quantizations,&part.roi_shifts,0,(tile,0),crate::specs::part2_profile_force_ht(caps),events);
        let next=|meta,rest|crate::specs::private_plan_after_metadata(size,tile,meta,grid_value,caps,limits,rest);
        if let Err(error)=derived_metadata {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(meta)=super::component_plan_metadata_outcome(derived_metadata){
            prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,meta);
        }
    }
    let metadata = derived_metadata?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost meta=super::component_plan_metadata_view(&metadata);}
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(super::component_plan_metadata_view);
        crate::specs::private_plan_metadata_fields(size,tile,part,caps,meta);
    }
    if metadata.subbands.len() != 1 {
        #[cfg(verus_keep_ghost)]
        proof! {assert(crate::specs::part2_cold_prefix(root,prefix,Err(crate::specs::part1_block_placement_error(false))));}
        return Err(invalid_decode());
    }
    let region_result = private_region(size, tile, &metadata);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=region_result{assert(crate::specs::part2_cold_prefix(root,prefix,Err(error)));}}
    let region = region_result?;
    let planned_band = plan_subband(
        metadata.subbands[0],
        metadata.tier1_style,
        region.0,
        region.1,
        profile,
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let child=|events|crate::specs::private_subband_run(crate::specs::private_plan_subband_context(meta,region,caps,limits),events);
        let next=|band,rest|crate::specs::private_plan_after_subband(meta,grid_value,band,limits,rest);
        if let Err(error)=planned_band {crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(band)=private_subband_outcome(planned_band){
            prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,band);
        }
    }
    let band = planned_band?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost band_value=band.view();}
    #[cfg(verus_keep_ghost)]
    proof! {reveal(PrivateHtSubband::view);reveal(PrivateHtSubband::invariant);reveal(private_rows_view);}
    let planned_precinct = new_private_ht_precinct(
        band.across,
        band.down,
        band.geometry.significant_bitplanes,
        metadata.tier1_style,
        band.blocks,
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let child=|events|crate::specs::private_precinct_initial_run(
            crate::specs::private_plan_precinct_context(meta,band_value,limits),events);
        let next=|precinct,rest|Some((Ok(crate::specs::private_plan_finish(meta,grid_value,band_value,precinct)),rest));
        if let Err(error)=planned_precinct{crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(precinct)=crate::packet::private_precinct_outcome(planned_precinct){
            prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,precinct);
        }
    }
    let precinct = planned_precinct?;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(PrivateHtPlan::view);reveal(PrivateHtPlan::invariant);reveal(super::prepare_plan_view);
        assert(crate::specs::part2_cold_prefix(root,prefix,Ok(
            crate::specs::private_plan_finish(meta,grid_value,band_value,precinct.storage_view()))));
    }
    Ok(PrivateHtPlan {
        component: PlannedTileComponent {
            component: 0,
            x: metadata.component_x,
            y: metadata.component_y,
            width: metadata.component_width,
            height: metadata.component_height,
            output_resolution: metadata.output_resolution,
            subbands: metadata.subbands,
            placements: band.placements,
        },
        grid,
        precinct,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::private_place_result(old(working)@,plan.component.subbands@,
            crate::specs::private_ht_precinct_planes(plan.precincts_view()),placement,reversible,
            crate::limits::resource_decoded_bytes_limit(limits),(result,final(working)@)),
        result!=Err(DecodeError::AllocationFailed) ==> (result,final(working)@)==crate::specs::part1_prepare_placement(
            old(working)@,plan.component.subbands@,crate::specs::private_ht_precinct_planes(plan.precincts_view()),
            placement,reversible,crate::limits::resource_decoded_bytes_limit(limits)),
        final(working).bands.len()==old(working).bands.len(),
))]
fn place_private_block(
    working: &mut super::PrepareWorking,
    plan: &PrivateHtReadable<'_>,
    placement: ProgressionCodeBlockPlacement,
    reversible: bool,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial=working@;
        let ghost planes=crate::specs::private_ht_precinct_planes(plan.precincts_view());
        let ghost maximum=crate::limits::resource_decoded_bytes_limit(limits);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::private_place_normal(initial,plan.component.subbands@,planes,placement,reversible,maximum);
        reveal(crate::specs::part1_prepare_placement);
    }
    if placement.subband_index >= working.bands.len() {
        return Ok(());
    }
    let geometry = *plan
        .component
        .subbands
        .get(placement.subband_index)
        .ok_or_else(invalid_decode)?;
    let decoder = plan.decoder(placement.precinct_index, placement.decoder_index)?;
    let (width, height) = decoder.dimensions();
    if placement
        .x
        .checked_add(u32::from(width))
        .ok_or_else(arithmetic_overflow)?
        > geometry.width
        || placement
            .y
            .checked_add(u32::from(height))
            .ok_or_else(arithmetic_overflow)?
            > geometry.height
    {
        return Err(invalid_decode());
    }
    let collected = decoder.collect();
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost source=decoder.view().plane;}
    #[cfg(verus_keep_ghost)]
    proof! {
        let outcome=crate::transform::quantized_coefficients_outcome(collected);
        crate::specs::part2_coefficient_collect_frames(source,outcome);
        if let Err(error)=collected{
            crate::specs::part2_extraction_place_after_coefficients_normal(initial,geometry,placement,source,reversible,maximum,outcome);
            crate::specs::private_place_collected(initial,plan.component.subbands@,planes,placement,reversible,maximum,
                geometry,source,outcome,(Err(error),initial));
        }
    }
    let coefficients = collected?;
    let converted = crate::transform::inverse_quantize_magnitudes(
        &coefficients,
        geometry.quantization_step,
        geometry.dynamic_range,
        reversible,
        geometry.roi_shift,
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost values=crate::transform::quantized_coefficients_view(coefficients@);}
    #[cfg(verus_keep_ghost)]
    proof! {
        let outcome=crate::transform::reconstruction_outcome(converted);
        crate::specs::private_place_quantized(initial,geometry,placement,source,reversible,maximum,values,outcome);
        let effect=crate::specs::part2_extraction_place_after_quantization(initial,geometry,placement,source,reversible,outcome);
        crate::specs::private_place_collected(initial,plan.component.subbands@,planes,placement,reversible,maximum,
            geometry,source,Ok(values),effect);
    }
    let quantized = converted?;
    if quantized.fraction_bits() != if reversible { 0 } else { 16 } {
        return Err(invalid_decode());
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before_bands=working.bands@;}
    let destination = working
        .bands
        .get_mut(placement.subband_index)
        .ok_or_else(invalid_decode)?;
    let written = super::reconstruction::write_quantized_block(
        destination,
        quantized.samples(),
        u32::from(width),
        u32::from(height),
        placement.x,
        placement.y,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(super::working_bands_view(working.bands@) =~= super::working_bands_view(before_bands).update(
            placement.subband_index as int,super::working_subband_view(working.bands@[placement.subband_index as int])));
        crate::specs::private_unit_result_fields(written);
    }
    written
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::private_component_result(private_reconstruction_context(plan,coding,limits),super::prepared_component_outcome(result)),
        super::prepared_component_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
            super::prepared_component_outcome(result)==crate::specs::part2_prepare_component(super::prepare_plan_view(&plan.component),
                crate::specs::private_ht_precinct_planes(plan.precincts_view()),super::prepare_style_view(coding),None,
                crate::limits::resource_decoded_bytes_limit(limits)),
))]
fn reconstruct_readable(
    plan: &PrivateHtReadable<'_>,
    coding: codestream::CodingStyle,
    limits: &ResourceLimits,
) -> Result<PreparedTileComponent, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost context=private_reconstruction_context(plan,coding,limits);}
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(private_reconstruction_context);reveal(super::prepare_plan_view);reveal(super::prepare_style_view);
        crate::specs::private_component_normal(context);
        reveal(crate::specs::part2_prepare_component);
    }
    if plan.component.subbands.is_empty() {
        return Err(invalid_decode());
    }
    let reversible = match coding.transform {
        WaveletTransform::Reversible5x3 => true,
        WaveletTransform::Irreversible9x7 => false,
        WaveletTransform::Arbitrary(_) => return Err(invalid_decode()),
    };
    let fraction = if reversible { 0 } else { 16 };
    let selected = coding.subband_count_through_resolution(plan.component.output_resolution)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::resolution_selectors_known_fields(coding);
        crate::specs::private_subband_count_positive(coding.decomposition_levels,coding.decomposition_directions@,
            plan.component.output_resolution);
    }
    if selected > plan.component.subbands.len() {
        return Err(invalid_decode());
    }
    let initialized = super::reconstruction::initialize_prepare_working(
        &plan.component.subbands,
        selected,
        fraction,
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=initialized{crate::specs::private_component_init_error(context,reversible,selected,error);}}
    let mut working = initialized?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost initial=working@;}
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_prepare_placements_empty(initial,context.plan,
            crate::specs::private_ht_precinct_planes(context.precinct),reversible,context.maximum);
    }
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= plan.component.placements.len(),working.bands.len()==selected,selected>0,
            context==private_reconstruction_context(plan,coding,limits),
            fraction==crate::specs::part1_prepare_fraction(reversible),
            crate::specs::part2_extraction_component_preflight(context.plan,context.style,None)==Ok((reversible,selected)),
            crate::specs::part1_prepare_init_prefix(context.plan.subbands,fraction,context.maximum,selected as nat)==Ok(initial),
            crate::specs::part1_prepare_placements(initial,context.plan,crate::specs::private_ht_precinct_planes(context.precinct),
                reversible,context.maximum,index as nat)==(Ok(()),working@),
        decreases plan.component.placements.len() - index,
    ))]
    while index < plan.component.placements.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=working@;}
        #[cfg(verus_keep_ghost)]
        proof! {crate::proofs::production_impl::production_prepare_placements_step(initial,context.plan,
        crate::specs::private_ht_precinct_planes(context.precinct),reversible,context.maximum,index as nat);}
        let placed = place_private_block(
            &mut working,
            plan,
            plan.component.placements[index],
            reversible,
            limits,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error)=placed{
                crate::specs::private_component_place_error(context,reversible,selected,initial,index as nat,before,(placed,working@));
                if error!=DecodeError::AllocationFailed{
                    crate::proofs::production_impl::production_prepare_placements_error(initial,context.plan,
                        crate::specs::private_ht_precinct_planes(context.precinct),reversible,context.maximum,index as nat+1,
                        context.plan.placements.len());
                    assert(crate::specs::part1_prepare_placements(initial,context.plan,
                        crate::specs::private_ht_precinct_planes(context.precinct),reversible,context.maximum,context.plan.placements.len()).0==Err(error));
                    reveal(crate::specs::part2_prepare_component);
                    assert(crate::specs::part2_prepare_component(context.plan,crate::specs::private_ht_precinct_planes(context.precinct),
                        context.style,None,context.maximum)==Err(error));
                }
            }else{
                crate::specs::private_unit_result_fields(placed);
                crate::proofs::production_impl::production_prepare_placements_step(initial,context.plan,
                    crate::specs::private_ht_precinct_planes(context.precinct),reversible,context.maximum,index as nat);
            }
        }
        placed?;
        index += 1;
    }
    let covered = super::reconstruction::validate_prepare_coverage(&working.bands);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=covered{
            crate::specs::private_placements_normal(initial,context,reversible,context.plan.placements.len());
            crate::specs::part2_extraction_component_finish_normal(context.plan,context.style,None,reversible,context.maximum,(Ok(()),working@));
            crate::specs::private_component_placed(context,reversible,selected,initial,(Ok(()),working@),Err(error));
        }
    }
    covered?;
    let folded = super::reconstruction::reconstruct_prepare_working(
        &working.bands,
        plan.component,
        coding,
        reversible,
        None,
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::private_component_folded(context,reversible,selected,initial,working@,super::prepare_fold_outcome(folded));}
    super::reconstruction::finish_prepared_component(plan.component, folded?, fraction)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result==crate::specs::part2_planned_tile_accounting(
        crate::specs::private_plan_public_view(plan.view(),first.tile_index,codestream::tile_part_owned_view(first)),
        crate::packet::packet_selection_view(selection),initial,limits),
))]
fn account_private_plan(
    plan: &PrivateHtPlan,
    first: &TilePartPayload<'_>,
    selection: Option<&[u8]>,
    limits: &ResourceLimits,
    initial: (u64, u64, u64),
) -> Result<(u64, u64, u64), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(PrivateHtPlan::view);reveal(super::prepare_plan_view);reveal(codestream::tile_part_owned_view);
        reveal_with_fuel(crate::specs::part2_account_plan_blocks,2);
    }
    let packets = initial
        .0
        .checked_add(match selection {
            None => plan.grid.packet_count(),
            Some(counts) => plan.grid.selected_packet_count(counts)?,
        })
        .ok_or_else(arithmetic_overflow)?;
    if packets > limits.maximum_packets() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: limits.maximum_packets(),
            actual: packets,
        });
    }
    let precinct_count = if selection.is_some() {
        (packets - initial.0)
            .checked_div(u64::from(first.coding_style.layers))
            .ok_or_else(arithmetic_overflow)?
    } else {
        plan.grid.total_precinct_count()?
    };
    let precincts = initial
        .1
        .checked_add(precinct_count)
        .ok_or_else(arithmetic_overflow)?;
    if precincts > limits.maximum_precincts() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Precincts,
            limit: limits.maximum_precincts(),
            actual: precincts,
        });
    }
    let blocks = if selection.is_some() {
        super::execution::count_selected_component_blocks(&plan.component, initial.2)?
    } else {
        initial
            .2
            .checked_add(plan.component.placements.len() as u64)
            .ok_or_else(arithmetic_overflow)?
    };
    if blocks > limits.maximum_code_blocks() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlocks,
            limit: limits.maximum_code_blocks(),
            actual: blocks,
        });
    }
    Ok((packets, precincts, blocks))
}

#[allow(
    clippy::too_many_arguments,
    reason = "The private entry preserves the original tile's counters and publication owner."
)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::private_image_admitted(private_image_context(size,_tile,parts@,_profile,discard,metadata,limits,prepared@,initial,mct_work)),
        planned.invariant(),crate::specs::private_grid_shape(planned.view().grid),planned.component.output_resolution==0,
        planned.precinct.view().resolution==0,planned.precinct.view().precinct==0,
    ensures crate::specs::private_image_after_plan_result(private_image_context(size,_tile,parts@,_profile,discard,metadata,limits,prepared@,initial,mct_work),
            planned.view(),super::decoded_layout_tile_outcome(result)),
        super::decoded_layout_tile_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
            super::decoded_layout_tile_outcome(result)==crate::specs::private_image_after_plan_value(
                private_image_context(size,_tile,parts@,_profile,discard,metadata,limits,prepared@,initial,mct_work),planned.view()),
))]
#[allow(
    clippy::manual_map,
    reason = "Keep the native slice projection explicit in the private governing contract."
)]
fn decode_planned(
    size: &ImageSize,
    _tile: u16,
    parts: &[TilePartPayload<'_>],
    _profile: &codestream::CodestreamProfile,
    discard: Option<u8>,
    metadata: &super::TileDecodeMetadata<'_, '_>,
    limits: &ResourceLimits,
    planned: PrivateHtPlan,
    prepared: Vec<PreparedTileComponent>,
    initial: (u64, u64, u64),
    mct_work: u64,
) -> Result<DecodedLayoutTile, DecodeError> {
    let mut prepared = prepared;
    let mut plan = planned;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost ctx=private_image_context(size,_tile,parts@,_profile,discard,metadata,limits,prepared@,initial,mct_work);
        let ghost planned_value=plan.view();
        let ghost root=|events|crate::specs::private_image_after_plan(ctx,planned_value,events);
        let ghost mut prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(private_image_context);reveal(super::tile_decode_metadata_view);reveal(codestream::tile_part_owned_view);
        crate::specs::private_ht_selected_metadata(size,_tile,ctx.parts,ctx.caps,discard,ctx.metadata);
    }
    let first = metadata.first;
    let selection = match discard {
        None => None,
        Some(_) => Some(metadata.resolution_counts.as_slice()),
    };
    let accounted = account_private_plan(&plan, first, selection, limits, initial);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=accounted{
            assert(crate::specs::part2_cold_prefix(root,prefix,Err(error)));
        }
    }
    let counters = accounted?;
    let packets_result = plan
        .precinct
        .decode_tile(parts, &plan.grid, selection, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::private_packet_value_observed(ctx.parts,planned_value.grid,planned_value.precinct,
            crate::specs::private_image_selection(ctx),limits,(packets_result,plan.precinct.storage_view()));
        let child=|events|crate::specs::private_packet_value_run(ctx.parts,planned_value.grid,planned_value.precinct,
            crate::specs::private_image_selection(ctx),limits,events);
        let next=|precinct,rest|crate::specs::private_image_after_packets(ctx,planned_value,counters,precinct,rest);
        if let Err(error)=packets_result{crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if packets_result.is_ok(){prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,plan.precinct.storage_view());}
    }
    packets_result?;
    let style_result = first.component_coding_styles.style(0);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=style_result{assert(crate::specs::part2_cold_prefix(root,prefix,Err(error)));}
    }
    let coding = style_result?;
    let readable = PrivateHtReadable {
        component: &plan.component,
        precincts: PrivateHtReadablePrecincts::One(&plan.precinct),
    };
    let reconstructed = reconstruct_readable(&readable, coding, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        let context=private_reconstruction_context(&readable,coding,limits);
        crate::specs::private_component_calls_observed(context,super::prepared_component_outcome(reconstructed));
        let child=|events|crate::specs::private_component_calls_run(context,events);
        let next=|value,rest|crate::specs::private_image_after_component(ctx,counters,value,rest);
        if let Err(error)=reconstructed{crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if let Ok(value)=super::prepared_component_outcome(reconstructed){
            prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,value);
        }
    }
    let component = reconstructed?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost value=super::prepared_component_view(component);}
    let start = prepared.len();
    let reserved = crate::allocation::reserve_additional(&mut prepared, 1);
    #[cfg(verus_keep_ghost)]
    proof! {
        let context=crate::specs::PrivateOwnerCapacityContext::PreparedAppend{source:ctx.prepared,next:value};
        crate::specs::private_owner_capacity_observed(context,crate::allocation::inspection_capacity_outcome(reserved));
        let child=|events|crate::specs::private_owner_capacity_run(context,events);
        let next=|_:(),rest|Some((crate::specs::private_image_finish(ctx,counters,value),rest));
        if let Err(error)=reserved{crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);}
        if reserved.is_ok(){prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,());}
    }
    reserved?;
    prepared.push(component);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(super::prepared_components_view(prepared@) =~= ctx.prepared.push(value));
        assert(super::prepared_components_view(prepared@).skip(start as int) =~= seq![value]);
    }
    let mut work = mct_work;
    let suffix = prepared.get_mut(start..).ok_or_else(invalid_decode)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(super::tile_mct_option);
        assert(super::prepared_components_view(suffix@) =~= seq![value]);
    }
    let finished = super::execution::finish_prepared_tile(
        suffix,
        size,
        None,
        metadata.standard,
        limits,
        &mut work,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let suffix_values=super::prepared_components_view(suffix@);
        crate::specs::private_image_inactive_finish(seq![value],codestream::image_size_component_count(size),
            codestream::image_size_component_infos(size),metadata.standard,mct_work,
            crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),(finished,suffix_values,work));
        assert(super::prepared_components_view(prepared@) =~= ctx.prepared+seq![value]);
        assert(crate::specs::part2_cold_prefix(root,prefix,crate::specs::private_image_finish(ctx,counters,value)));
    }
    finished?;
    Ok(DecodedLayoutTile {
        prepared,
        counters,
        mct_work: work,
    })
}
