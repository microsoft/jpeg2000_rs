use super::*;
verus! {

pub type PrivatePacketDecodeEffect=(Result<crate::packet::TilePacketDecode,crate::DecodeError>,PrivateHtPrecinctState);

pub(crate) open spec fn private_tile_calls_run(params:Part1TilePacketParameters,initial:PrivateTileExecution,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateTileEffect> {
    if events.len()==0{None}else{match events[0]{
        Part2JpipSnapshotEvent::PrivateTilePlaneCalls{params:actual,initial:before,calls}=>{
            if actual!=params || before!=initial{None}else{match private_tile_run(params,initial,calls){
                Some((Ok(effect),rest))=>if rest.len()==0{Some((Ok(effect),events.drop_first()))}else{None},
                _=>None,
            }}
        },
        _=>None,
    }}
}

pub(crate) open spec fn private_tile_calls_result(params:Part1TilePacketParameters,initial:PrivateTileExecution,result:PrivateTileEffect)->bool {
    part2_cold_framed(|events|private_tile_calls_run(params,initial,events),Ok(result))
}

pub(crate) proof fn private_tile_calls_observed(params:Part1TilePacketParameters,initial:PrivateTileExecution,result:PrivateTileEffect)
    requires private_tile_run_result(params,initial,result),
    ensures private_tile_calls_result(params,initial,result),
{
    let run=|tail|private_tile_run(params,initial,tail);
    let calls=choose|calls:Seq<Part2Tier1StorageEvent>| #[trigger] part2_tier1_storage_prefix(run,calls,Ok(result));
    part2_tier1_storage_at(run,calls,Ok(result),Seq::empty());
    let prefix=seq![Part2JpipSnapshotEvent::PrivateTilePlaneCalls{params,initial,calls}];
    assert forall|tail|private_tile_calls_run(params,initial,prefix+tail)==Some((Ok(result),tail)) by {
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|private_tile_calls_run(params,initial,events),prefix,Ok(result)));
}

pub(crate) open spec fn private_packet_after_progress_run(params:Part1TilePacketParameters,before:PrivateHtPrecinctState,
    progress:Part1TilePacketProgress,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivatePacketDecodeEffect> {
    part2_jpip_snapshot_bind(private_tile_calls_run(params,PrivateTileExecution{precinct:before,progress},events),
        |effect:PrivateTileEffect,rest|Some((Ok(match effect.0{
            Err(error)=>(Err(error),effect.1.precinct),
            Ok(())=>(part1_tile_finish(params,effect.1.progress).0,effect.1.precinct),
        }),rest)))
}

pub(crate) open spec fn private_packet_decode_run(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:PrivateHtPrecinctState,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
    events:Seq<Part2JpipSnapshotEvent>)->Option<(PrivatePacketDecodeEffect,Seq<Part2JpipSnapshotEvent>)> {
    match part2_packet_input_run(parts,grid,seq![before.logical],selection,limits,events){
        None=>None,Some((Err(error),rest))=>Some(((Err(error),before),rest)),
        Some((Ok(input),rest))=>{
            let params=part2_packet_parameters(parts,grid,input,selection,limits);
            match part2_progress_initial_run(params,rest){
                None=>None,Some((Err(error),tail))=>Some(((Err(error),before),tail)),
                Some((Ok(progress),tail))=>match private_packet_after_progress_run(params,before,progress,tail){
                    None=>None,Some((Err(error),suffix))=>Some(((Err(error),before),suffix)),
                    Some((Ok(effect),suffix))=>Some((effect,suffix)),
                },
            }
        },
    }
}

pub(crate) open spec fn private_packet_decode_result(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:PrivateHtPrecinctState,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,result:PrivatePacketDecodeEffect)->bool {
    exists|prefix:Seq<Part2JpipSnapshotEvent>| #[trigger]
        private_packet_decode_prefix(parts,grid,before,selection,limits,prefix,result)
}

pub(crate) open spec fn private_packet_decode_prefix(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:PrivateHtPrecinctState,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,prefix:Seq<Part2JpipSnapshotEvent>,
    result:PrivatePacketDecodeEffect)->bool {
    forall|tail| #[trigger] private_packet_decode_run(parts,grid,before,selection,limits,prefix+tail)==Some((result,tail))
}

pub(crate) open spec fn private_packet_decode_value(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:PrivateHtPrecinctState,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits)->PrivatePacketDecodeEffect {
    match part1_progression_tile_input_owned(parts,grid,seq![before.logical],selection,limits){
        Err(error)=>(Err(error),before),
        Ok(input)=>{
            let params=part2_packet_parameters(parts,grid,input,selection,limits);
            match part1_tile_progress_initial(params){
                Err(error)=>(Err(error),before),
                Ok(progress)=>{
                    let effect=private_tile_value(params,PrivateTileExecution{precinct:before,progress});
                    match effect.0{
                        Err(error)=>(Err(error),effect.1.precinct),
                        Ok(())=>(part1_tile_finish(params,effect.1.progress).0,effect.1.precinct),
                    }
                },
            }
        },
    }
}

pub(crate) proof fn private_packet_input_error(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,before:PrivateHtPrecinctState,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,error:crate::DecodeError)
    requires part2_packet_input_result(parts,grid,seq![before.logical],selection,limits,Err(error)),
    ensures private_packet_decode_result(parts,grid,before,selection,limits,(Err(error),before)),
{
    reveal(part2_packet_input_result);
    let child=|events|part2_packet_input_run(parts,grid,seq![before.logical],selection,limits,events);
    let prefix=part2_cold_witness(child,Err(error));
    assert forall|tail|private_packet_decode_run(parts,grid,before,selection,limits,prefix+tail)==Some(((Err(error),before),tail)) by {
        part2_cold_prefix_at(child,prefix,Err(error),tail);
    }
    assert(private_packet_decode_prefix(parts,grid,before,selection,limits,prefix,(Err(error),before)));
}

pub(crate) proof fn private_packet_progress_error(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,before:PrivateHtPrecinctState,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,input:Part1TilePacketPreparation,error:crate::DecodeError)
    requires part2_packet_input_result(parts,grid,seq![before.logical],selection,limits,Ok(input)),
        part2_progress_initial_result(part2_packet_parameters(parts,grid,input,selection,limits),Err(error)),
    ensures private_packet_decode_result(parts,grid,before,selection,limits,(Err(error),before)),
{
    reveal(part2_packet_input_result);reveal(part2_progress_initial_result);
    let params=part2_packet_parameters(parts,grid,input,selection,limits);
    let first=|events|part2_packet_input_run(parts,grid,seq![before.logical],selection,limits,events);
    let second=|events|part2_progress_initial_run(params,events);
    let p=part2_cold_witness(first,Ok(input));let q=part2_cold_witness(second,Err(error));
    assert forall|tail|private_packet_decode_run(parts,grid,before,selection,limits,(p+q)+tail)==Some(((Err(error),before),tail)) by {
        assert((p+q)+tail =~= p+(q+tail));
        part2_cold_prefix_at(first,p,Ok(input),q+tail);
        part2_cold_prefix_at(second,q,Err(error),tail);
    }
    assert(private_packet_decode_prefix(parts,grid,before,selection,limits,p+q,(Err(error),before)));
}

pub(crate) proof fn private_packet_decode_observed(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,before:PrivateHtPrecinctState,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,input:Part1TilePacketPreparation,progress:Part1TilePacketProgress,
    effect:PrivateTileEffect)
    requires part2_packet_input_result(parts,grid,seq![before.logical],selection,limits,Ok(input)),
        part2_progress_initial_result(part2_packet_parameters(parts,grid,input,selection,limits),Ok(progress)),
        private_tile_run_result(part2_packet_parameters(parts,grid,input,selection,limits),
            PrivateTileExecution{precinct:before,progress},effect),
    ensures private_packet_decode_result(parts,grid,before,selection,limits,
        match effect.0{Err(error)=>(Err(error),effect.1.precinct),
            Ok(())=>(part1_tile_finish(part2_packet_parameters(parts,grid,input,selection,limits),effect.1.progress).0,effect.1.precinct)}),
{
    reveal(part2_packet_input_result);reveal(part2_progress_initial_result);
    let params=part2_packet_parameters(parts,grid,input,selection,limits);
    private_tile_calls_observed(params,PrivateTileExecution{precinct:before,progress},effect);
    let first=|events|part2_packet_input_run(parts,grid,seq![before.logical],selection,limits,events);
    let second=|events|part2_progress_initial_run(params,events);
    let third=|events|private_tile_calls_run(params,PrivateTileExecution{precinct:before,progress},events);
    let p=part2_cold_witness(first,Ok(input));let q=part2_cold_witness(second,Ok(progress));
    let r=part2_cold_witness(third,Ok(effect));
    let outcome=match effect.0{Err(error)=>(Err(error),effect.1.precinct),
        Ok(())=>(part1_tile_finish(params,effect.1.progress).0,effect.1.precinct)};
    assert forall|tail|private_packet_decode_run(parts,grid,before,selection,limits,((p+q)+r)+tail)==Some((outcome,tail)) by {
        assert(((p+q)+r)+tail =~= p+(q+(r+tail)));
        part2_cold_prefix_at(first,p,Ok(input),q+(r+tail));
        part2_cold_prefix_at(second,q,Ok(progress),r+tail);
        part2_cold_prefix_at(third,r,Ok(effect),tail);
    }
    assert(private_packet_decode_prefix(parts,grid,before,selection,limits,(p+q)+r,outcome));
}

pub(crate) proof fn private_packet_input_parameters(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:PrivateHtPrecinctState,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,input:Part1TilePacketPreparation)
    requires parts.len()==1,private_grid_shape(grid),
        (match parts[0].packed_packet_headers.source{Part1PackedHeaderSource::None=>true,_=>false}),
        (match parts[0].packet_lengths.source{Part1PacketLengthSource::None=>true,_=>false}),
        selection.is_none() || selection==Some(seq![1u8]),
        part1_progression_tile_input_owned(parts,grid,seq![before.logical],selection,limits)==Ok(input),
    ensures private_tile_parameters(part2_packet_parameters(parts,grid,input,selection,limits)),
{
    reveal_with_fuel(part1_progression_payloads_owned,2);
    reveal(part1_packed_header_reassembly);
}

pub(crate) proof fn private_packet_decode_value_fields(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:PrivateHtPrecinctState,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits)
    requires parts.len()==1,private_grid_shape(grid),private_precinct_wf(before),
        (match parts[0].packed_packet_headers.source{Part1PackedHeaderSource::None=>true,_=>false}),
        (match parts[0].packet_lengths.source{Part1PacketLengthSource::None=>true,_=>false}),
        selection.is_none() || selection==Some(seq![1u8]),
    ensures private_precinct_wf(private_packet_decode_value(parts,grid,before,selection,limits).1),
        (private_packet_decode_value(parts,grid,before,selection,limits).0,
            seq![private_packet_decode_value(parts,grid,before,selection,limits).1.logical])
            ==part1_progression_tile_decode_owned(parts,grid,seq![before.logical],selection,limits),
{
    if let Ok(input)=part1_progression_tile_input_owned(parts,grid,seq![before.logical],selection,limits){
        private_packet_input_parameters(parts,grid,before,selection,limits,input);
        let params=part2_packet_parameters(parts,grid,input,selection,limits);
        if let Ok(progress)=part1_tile_progress_initial(params){
            private_tile_value_fields(params,PrivateTileExecution{precinct:before,progress});
        }
    }

}

    pub(crate) proof fn private_packet_decode_normal(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
        before:PrivateHtPrecinctState,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits)
        requires parts.len()==1,private_grid_shape(grid),private_precinct_wf(before),
            (match parts[0].packed_packet_headers.source{Part1PackedHeaderSource::None=>true,_=>false}),
            (match parts[0].packet_lengths.source{Part1PacketLengthSource::None=>true,_=>false}),
            selection.is_none() || selection==Some(seq![1u8]),
        ensures private_packet_decode_result(parts,grid,before,selection,limits,private_packet_decode_value(parts,grid,before,selection,limits)),
    {
        part2_packet_input_normal(parts,grid,seq![before.logical],selection,limits);
        match part1_progression_tile_input_owned(parts,grid,seq![before.logical],selection,limits){
            Err(error)=>{private_packet_input_error(parts,grid,before,selection,limits,error);},
            Ok(input)=>{
                let params=part2_packet_parameters(parts,grid,input,selection,limits);
                private_packet_input_parameters(parts,grid,before,selection,limits,input);
                part2_progress_initial_normal(params);
                match part1_tile_progress_initial(params){
                    Err(error)=>{private_packet_progress_error(parts,grid,before,selection,limits,input,error);},
                    Ok(progress)=>{
                        private_tile_run_normal(params,PrivateTileExecution{precinct:before,progress});
                        private_packet_decode_observed(parts,grid,before,selection,limits,input,progress,
                            private_tile_value(params,PrivateTileExecution{precinct:before,progress}));
                    },
                }
            },
        }
    }
}
