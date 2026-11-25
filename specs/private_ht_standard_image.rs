use super::*;
verus! {

pub(crate) open spec fn private_standard_image_admitted(context:PrivateImageContext)->bool {
    private_ht_standard_eligible(&context.size,context.tile,context.parts,context.caps,context.discard)
        && part2_tile_decode_metadata_owned(context.parts,crate::codestream::image_size_component_count(&context.size),context.discard)==Ok(context.metadata)
}

pub(crate) open spec fn private_standard_image_plan_context(context:PrivateImageContext)->PrivateStandardPlanContext {
    PrivateStandardPlanContext {size:context.size,tile:context.tile,first:context.metadata.first,caps:context.caps,limits:context.limits}
}

pub(crate) open spec fn private_standard_packet_value_run(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<PrivateHtPrecinctState>> {
    match private_resolution_decode_run(parts,grid,before,selection,limits,events){
        None=>None,Some(((Err(error),_),rest))=>Some((Err(error),rest)),
        Some(((Ok(_),after),rest))=>Some((Ok(after),rest)),
    }
}

pub(crate) proof fn private_standard_packet_value_observed(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,result:PrivateResolutionDecodeEffect)
    requires private_resolution_decode_result(parts,grid,before,selection,limits,result),
    ensures part2_cold_framed(|events|private_standard_packet_value_run(parts,grid,before,selection,limits,events),
        match result.0{Err(error)=>Err(error),Ok(_)=>Ok(result.1)}),
{
    let prefix=choose|prefix| #[trigger] private_resolution_decode_prefix(parts,grid,before,selection,limits,prefix,result);
    let value=match result.0{Err(error)=>Err(error),Ok(_)=>Ok(result.1)};
    assert forall|tail|private_standard_packet_value_run(parts,grid,before,selection,limits,prefix+tail)==Some((value,tail)) by {}
    assert(part2_cold_prefix(|events|private_standard_packet_value_run(parts,grid,before,selection,limits,events),prefix,value));
}

pub(crate) open spec fn private_standard_image_reconstruction(context:PrivateImageContext,plan:PrivateStandardPlanState,
    precincts:Seq<PrivateHtPrecinctState>,style:Part1PrepareStyle)->PrivateReconstructionContext {
    PrivateReconstructionContext {plan:plan.component,precinct:precincts,style,maximum:crate::limits::resource_decoded_bytes_limit(&context.limits)}
}

pub(crate) open spec fn private_standard_image_after_packets(context:PrivateImageContext,plan:PrivateStandardPlanState,
    counters:(u64,u64,u64),precincts:Seq<PrivateHtPrecinctState>,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2DecodedLayoutTile> {
    match crate::codestream::component_coding_style_result(&context.metadata.first.component_coding_styles,0){
        Err(error)=>Some((Err(error),events)),
        Ok(style)=>part2_jpip_snapshot_bind(private_component_calls_run(
            private_standard_image_reconstruction(context,plan,precincts,crate::decode::prepare_style_view(style)),events),
            |value,rest|private_image_after_component(context,counters,value,rest)),
    }
}

pub(crate) open spec fn private_standard_image_after_plan(context:PrivateImageContext,plan:PrivateStandardPlanState,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2DecodedLayoutTile> {
    match part2_planned_tile_accounting(private_standard_plan_public(private_standard_image_plan_context(context),plan),
        private_image_selection(context),context.initial,&context.limits){
        Err(error)=>Some((Err(error),events)),
        Ok(counters)=>part2_jpip_snapshot_bind(private_standard_packet_value_run(context.parts,plan.grid,plan.precincts,
            private_image_selection(context),&context.limits,events),
            |after,rest|private_standard_image_after_packets(context,plan,counters,after,rest)),
    }
}

pub(crate) open spec fn private_standard_image_run(context:PrivateImageContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2DecodedLayoutTile> {
    part2_jpip_snapshot_bind(private_standard_plan_run(private_standard_image_plan_context(context),events),
        |plan,rest|private_standard_image_after_plan(context,plan,rest))
}

pub(crate) open spec fn private_standard_image_result(context:PrivateImageContext,
    result:Result<Part2DecodedLayoutTile,crate::DecodeError>)->bool {
    part2_cold_framed(|events|private_standard_image_run(context,events),result)
}

pub(crate) open spec fn private_standard_image_after_plan_value(context:PrivateImageContext,plan:PrivateStandardPlanState)
    ->Result<Part2DecodedLayoutTile,crate::DecodeError> {
    match part2_planned_tile_accounting(private_standard_plan_public(private_standard_image_plan_context(context),plan),
        private_image_selection(context),context.initial,&context.limits){
        Err(error)=>Err(error),
        Ok(counters)=>{
            let packets=private_resolution_decode_value(context.parts,plan.grid,plan.precincts,private_image_selection(context),&context.limits);
            match packets.0 {
                Err(error)=>Err(error),
                Ok(_)=>match crate::codestream::component_coding_style_result(&context.metadata.first.component_coding_styles,0){
                    Err(error)=>Err(error),
                    Ok(style)=>match part2_prepare_component(plan.component,private_ht_precinct_planes(packets.1),
                        crate::decode::prepare_style_view(style),None,crate::limits::resource_decoded_bytes_limit(&context.limits)){
                        Err(error)=>Err(error),Ok(value)=>private_image_finish(context,counters,value),
                    },
                },
            }
        },
    }
}

pub(crate) open spec fn private_standard_image_value(context:PrivateImageContext)->Result<Part2DecodedLayoutTile,crate::DecodeError> {
    match private_standard_plan_value(private_standard_image_plan_context(context)){
        Err(error)=>Err(error),Ok(plan)=>private_standard_image_after_plan_value(context,plan),
    }
}

pub(crate) proof fn private_ht_standard_disjoint(context:PrivateImageContext)
    requires private_standard_image_admitted(context),
    ensures !private_ht_eligible(&context.size,context.tile,context.parts,context.caps,context.discard),
{}

pub(crate) proof fn private_standard_image_fields(context:PrivateImageContext,plan:PrivateStandardPlanState)
    requires private_standard_image_admitted(context),
        private_standard_plan_value(private_standard_image_plan_context(context))==Ok(plan),
    ensures context.parts.len()==1,plan.grid.components==1,plan.grid.component_resolutions.len()==1,
        private_image_selection(context).is_none() || private_image_selection(context)==Some(plan.grid.component_resolutions),
        (match context.parts[0].packed_packet_headers.source{Part1PackedHeaderSource::None=>true,_=>false}),
        (match context.parts[0].packet_lengths.source{Part1PacketLengthSource::None=>true,_=>false}),
        forall|i:int|0<=i<plan.precincts.len() ==> #[trigger] private_precinct_wf(plan.precincts[i]),
{
    private_ht_standard_selected_metadata(&context.size,context.tile,context.parts,context.caps,context.discard,context.metadata);
    assert(context.parts =~= seq![context.metadata.first]);
    private_standard_plan_value_fields(private_standard_image_plan_context(context),plan);
}

pub(crate) proof fn private_standard_image_normal(context:PrivateImageContext)
    requires private_standard_image_admitted(context),
    ensures private_standard_image_result(context,private_standard_image_value(context)),
{
    private_ht_standard_selected_metadata(&context.size,context.tile,context.parts,context.caps,context.discard,context.metadata);
    let planned=private_standard_plan_value(private_standard_image_plan_context(context));
    let result=private_standard_image_value(context);
    private_standard_plan_normal(private_standard_image_plan_context(context));
    if let Ok(plan)=planned{
        private_standard_image_fields(context,plan);
        let accounting=part2_planned_tile_accounting(private_standard_plan_public(private_standard_image_plan_context(context),plan),
            private_image_selection(context),context.initial,&context.limits);
        match accounting{
            Err(_)=>part2_cold_pure(result),
            Ok(counters)=>{
                let packets=private_resolution_decode_value(context.parts,plan.grid,plan.precincts,private_image_selection(context),&context.limits);
                private_resolution_decode_normal(context.parts,plan.grid,plan.precincts,private_image_selection(context),&context.limits);
                private_standard_packet_value_observed(context.parts,plan.grid,plan.precincts,private_image_selection(context),&context.limits,packets);
                if packets.0.is_ok(){
                    match crate::codestream::component_coding_style_result(&context.metadata.first.component_coding_styles,0){
                        Err(_)=>part2_cold_pure(result),
                        Ok(style)=>{
                            let reconstruction=private_standard_image_reconstruction(context,plan,packets.1,crate::decode::prepare_style_view(style));
                            let value=part2_prepare_component(plan.component,private_ht_precinct_planes(packets.1),reconstruction.style,None,reconstruction.maximum);
                            private_component_normal(reconstruction);private_component_calls_observed(reconstruction,value);
                            if let Ok(component)=value{
                                let capacity=PrivateOwnerCapacityContext::PreparedAppend {source:context.prepared,next:component};
                                private_owner_capacity_observed(capacity,Ok(()));
                                part2_cold_pure(result);
                                part2_cold_bind(|events|private_owner_capacity_run(capacity,events),
                                    |_:(),rest|Some((private_image_finish(context,counters,component),rest)),Ok(()),result);
                                part2_decode_eta(|events|private_image_after_component(context,counters,component,events),result);
                            }
                            part2_cold_bind(|events|private_component_calls_run(reconstruction,events),
                                |component,rest|private_image_after_component(context,counters,component,rest),value,result);
                        },
                    }
                    part2_decode_eta(|events|private_standard_image_after_packets(context,plan,counters,packets.1,events),result);
                }
                part2_cold_bind(|events|private_standard_packet_value_run(context.parts,plan.grid,plan.precincts,private_image_selection(context),&context.limits,events),
                    |after,rest|private_standard_image_after_packets(context,plan,counters,after,rest),
                    match packets.0{Err(error)=>Err(error),Ok(_)=>Ok(packets.1)},result);
            },
        }
        part2_decode_eta(|events|private_standard_image_after_plan(context,plan,events),result);
    }
    part2_cold_bind(|events|private_standard_plan_run(private_standard_image_plan_context(context),events),
        |plan,rest|private_standard_image_after_plan(context,plan,rest),planned,result);
}

pub(crate) proof fn private_standard_image_reference(context:PrivateImageContext)
    requires private_standard_image_admitted(context),
    ensures private_standard_image_value(context)==part2_decode_tile_parts_owned(&context.size,context.tile,context.parts,context.caps,
        context.discard,&context.limits,context.prepared,context.initial,context.work),
{
    private_ht_standard_selected_metadata(&context.size,context.tile,context.parts,context.caps,context.discard,context.metadata);
    assert(context.parts =~= seq![context.metadata.first]);
    private_standard_plan_reference(private_standard_image_plan_context(context));
    reveal_with_fuel(part2_reconstruct_components_prefix,2);
    if let Ok(plan)=private_standard_plan_value(private_standard_image_plan_context(context)){
        private_standard_image_fields(context,plan);
        private_resolution_decode_value_fields(context.parts,plan.grid,plan.precincts,private_image_selection(context),&context.limits);
        let packets=private_resolution_decode_value(context.parts,plan.grid,plan.precincts,private_image_selection(context),&context.limits);
        assert(part2_precinct_decoder_planes(private_precincts_logical(packets.1)) =~= private_ht_precinct_planes(packets.1));
        if packets.0.is_ok(){
            if let Ok(style)=crate::codestream::component_coding_style_result(&context.metadata.first.component_coding_styles,0){
                if let Ok(value)=part2_prepare_component(plan.component,private_ht_precinct_planes(packets.1),
                    crate::decode::prepare_style_view(style),None,crate::limits::resource_decoded_bytes_limit(&context.limits)){
                    assert(context.prepared.push(value).skip(context.prepared.len() as int) =~= seq![value]);
                    assert(context.prepared.push(value) =~= context.prepared+seq![value]);
                }
            }
        }
    }
}

pub(crate) proof fn private_standard_image_tile_observed(context:PrivateImageContext,
    result:Result<Part2DecodedLayoutTile,crate::DecodeError>)
    requires private_standard_image_admitted(context),
        part2_tile_metadata_result(context.parts,crate::codestream::image_size_component_count(&context.size),context.discard,Ok(context.metadata)),
        private_standard_image_result(context,result),
    ensures part2_tile_decode_result(&context.size,context.tile,context.parts,context.caps,context.discard,&context.limits,
        context.prepared,context.initial,context.work,result),
{
    reveal(part2_tile_decode_result);
    private_ht_standard_disjoint(context);
    part2_tile_metadata_frames(context.parts,crate::codestream::image_size_component_count(&context.size),context.discard,Ok(context.metadata));
    part2_decode_eta(|events|private_standard_image_run(context,events),result);
    part2_cold_bind(|events|part2_tile_metadata_run(context.parts,crate::codestream::image_size_component_count(&context.size),context.discard,events),
        |metadata:Part2TileDecodeMetadata,rest|part2_tile_after_metadata_run(&context.size,context.tile,context.parts,context.caps,context.discard,
            &context.limits,context.prepared,context.initial,context.work,metadata,rest),Ok(context.metadata),result);
}

}
