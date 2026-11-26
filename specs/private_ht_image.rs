use super::*;
verus! {

pub struct PrivateImageContext {
    pub size:crate::codestream::ImageSize,pub tile:u16,pub parts:Seq<Part2OwnedTilePart>,
    pub caps:Option<(u32,Seq<u16>)>,pub discard:Option<u8>,pub limits:crate::ResourceLimits,
    pub prepared:Seq<Part1AssemblyTile>,pub initial:(u64,u64,u64),pub work:u64,
    pub metadata:Part2TileDecodeMetadata,
}

pub(crate) open spec fn private_image_admitted(context:PrivateImageContext)->bool {
    private_ht_eligible(&context.size,context.tile,context.parts,context.caps,context.discard)
        && part2_tile_decode_metadata_owned(context.parts,crate::codestream::image_size_component_count(&context.size),
            context.discard)==Ok(context.metadata)
}

pub(crate) open spec fn private_image_selection(context:PrivateImageContext)->Option<Seq<u8>> {
    match context.discard{None=>None,Some(_)=>Some(context.metadata.resolution_counts)}
}

pub(crate) open spec fn private_packet_value_run(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:PrivateHtPrecinctState,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtPrecinctState> {
    match private_packet_decode_run(parts,grid,before,selection,limits,events){
        None=>None,Some(((Err(error),_),rest))=>Some((Err(error),rest)),
        Some(((Ok(_),after),rest))=>Some((Ok(after),rest)),
    }
}

pub(crate) open spec fn private_component_calls_run(context:PrivateReconstructionContext,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<Part1AssemblyTile> {
    if events.len()==0{None}else{match events[0]{
        Part2JpipSnapshotEvent::PrivateComponentPlaneCalls{context:actual,calls}=>{
            if actual!=context{None}else{match private_component_run(context,calls){
                Some((result,rest))=>if rest.len()==0{Some((result,events.drop_first()))}else{None},
                None=>None,
            }}
        },
        _=>None,
    }}
}

pub(crate) open spec fn private_image_reconstruction(context:PrivateImageContext,plan:PrivateHtPlanState,
    precinct:PrivateHtPrecinctState,style:Part1PrepareStyle)->PrivateReconstructionContext {
    PrivateReconstructionContext {
        plan:plan.component,precinct:seq![precinct],style,maximum:crate::limits::resource_decoded_bytes_limit(&context.limits),
    }
}

pub(crate) open spec fn private_image_finish(context:PrivateImageContext,counters:(u64,u64,u64),value:Part1AssemblyTile)
    ->Result<Part2DecodedLayoutTile,crate::DecodeError> {
    let finished=part2_finish_prepared_tile(seq![value],crate::codestream::image_size_component_count(&context.size),
        crate::codestream::image_size_component_infos(&context.size),None,context.metadata.standard,context.work,
        crate::limits::resource_work_limit(&context.limits),crate::limits::resource_decoded_bytes_limit(&context.limits));
    match finished.0{Err(error)=>Err(error),Ok(())=>Ok(Part2DecodedLayoutTile {
        prepared:context.prepared+finished.1,counters,mct_work:finished.2,
    })}
}

pub(crate) open spec fn private_image_after_component(context:PrivateImageContext,counters:(u64,u64,u64),value:Part1AssemblyTile,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2DecodedLayoutTile> {
    part2_jpip_snapshot_bind(private_owner_capacity_run(PrivateOwnerCapacityContext::PreparedAppend {
        source:context.prepared,next:value,
    },events),|_:(),rest|Some((private_image_finish(context,counters,value),rest)))
}

pub(crate) open spec fn private_image_after_packets(context:PrivateImageContext,plan:PrivateHtPlanState,
    counters:(u64,u64,u64),precinct:PrivateHtPrecinctState,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2DecodedLayoutTile> {
    match crate::codestream::component_coding_style_result(&context.metadata.first.component_coding_styles,0){
        Err(error)=>Some((Err(error),events)),
        Ok(style)=>part2_jpip_snapshot_bind(private_component_calls_run(
            private_image_reconstruction(context,plan,precinct,crate::decode::prepare_style_view(style)),events),
            |value:Part1AssemblyTile,rest|private_image_after_component(context,counters,value,rest)),
    }
}

pub(crate) open spec fn private_image_after_plan(context:PrivateImageContext,plan:PrivateHtPlanState,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2DecodedLayoutTile> {
    match part2_planned_tile_accounting(private_plan_public_view(plan,context.tile,context.metadata.first),
        private_image_selection(context),context.initial,&context.limits){
        Err(error)=>Some((Err(error),events)),
        Ok(counters)=>part2_jpip_snapshot_bind(private_packet_value_run(context.parts,plan.grid,plan.precinct,
            private_image_selection(context),&context.limits,events),
            |precinct:PrivateHtPrecinctState,rest|private_image_after_packets(context,plan,counters,precinct,rest)),
    }
}

pub(crate) open spec fn private_image_run(context:PrivateImageContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2DecodedLayoutTile> {
    part2_jpip_snapshot_bind(private_plan_run(&context.size,context.tile,context.metadata.first,context.caps,&context.limits,events),
        |plan:PrivateHtPlanState,rest|private_image_after_plan(context,plan,rest))
}

pub(crate) open spec fn private_image_result(context:PrivateImageContext,result:Result<Part2DecodedLayoutTile,crate::DecodeError>)->bool {
    part2_cold_framed(|events|private_image_run(context,events),result)
}

pub(crate) open spec fn private_image_value(context:PrivateImageContext)->Result<Part2DecodedLayoutTile,crate::DecodeError> {
    match private_plan_value(&context.size,context.tile,context.metadata.first,context.caps,&context.limits){
        Err(error)=>Err(error),Ok(plan)=>private_image_after_plan_value(context,plan),
    }
}

pub(crate) open spec fn private_image_after_plan_result(context:PrivateImageContext,plan:PrivateHtPlanState,
    result:Result<Part2DecodedLayoutTile,crate::DecodeError>)->bool {
    part2_cold_framed(|events|private_image_after_plan(context,plan,events),result)
}

pub(crate) open spec fn private_image_after_plan_value(context:PrivateImageContext,plan:PrivateHtPlanState)->Result<Part2DecodedLayoutTile,crate::DecodeError> {
    match part2_planned_tile_accounting(
            private_plan_public_view(plan,context.tile,context.metadata.first),private_image_selection(context),context.initial,&context.limits){
            Err(error)=>Err(error),Ok(counters)=>{
                let packets=private_packet_decode_value(context.parts,plan.grid,plan.precinct,private_image_selection(context),&context.limits);
                match packets.0{
                    Err(error)=>Err(error),Ok(_)=>match crate::codestream::component_coding_style_result(&context.metadata.first.component_coding_styles,0){
                        Err(error)=>Err(error),Ok(style)=>match part2_prepare_component(plan.component,private_ht_precinct_planes(seq![packets.1]),
                            crate::decode::prepare_style_view(style),None,crate::limits::resource_decoded_bytes_limit(&context.limits)){
                            Err(error)=>Err(error),Ok(value)=>private_image_finish(context,counters,value),
                        },
                    },
                }
            },
        }
}

    pub(crate) proof fn private_packet_value_observed(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
        before:PrivateHtPrecinctState,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,result:PrivatePacketDecodeEffect)
        requires private_packet_decode_result(parts,grid,before,selection,limits,result),
        ensures part2_cold_framed(|events|private_packet_value_run(parts,grid,before,selection,limits,events),
            match result.0{Err(error)=>Err(error),Ok(_)=>Ok(result.1)}),
    {
        let prefix=choose|prefix| #[trigger] private_packet_decode_prefix(parts,grid,before,selection,limits,prefix,result);
        let output=match result.0{Err(error)=>Err(error),Ok(_)=>Ok(result.1)};
        assert forall|tail|private_packet_value_run(parts,grid,before,selection,limits,prefix+tail)==Some((output,tail)) by {}
        assert(part2_cold_prefix(|events|private_packet_value_run(parts,grid,before,selection,limits,events),prefix,output));
    }

    pub(crate) proof fn private_component_calls_observed(context:PrivateReconstructionContext,result:Result<Part1AssemblyTile,crate::DecodeError>)
        requires private_component_result(context,result),
        ensures part2_cold_framed(|events|private_component_calls_run(context,events),result),
    {
        let run=|tail|private_component_run(context,tail);
        let calls=choose|calls| #[trigger] part2_tier1_storage_prefix(run,calls,result);
        part2_tier1_storage_at(run,calls,result,Seq::empty());
        let prefix=seq![Part2JpipSnapshotEvent::PrivateComponentPlaneCalls{context,calls}];
        assert forall|tail|private_component_calls_run(context,prefix+tail)==Some((result,tail)) by {
            assert((prefix+tail).drop_first() =~= tail);
        }
        assert(part2_cold_prefix(|events|private_component_calls_run(context,events),prefix,result));
    }

    pub(crate) proof fn private_image_inactive_finish(before:Seq<Part1AssemblyTile>,components:u16,
        infos:Seq<crate::codestream::ComponentInfo>,standard:(bool,bool),work:u64,maximum_work:u64,maximum_bytes:u64,result:Part2ExtractionTileEffect)
        requires !standard.0,part2_mct_line_finish_result(before,components,infos,None,standard,work,maximum_work,maximum_bytes,result),
        ensures result==(Ok(()),before,work),
    {
        let run=|tail|part2_mct_line_finish_run(before,components,infos,None,standard,work,maximum_work,maximum_bytes,tail);
        let calls=choose|calls| #[trigger] part2_tier1_storage_prefix(run,calls,Ok(result));
        part2_tier1_storage_at(run,calls,Ok(result),Seq::empty());
    }

    pub(crate) proof fn private_image_normal(context:PrivateImageContext)
        requires private_image_admitted(context),
        ensures private_image_result(context,private_image_value(context)),
    {
        let result=private_image_value(context);
        private_ht_selected_metadata(&context.size,context.tile,context.parts,context.caps,context.discard,context.metadata);
        let planned=private_plan_value(&context.size,context.tile,context.metadata.first,context.caps,&context.limits);
        private_plan_normal(&context.size,context.tile,context.metadata.first,context.caps,&context.limits);
        if let Ok(plan)=planned{
            private_plan_value_fields(&context.size,context.tile,context.metadata.first,context.caps,&context.limits,plan);
            let accounting=part2_planned_tile_accounting(private_plan_public_view(plan,context.tile,context.metadata.first),
                private_image_selection(context),context.initial,&context.limits);
            match accounting{
                Err(_)=>{part2_cold_pure(result);},
                Ok(counters)=>{
                    let packets=private_packet_decode_value(context.parts,plan.grid,plan.precinct,private_image_selection(context),&context.limits);
                    private_packet_decode_normal(context.parts,plan.grid,plan.precinct,private_image_selection(context),&context.limits);
                    private_packet_value_observed(context.parts,plan.grid,plan.precinct,private_image_selection(context),&context.limits,packets);
                    if packets.0.is_ok(){
                        match crate::codestream::component_coding_style_result(&context.metadata.first.component_coding_styles,0){
                            Err(_)=>{part2_cold_pure(result);},
                            Ok(style)=>{
                                let reconstruction=private_image_reconstruction(context,plan,packets.1,crate::decode::prepare_style_view(style));
                                let component=part2_prepare_component(plan.component,private_ht_precinct_planes(seq![packets.1]),
                                    reconstruction.style,None,reconstruction.maximum);
                                private_component_normal(reconstruction);
                                private_component_calls_observed(reconstruction,component);
                                if let Ok(value)=component{
                                    let capacity=PrivateOwnerCapacityContext::PreparedAppend{source:context.prepared,next:value};
                                    private_owner_capacity_observed(capacity,Ok(()));
                                    part2_cold_pure(result);
                                    part2_cold_bind(|events|private_owner_capacity_run(capacity,events),
                                        |_:(),rest|Some((private_image_finish(context,counters,value),rest)),Ok(()),result);
                                    part2_decode_eta(|events|private_image_after_component(context,counters,value,events),result);
                                }
                                part2_cold_bind(|events|private_component_calls_run(reconstruction,events),
                                    |value,rest|private_image_after_component(context,counters,value,rest),component,result);
                            },
                        }
                        part2_decode_eta(|events|private_image_after_packets(context,plan,counters,packets.1,events),result);
                    }
                    part2_cold_bind(|events|private_packet_value_run(context.parts,plan.grid,plan.precinct,private_image_selection(context),&context.limits,events),
                        |precinct,rest|private_image_after_packets(context,plan,counters,precinct,rest),
                        match packets.0{Err(error)=>Err(error),Ok(_)=>Ok(packets.1)},result);
                },
            }
            part2_decode_eta(|events|private_image_after_plan(context,plan,events),result);
        }
        part2_cold_bind(|events|private_plan_run(&context.size,context.tile,context.metadata.first,context.caps,&context.limits,events),
            |plan,rest|private_image_after_plan(context,plan,rest),planned,result);
    }

    pub(crate) proof fn private_image_reference(context:PrivateImageContext)
        requires private_image_admitted(context),
        ensures private_image_value(context)==part2_decode_tile_parts_owned(&context.size,context.tile,context.parts,context.caps,
            context.discard,&context.limits,context.prepared,context.initial,context.work),
    {
        private_ht_selected_metadata(&context.size,context.tile,context.parts,context.caps,context.discard,context.metadata);
        private_plan_reference(&context.size,context.tile,context.metadata.first,context.caps,&context.limits);
        reveal_with_fuel(part2_reconstruct_components_prefix,2);
        if let Ok(plan)=private_plan_value(&context.size,context.tile,context.metadata.first,context.caps,&context.limits){
            private_plan_value_fields(&context.size,context.tile,context.metadata.first,context.caps,&context.limits,plan);
            private_packet_decode_value_fields(context.parts,plan.grid,plan.precinct,private_image_selection(context),&context.limits);
            let packets=private_packet_decode_value(context.parts,plan.grid,plan.precinct,private_image_selection(context),&context.limits);
            assert(part2_precinct_decoder_planes(seq![packets.1.logical]) =~= private_ht_precinct_planes(seq![packets.1]));
            if packets.0.is_ok(){
                if let Ok(style)=crate::codestream::component_coding_style_result(&context.metadata.first.component_coding_styles,0){
                    if let Ok(value)=part2_prepare_component(plan.component,private_ht_precinct_planes(seq![packets.1]),
                        crate::decode::prepare_style_view(style),None,crate::limits::resource_decoded_bytes_limit(&context.limits)){
                        assert(context.prepared.push(value).skip(context.prepared.len() as int) =~= seq![value]);
                        assert(context.prepared.push(value) =~= context.prepared+seq![value]);
                    }
                }
            }
        }
    }

    pub(crate) proof fn private_image_tile_observed(context:PrivateImageContext,result:Result<Part2DecodedLayoutTile,crate::DecodeError>)
        requires private_image_admitted(context),
            part2_tile_metadata_result(context.parts,crate::codestream::image_size_component_count(&context.size),context.discard,Ok(context.metadata)),
            private_image_result(context,result),
        ensures part2_tile_decode_result(&context.size,context.tile,context.parts,context.caps,context.discard,&context.limits,
            context.prepared,context.initial,context.work,result),
    {
        reveal(part2_tile_decode_result);
        part2_tile_metadata_frames(context.parts,crate::codestream::image_size_component_count(&context.size),context.discard,Ok(context.metadata));
        part2_decode_eta(|events|private_image_run(context,events),result);
        part2_cold_bind(
            |events|part2_tile_metadata_run(context.parts,crate::codestream::image_size_component_count(&context.size),context.discard,events),
            |metadata:Part2TileDecodeMetadata,rest|part2_tile_after_metadata_run(&context.size,context.tile,context.parts,context.caps,context.discard,
                &context.limits,context.prepared,context.initial,context.work,metadata,rest),Ok(context.metadata),result);
    }
}
