use super::*;
verus! {

pub struct PrivateHtInitialContext {
    pub width:u16,
    pub height:u16,
    pub bitplanes:u16,
    pub orientation:crate::tier1::SubbandOrientation,
    pub style:crate::tier1::Tier1CodingStyle,
    pub allowed:bool,
    pub bound:u8,
}

pub(crate) open spec fn private_ht_initial_supported(ctx:PrivateHtInitialContext)->bool {
    matches!(ctx.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput)
        && ctx.style.force_high_throughput && 1<=ctx.bitplanes<=crate::tier1::MAX_TIER1_BITPLANES
        && 1<=ctx.bound<=crate::tier1::tier1_max_ht_magnitude_bits()
}

pub(crate) open spec fn private_ht_initial_state(ctx:PrivateHtInitialContext,plane:Tier1RawPlane)->PrivateHtDecoderState {
    PrivateHtDecoderState {packed:true,logical:Tier1DecoderState {
        plane,private_plan:true,orientation:ctx.orientation,style:ctx.style,
        maximum_passes:(3*(ctx.bitplanes as nat)-2) as u32,next_pass:0,
        bitplane:(ctx.bitplanes as int-1) as u16,zero_bitplanes:None,
        bitplane_state:None,mq_context_state:None,reset_contexts_before_mq:false,
        decoded_segments:0,decoded_bytes:0,legacy_segment:None,legacy_decode_work:0,
        ht_cleanup_plane:None,ht_refinement_data:Seq::empty(),ht_refinement_passes:0,
        ht_decoded_bitplanes:0,ht_current_set_has_cleanup:false,ht_sets_seen:0,
        allow_multiple_ht_sets:ctx.allowed,ht_magnitude_bound:ctx.bound,
    }}
}

pub(crate) open spec fn private_ht_initial_value(ctx:PrivateHtInitialContext)->Result<PrivateHtDecoderState,crate::DecodeError> {
    if !private_ht_initial_supported(ctx){Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
    else{match tier1_empty_plane(ctx.width,ctx.height){
        Err(error)=>Err(error),Ok(plane)=>Ok(private_ht_initial_state(ctx,plane)),
    }}
}

pub(crate) open spec fn private_ht_initial_run(ctx:PrivateHtInitialContext,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<PrivateHtDecoderState> {
    if !private_ht_initial_supported(ctx){Some((Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),calls))}
    else{part2_tier1_storage_bind(private_primary_initial_run(ctx.width,ctx.height,calls),
        |primary:PrivatePrimaryValue,rest|Some((Ok(private_ht_initial_state(ctx,primary.0)),rest)))}
}

pub(crate) open spec fn private_ht_initial_result(ctx:PrivateHtInitialContext,result:Result<PrivateHtDecoderState,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|private_ht_initial_run(ctx,calls),result)
}

pub(crate) proof fn private_ht_initial_normal(ctx:PrivateHtInitialContext)
    ensures private_ht_initial_result(ctx,private_ht_initial_value(ctx)),
{
    if !private_ht_initial_supported(ctx){part2_tier1_storage_pure(private_ht_initial_value(ctx));}
    else{
        private_primary_initial_normal(ctx.width,ctx.height);
        private_ht_initial_observed(ctx,match tier1_empty_plane(ctx.width,ctx.height){
            Err(error)=>Err(error),Ok(plane)=>Ok((plane,true)),
        });
    }
}

pub(crate) proof fn private_ht_initial_fields(ctx:PrivateHtInitialContext,state:PrivateHtDecoderState)
    requires private_ht_initial_value(ctx)==Ok(state),
    ensures private_ht_state_wf(state),
{
    let plane=tier1_empty_plane(ctx.width,ctx.height).get_Ok_0();
    private_primary_empty_shape(ctx.width,ctx.height,plane);
}

pub(crate) proof fn private_ht_initial_equivalent(ctx:PrivateHtInitialContext)
    requires matches!(ctx.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput),ctx.style.force_high_throughput,
    ensures match private_ht_initial_value(ctx){
        Err(error)=>Err(error),Ok(value)=>Ok(value.logical),
    }==part2_configured_checkpoint(ctx.width,ctx.height,ctx.bitplanes,
        ctx.orientation,ctx.style,ctx.allowed,ctx.bound,true),
{
    reveal(part2_tier1_initial_decoder);
    reveal(part2_tier1_configured_decoder);reveal(part2_configured_checkpoint);reveal(part2_with_ht_checkpoint);
    assert((ctx.width as int)*(ctx.height as int)<=usize::MAX) by(nonlinear_arith)
        requires ctx.width<=65535,ctx.height<=65535;
    if private_ht_initial_supported(ctx){
        if let Ok(plane)=tier1_empty_plane(ctx.width,ctx.height){
            assert((3*(ctx.bitplanes as nat)-2) as u32==((ctx.bitplanes as int)*3-2) as u32);
        }
    }else{
        assert(ctx.bitplanes==0 || ctx.bitplanes>crate::tier1::MAX_TIER1_BITPLANES
            || ctx.bound==0 || ctx.bound>crate::tier1::tier1_max_ht_magnitude_bits());
    }
}

pub(crate) proof fn private_ht_initial_observed(ctx:PrivateHtInitialContext,result:Result<PrivatePrimaryValue,crate::DecodeError>)
    requires private_ht_initial_supported(ctx),private_primary_initial_result(ctx.width,ctx.height,result),
    ensures private_ht_initial_result(ctx,match result{Err(error)=>Err(error),Ok(value)=>Ok(private_ht_initial_state(ctx,value.0))}),
{
    let outcome=match result{Err(error)=>Err(error),Ok(value)=>Ok(private_ht_initial_state(ctx,value.0))};
    if let Ok(value)=result {part2_tier1_storage_pure(Ok(private_ht_initial_state(ctx,value.0)));}
    part2_tier1_storage_bind_frame(|calls|private_primary_initial_run(ctx.width,ctx.height,calls),
        |primary:PrivatePrimaryValue,rest|Some((Ok(private_ht_initial_state(ctx,primary.0)),rest)),result,outcome);
}

pub(crate) open spec fn private_ht_metadata_frame(before:Tier1DecoderState,after:Tier1DecoderState)->bool {
    after.private_plan==before.private_plan && after.orientation==before.orientation
        && after.style==before.style && after.bitplane_state==before.bitplane_state
        && after.mq_context_state==before.mq_context_state
        && after.reset_contexts_before_mq==before.reset_contexts_before_mq
        && after.legacy_segment==before.legacy_segment
        && after.legacy_decode_work==before.legacy_decode_work
}

pub(crate) proof fn private_ht_coefficient_metadata(before:Tier1DecoderState,segments:HtBlockSegmentsState,
    passes:u32,maximum_u:u8,skipped:u16,work:u64)
    ensures private_ht_metadata_frame(before,ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work).1),
{
    reveal(ht_store_coefficient_symbols);
}

pub(crate) proof fn private_ht_after_parse_metadata(before:Tier1DecoderState,segments:HtBlockSegmentsState,
    passes:u32,refinements:u8,bytes:u64,work:u64)
    ensures private_ht_metadata_frame(before,ht_segments_after_parse(before,segments,passes,refinements,bytes,work).1),
{
    let skipped=before.next_pass/3;
    let missing=match before.zero_bitplanes{None=>0nat,Some(value)=>value as nat};
    private_ht_coefficient_metadata(before,segments,passes,
        part15_cleanup_u_bound(missing,skipped as nat,before.ht_magnitude_bound as nat) as u8,
        skipped as u16,work);
}

pub(crate) proof fn private_ht_cleanup_metadata(before:Tier1DecoderState,body:Seq<u8>,cleanup:u8,
    refinement:Option<Seq<u8>>,refinements:u8,passes:u32,bytes:u64,work:u64)
    ensures private_ht_metadata_frame(before,ht_decode_segments(before,body,cleanup,refinement,refinements,passes,bytes,work).1),
{
    if let Ok(segments)=ht_parse_block_segments(body,refinement,bytes) {
        private_ht_after_parse_metadata(before,segments,(cleanup as nat+refinements as nat) as u32,refinements,bytes,work);
    }
}

pub(crate) proof fn private_ht_route_metadata(before:Tier1DecoderState,body:Seq<u8>,passes:u8,
    maximum_passes:u32,bytes:u64,work:u64)
    ensures private_ht_metadata_frame(before,ht_packet_segment_route(before,body,passes,maximum_passes,bytes,work).1),
{
    reveal(ht_decode_refinement_contribution);
    reveal(ht_finish_refinement_contribution);
    private_ht_cleanup_metadata(before,body,1,None,0,maximum_passes,bytes,work);
}

pub(crate) proof fn private_ht_segment_metadata(before:Tier1DecoderState,segment:crate::packet::CodeBlockSegmentContribution,
    body:Seq<u8>,offset:usize,decoded:u32,passes:u32,bytes:u64,work:u64)
    ensures private_ht_metadata_frame(before,ht_packet_segment_body(before,segment,body,offset,decoded,passes,bytes,work).1),
{
    let end=offset as nat+segment.data_length as nat;
    if offset<=end && end<=body.len() {
        private_ht_route_metadata(before,body.subrange(offset as int,end as int),segment.passes,passes,bytes,work);
    }
}

pub(crate) proof fn private_ht_body_metadata(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,
    progress:HtPacketBodyProgress,passes:u32,bytes:u64,work:u64)
    ensures private_ht_metadata_frame(before,ht_packet_body_run(before,header,body,progress,passes,bytes,work).1),
    decreases header.segment_count as nat-progress.segment_index as nat,
{
    reveal_with_fuel(ht_packet_body_run,1);
    if progress.segment_index<header.segment_count {
        if let Ok(segment)=part1_code_block_segment(header,progress.segment_index) {
            private_ht_segment_metadata(before,segment,body,progress.offset,progress.decoded_passes,passes,bytes,work);
            let step=ht_packet_segment_body(before,segment,body,progress.offset,progress.decoded_passes,passes,bytes,work);
            if step.0.is_ok() && progress.segment_index<u8::MAX {
                private_ht_body_metadata(step.1,header,body,HtPacketBodyProgress {
                    segment_index:(progress.segment_index+1) as u8,offset:step.2,decoded_passes:step.3,
                },passes,bytes,work);
            }
        }
    }
}

pub(crate) proof fn private_ht_staged_metadata(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,
    passes:u32,bytes:u64,input:u64,work:u64)
    requires private_ht_metadata_supported(before),
    ensures private_ht_metadata_supported(part1_code_block_body_staged(before,header,body,passes,bytes,input,work).1),
{
    let prepared=part1_code_block_body_prepare(before,header,body);
    if prepared.0.is_ok() {
        assert(header.high_throughput);
        private_ht_body_metadata(prepared.1,header,body,HtPacketBodyProgress {
            segment_index:0,offset:0,decoded_passes:0,
        },passes,bytes,work);
    }
}

pub(crate) open spec fn private_ht_state_wf(state:PrivateHtDecoderState)->bool {
    private_ht_metadata_supported(state.logical) && private_primary_shape(state.logical.plane,state.packed)
}

pub(crate) open spec fn private_ht_stage_after_primary(before:PrivateHtDecoderState,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<PrivateHtDecoderState> {
    let role=crate::tier1::HtRefinementCopyRole::PacketStaging;
    part2_tier1_storage_bind(part2_decoder_cleanup_run(before.logical.ht_cleanup_plane,role,calls),
        |_:Option<Tier1RawPlane>,rest|part2_tier1_storage_bind(part2_ht_bytes_run(before.logical.ht_refinement_data,role,rest),
            |_:Seq<u8>,tail|Some((Ok(before),tail))))
}

pub(crate) open spec fn private_ht_stage_run(before:PrivateHtDecoderState,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<PrivateHtDecoderState> {
    part2_tier1_storage_bind(private_primary_copy_run((before.logical.plane,before.packed),calls),
        |_:PrivatePrimaryValue,rest|private_ht_stage_after_primary(before,rest))
}

pub(crate) open spec fn private_ht_stage_result(before:PrivateHtDecoderState,result:Result<PrivateHtDecoderState,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|private_ht_stage_run(before,calls),result)
}

pub(crate) proof fn private_ht_stage_primary_error(before:PrivateHtDecoderState,error:crate::DecodeError)
    requires private_primary_copy_result((before.logical.plane,before.packed),Err(error)),
    ensures private_ht_stage_result(before,Err(error)),
{
    part2_tier1_storage_bind_frame(|calls|private_primary_copy_run((before.logical.plane,before.packed),calls),
        |_:PrivatePrimaryValue,rest|private_ht_stage_after_primary(before,rest),Err(error),Err(error));
}

pub(crate) proof fn private_ht_stage_after_primary_observed(before:PrivateHtDecoderState,result:Result<PrivateHtDecoderState,crate::DecodeError>)
    requires private_primary_copy_result((before.logical.plane,before.packed),Ok((before.logical.plane,before.packed))),
        part2_tier1_storage_framed(|calls|private_ht_stage_after_primary(before,calls),result),
    ensures private_ht_stage_result(before,result),
{
    part2_tier1_storage_eta(|calls|private_ht_stage_after_primary(before,calls),result);
    part2_tier1_storage_bind_frame(|calls|private_primary_copy_run((before.logical.plane,before.packed),calls),
        |_:PrivatePrimaryValue,rest|private_ht_stage_after_primary(before,rest),Ok((before.logical.plane,before.packed)),result);
}

pub(crate) proof fn private_ht_stage_cleanup_error(before:PrivateHtDecoderState,error:crate::DecodeError)
    requires private_primary_copy_result((before.logical.plane,before.packed),Ok((before.logical.plane,before.packed))),
        part2_decoder_cleanup_result(before.logical.ht_cleanup_plane,crate::tier1::HtRefinementCopyRole::PacketStaging,Err(error)),
    ensures private_ht_stage_result(before,Err(error)),
{
    let role=crate::tier1::HtRefinementCopyRole::PacketStaging;
    part2_decoder_cleanup_frames(before.logical.ht_cleanup_plane,role,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_decoder_cleanup_run(before.logical.ht_cleanup_plane,role,calls),
        |_:Option<Tier1RawPlane>,rest|part2_tier1_storage_bind(part2_ht_bytes_run(before.logical.ht_refinement_data,role,rest),
            |_:Seq<u8>,tail|Some((Ok(before),tail))),Err(error),Err(error));
    private_ht_stage_after_primary_observed(before,Err(error));
}

pub(crate) proof fn private_ht_stage_bytes_observed(before:PrivateHtDecoderState,result:Result<Seq<u8>,crate::DecodeError>)
    requires private_primary_copy_result((before.logical.plane,before.packed),Ok((before.logical.plane,before.packed))),
        part2_decoder_cleanup_result(before.logical.ht_cleanup_plane,crate::tier1::HtRefinementCopyRole::PacketStaging,Ok(before.logical.ht_cleanup_plane)),
        part2_ht_bytes_result(before.logical.ht_refinement_data,crate::tier1::HtRefinementCopyRole::PacketStaging,result),
    ensures private_ht_stage_result(before,match result{Err(error)=>Err(error),Ok(_)=>Ok(before)}),
{
    let role=crate::tier1::HtRefinementCopyRole::PacketStaging;
    let outcome=match result{Err(error)=>Err(error),Ok(_)=>Ok(before)};
    part2_ht_bytes_frames(before.logical.ht_refinement_data,role,result);
    if result.is_ok(){part2_tier1_storage_pure(Ok(before));}
    part2_tier1_storage_bind_frame(|calls|part2_ht_bytes_run(before.logical.ht_refinement_data,role,calls),
        |_:Seq<u8>,rest|Some((Ok(before),rest)),result,outcome);
    part2_decoder_cleanup_frames(before.logical.ht_cleanup_plane,role,Ok(before.logical.ht_cleanup_plane));
    part2_tier1_storage_bind_frame(|calls|part2_decoder_cleanup_run(before.logical.ht_cleanup_plane,role,calls),
        |_:Option<Tier1RawPlane>,rest|part2_tier1_storage_bind(part2_ht_bytes_run(before.logical.ht_refinement_data,role,rest),
            |_:Seq<u8>,tail|Some((Ok(before),tail))),Ok(before.logical.ht_cleanup_plane),outcome);
    private_ht_stage_after_primary_observed(before,outcome);
}

pub(crate) proof fn private_ht_stage_normal(before:PrivateHtDecoderState)
    ensures private_ht_stage_result(before,Ok(before)),
{
    private_primary_copy_normal((before.logical.plane,before.packed));
    part2_decoder_cleanup_normal(before.logical.ht_cleanup_plane,crate::tier1::HtRefinementCopyRole::PacketStaging);
    part2_ht_bytes_normal(before.logical.ht_refinement_data,crate::tier1::HtRefinementCopyRole::PacketStaging);
    private_ht_stage_bytes_observed(before,Ok(before.logical.ht_refinement_data));
}

pub(crate) open spec fn private_ht_into_wide_run(before:PrivateHtDecoderState,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<Tier1DecoderState> {
    part2_tier1_storage_bind(private_primary_materialize_run((before.logical.plane,before.packed),calls),
        |_:Tier1RawPlane,rest|Some((Ok(before.logical),rest)))
}

pub(crate) open spec fn private_ht_into_wide_result(before:PrivateHtDecoderState,result:Result<Tier1DecoderState,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|private_ht_into_wide_run(before,calls),result)
}

pub(crate) proof fn private_ht_into_wide_observed(before:PrivateHtDecoderState,result:Result<Tier1RawPlane,crate::DecodeError>)
    requires private_primary_materialize_result((before.logical.plane,before.packed),result),
        match result{Ok(plane)=>plane==before.logical.plane,Err(_)=>true},
    ensures private_ht_into_wide_result(before,match result{Err(error)=>Err(error),Ok(_)=>Ok(before.logical)}),
{
    let outcome=match result{Err(error)=>Err(error),Ok(_)=>Ok(before.logical)};
    if result.is_ok(){part2_tier1_storage_pure(Ok(before.logical));}
    part2_tier1_storage_bind_frame(|calls|private_primary_materialize_run((before.logical.plane,before.packed),calls),
        |_:Tier1RawPlane,rest|Some((Ok(before.logical),rest)),result,outcome);
}

pub(crate) open spec fn private_ht_from_wide_run(before:Tier1DecoderState,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<PrivateHtDecoderState> {
    if !private_ht_metadata_supported(before){Some((Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),calls))}
    else{part2_tier1_storage_bind(private_primary_retention_run(before.plane,calls),
        |retained:PrivatePrimaryValue,rest|Some((Ok(PrivateHtDecoderState{logical:before,packed:retained.1}),rest)))}
}

pub(crate) open spec fn private_ht_from_wide_result(before:Tier1DecoderState,result:Result<PrivateHtDecoderState,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|private_ht_from_wide_run(before,calls),result)
}

pub(crate) proof fn private_ht_from_wide_observed(before:Tier1DecoderState,result:Result<PrivatePrimaryValue,crate::DecodeError>)
    requires private_ht_metadata_supported(before),private_primary_retention_result(before.plane,result),
    ensures private_ht_from_wide_result(before,match result{Err(error)=>Err(error),
        Ok(value)=>Ok(PrivateHtDecoderState{logical:before,packed:value.1})}),
{
    let outcome=match result{Err(error)=>Err(error),Ok(value)=>Ok(PrivateHtDecoderState{logical:before,packed:value.1})};
    if let Ok(value)=result {part2_tier1_storage_pure(Ok(PrivateHtDecoderState{logical:before,packed:value.1}));}
    part2_tier1_storage_bind_frame(|calls|private_primary_retention_run(before.plane,calls),
        |value:PrivatePrimaryValue,rest|Some((Ok(PrivateHtDecoderState{logical:before,packed:value.1}),rest)),result,outcome);
}

pub type PrivateHtBodyEffect=(Result<crate::packet::CodeBlockBodyDecode,crate::DecodeError>,PrivateHtDecoderState);

pub(crate) open spec fn private_ht_body_value(before:PrivateHtDecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,
    passes:u32,bytes:u64,input:u64,work:u64)->PrivateHtBodyEffect {
    let converted=if before.packed{tier1_duplicate_plane(before.logical.plane)}else{Ok(before.logical.plane)};
    match converted{
        Err(error)=>(Err(error),before),
        Ok(_)=>{
            let kernel=part1_code_block_body_staged(before.logical,header,body,passes,bytes,input,work);
            match kernel.0{
                Err(error)=>(Err(error),before),
                Ok(decoded)=>if !private_ht_metadata_supported(kernel.1){
                    (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before)
                }else{(Ok(decoded),PrivateHtDecoderState{
                    logical:kernel.1,packed:private_primary_selected(kernel.1.plane),
                })},
            }
        },
    }
}

pub(crate) proof fn private_ht_body_value_fields(before:PrivateHtDecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,
    passes:u32,bytes:u64,input:u64,work:u64)
    requires private_ht_state_wf(before),
    ensures private_ht_state_wf(private_ht_body_value(before,header,body,passes,bytes,input,work).1),
        (private_ht_body_value(before,header,body,passes,bytes,input,work).0,
            private_ht_body_value(before,header,body,passes,bytes,input,work).1.logical)
            ==part1_code_block_body_transaction(before.logical,header,body,passes,bytes,input,work),
{
    if before.packed {private_primary_shape_duplicate(before.logical.plane);}
    private_ht_staged_metadata(before.logical,header,body,passes,bytes,input,work);
}

pub struct PrivateHtBodyContext {
    pub before:PrivateHtDecoderState,
    pub header:Part1CodeBlockContribution,
    pub body:Seq<u8>,
    pub passes:u32,
    pub bytes:u64,
    pub input:u64,
    pub work:u64,
}

pub(crate) open spec fn private_ht_body_after_kernel(before:PrivateHtDecoderState,kernel:HtCodeBlockBodyResult,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<PrivateHtBodyEffect> {
    match kernel.0 {
        Err(error)=>Some((Ok((Err(error),before)),calls)),
        Ok(decoded)=>part2_tier1_storage_resume(private_ht_from_wide_run(kernel.1,calls),
            |retained:Result<PrivateHtDecoderState,crate::DecodeError>,rest|Some((Ok(match retained{
                Err(error)=>(Err(error),before),Ok(after)=>(Ok(decoded),after),
            }),rest))),
    }
}

pub(crate) open spec fn private_ht_body_after_materialize(before:PrivateHtDecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<PrivateHtBodyEffect> {
    part2_tier1_storage_bind(part2_plane_body_staged_run(before.logical,header,body,pass_limit,byte_limit,input_limit,work,calls),
        |kernel:HtCodeBlockBodyResult,rest|private_ht_body_after_kernel(before,kernel,rest))
}

pub(crate) open spec fn private_ht_body_after_stage(before:PrivateHtDecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<PrivateHtBodyEffect> {
    part2_tier1_storage_resume(private_ht_into_wide_run(before,calls),
        |converted:Result<Tier1DecoderState,crate::DecodeError>,rest|match converted{
            Err(error)=>Some((Ok((Err(error),before)),rest)),
            Ok(_)=>private_ht_body_after_materialize(before,header,body,pass_limit,byte_limit,input_limit,work,rest),
        })
}

pub(crate) open spec fn private_ht_body_run(before:PrivateHtDecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<PrivateHtBodyEffect> {
    part2_tier1_storage_resume(private_ht_stage_run(before,calls),
        |staged:Result<PrivateHtDecoderState,crate::DecodeError>,rest|match staged{
            Err(error)=>Some((Ok((Err(error),before)),rest)),
            Ok(_)=>private_ht_body_after_stage(before,header,body,pass_limit,byte_limit,input_limit,work,rest),
        })
}

pub(crate) open spec fn private_ht_body_result(before:PrivateHtDecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,result:PrivateHtBodyEffect)->bool {
    part2_tier1_storage_framed(|calls|private_ht_body_run(before,header,body,pass_limit,byte_limit,input_limit,work,calls),Ok(result))
}

pub(crate) proof fn private_ht_body_stage_error(ctx:PrivateHtBodyContext,error:crate::DecodeError)
    requires private_ht_stage_result(ctx.before,Err(error)),
    ensures private_ht_body_result(ctx.before,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,(Err(error),ctx.before)),
{
    let b=ctx.before;
    let outcome=Ok((Err(error),b));
    part2_tier1_storage_pure(outcome);
    part2_tier1_resume_frame(|calls|private_ht_stage_run(b,calls),
        |staged:Result<PrivateHtDecoderState,crate::DecodeError>,rest|match staged{
            Err(error)=>Some((Ok((Err(error),b)),rest)),
            Ok(_)=>private_ht_body_after_stage(b,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,rest),
        },Err(error),outcome);
}

pub(crate) proof fn private_ht_body_after_stage_observed(ctx:PrivateHtBodyContext,effect:PrivateHtBodyEffect)
    requires private_ht_stage_result(ctx.before,Ok(ctx.before)),
        part2_tier1_storage_framed(|calls|private_ht_body_after_stage(ctx.before,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,calls),Ok(effect)),
    ensures private_ht_body_result(ctx.before,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,effect),
{
    let b=ctx.before;
    part2_tier1_storage_eta(|calls|private_ht_body_after_stage(b,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,calls),Ok(effect));
    part2_tier1_resume_frame(|calls|private_ht_stage_run(b,calls),
        |staged:Result<PrivateHtDecoderState,crate::DecodeError>,rest|match staged{
            Err(error)=>Some((Ok((Err(error),b)),rest)),
            Ok(_)=>private_ht_body_after_stage(b,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,rest),
        },Ok(b),Ok(effect));
}

pub(crate) proof fn private_ht_body_materialize_error(ctx:PrivateHtBodyContext,error:crate::DecodeError)
    requires private_ht_stage_result(ctx.before,Ok(ctx.before)),private_ht_into_wide_result(ctx.before,Err(error)),
    ensures private_ht_body_result(ctx.before,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,(Err(error),ctx.before)),
{
    let b=ctx.before;
    part2_tier1_storage_pure::<PrivateHtBodyEffect>(Ok((Err(error),b)));
    part2_tier1_resume_frame(|calls|private_ht_into_wide_run(b,calls),
        |converted:Result<Tier1DecoderState,crate::DecodeError>,rest|match converted{
            Err(error)=>Some((Ok((Err(error),b)),rest)),
            Ok(_)=>private_ht_body_after_materialize(b,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,rest),
        },Err(error),Ok((Err(error),b)));
    private_ht_body_after_stage_observed(ctx,(Err(error),b));
}

pub(crate) proof fn private_ht_body_kernel_observed(ctx:PrivateHtBodyContext,kernel:HtCodeBlockBodyResult,effect:PrivateHtBodyEffect)
    requires private_ht_stage_result(ctx.before,Ok(ctx.before)),private_ht_into_wide_result(ctx.before,Ok(ctx.before.logical)),
        part2_plane_body_staged_result(ctx.before.logical,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,kernel),
        part2_tier1_storage_framed(|calls|private_ht_body_after_kernel(ctx.before,kernel,calls),Ok(effect)),
    ensures private_ht_body_result(ctx.before,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,effect),
{
    let b=ctx.before;
    part2_tier1_storage_eta(|calls|private_ht_body_after_kernel(b,kernel,calls),Ok(effect));
    part2_tier1_storage_bind_frame(
        |calls|part2_plane_body_staged_run(b.logical,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,calls),
        |actual:HtCodeBlockBodyResult,rest|private_ht_body_after_kernel(b,actual,rest),Ok(kernel),Ok(effect));
    part2_tier1_resume_frame(|calls|private_ht_into_wide_run(b,calls),
        |converted:Result<Tier1DecoderState,crate::DecodeError>,rest|match converted{
            Err(error)=>Some((Ok((Err(error),b)),rest)),
            Ok(_)=>private_ht_body_after_materialize(b,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,rest),
        },Ok(b.logical),Ok(effect));
    private_ht_body_after_stage_observed(ctx,effect);
}

pub(crate) proof fn private_ht_body_kernel_error(ctx:PrivateHtBodyContext,kernel:HtCodeBlockBodyResult)
    requires private_ht_stage_result(ctx.before,Ok(ctx.before)),private_ht_into_wide_result(ctx.before,Ok(ctx.before.logical)),
        part2_plane_body_staged_result(ctx.before.logical,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,kernel),
        kernel.0.is_err(),
    ensures private_ht_body_result(ctx.before,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,(kernel.0,ctx.before)),
{
    part2_tier1_storage_pure(Ok((kernel.0,ctx.before)));
    private_ht_body_kernel_observed(ctx,kernel,(kernel.0,ctx.before));
}

pub(crate) proof fn private_ht_body_retained(ctx:PrivateHtBodyContext,kernel:HtCodeBlockBodyResult,retained:Result<PrivateHtDecoderState,crate::DecodeError>)
    requires private_ht_stage_result(ctx.before,Ok(ctx.before)),private_ht_into_wide_result(ctx.before,Ok(ctx.before.logical)),
        part2_plane_body_staged_result(ctx.before.logical,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,kernel),
        kernel.0.is_ok(),private_ht_from_wide_result(kernel.1,retained),
    ensures private_ht_body_result(ctx.before,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,
        match retained{Err(error)=>(Err(error),ctx.before),Ok(after)=>(kernel.0,after)}),
{
    let effect=match retained{Err(error)=>(Err(error),ctx.before),Ok(after)=>(kernel.0,after)};
    part2_tier1_storage_pure(Ok(effect));
    part2_tier1_resume_frame(|calls|private_ht_from_wide_run(kernel.1,calls),
        |actual:Result<PrivateHtDecoderState,crate::DecodeError>,rest|Some((Ok(match actual{
            Err(error)=>(Err(error),ctx.before),Ok(after)=>(kernel.0,after),
        }),rest)),retained,Ok(effect));
    private_ht_body_kernel_observed(ctx,kernel,effect);
}

pub(crate) proof fn private_ht_body_normal(ctx:PrivateHtBodyContext)
    requires private_ht_state_wf(ctx.before),
    ensures private_ht_body_result(ctx.before,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work,
        private_ht_body_value(ctx.before,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work)),
{
    let b=ctx.before;
    private_ht_stage_normal(b);
    if b.packed{
        private_primary_shape_duplicate(b.logical.plane);
        part2_plane_duplicate_normal(b.logical.plane,crate::tier1::CoefficientStorageRole::PrivatePrimaryOutput);
        private_primary_materialize_observed((b.logical.plane,true),Ok(b.logical.plane));
    }else{
        private_primary_materialize_observed((b.logical.plane,false),Ok(b.logical.plane));
    }
    private_ht_into_wide_observed(b,Ok(b.logical.plane));
    let kernel=part1_code_block_body_staged(b.logical,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work);
    part2_plane_body_staged_normal(b.logical,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work);
    if kernel.0.is_err(){private_ht_body_kernel_error(ctx,kernel);}else{
        private_ht_staged_metadata(b.logical,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work);
        private_primary_retention_normal(kernel.1.plane);
        let retained=(kernel.1.plane,private_primary_selected(kernel.1.plane));
        private_ht_from_wide_observed(kernel.1,Ok(retained));
        private_ht_body_retained(ctx,kernel,Ok(PrivateHtDecoderState{logical:kernel.1,packed:retained.1}));
    }
}
}
