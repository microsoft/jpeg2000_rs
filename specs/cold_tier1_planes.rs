//! The remaining shared coefficient-plane roles, with actual copy and entropy order.
use super::*;
verus! {
pub(crate) open spec fn part2_plane_duplicate_run(plane:Tier1RawPlane,role:crate::tier1::CoefficientStorageRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1RawPlane> {
    part2_tier1_storage_bind(part2_tier1_plane_run(plane.width,plane.height,role,calls),
        |_:Tier1RawPlane,rest|Some((tier1_duplicate_plane(plane),rest)))
}
pub closed spec fn part1_plane_duplicate_storage_result(plane:Tier1RawPlane,role:crate::tier1::CoefficientStorageRole,result:Result<Tier1RawPlane,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_duplicate_run(plane,role,calls),result)
}
pub(crate) proof fn part2_plane_duplicate_normal(plane:Tier1RawPlane,role:crate::tier1::CoefficientStorageRole)
    ensures part1_plane_duplicate_storage_result(plane,role,tier1_duplicate_plane(plane)),
{
    part2_tier1_plane_normal(plane.width,plane.height,role);
    let first=tier1_empty_plane(plane.width,plane.height);let result=tier1_duplicate_plane(plane);
    part2_tier1_plane_frames(plane.width,plane.height,role,first);
    if first.is_ok(){part2_tier1_storage_pure(result);}
    part2_tier1_storage_bind_frame(|calls|part2_tier1_plane_run(plane.width,plane.height,role,calls),|_:Tier1RawPlane,rest|Some((result,rest)),first,result);
}
pub(crate) proof fn part2_plane_duplicate_error(plane:Tier1RawPlane,role:crate::tier1::CoefficientStorageRole,error:crate::DecodeError)
    requires part1_tier1_plane_storage_result(plane.width,plane.height,role,Err(error)),
    ensures part1_plane_duplicate_storage_result(plane,role,Err(error)),
{
    part2_tier1_plane_frames(plane.width,plane.height,role,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_tier1_plane_run(plane.width,plane.height,role,calls),
        |_:Tier1RawPlane,rest|Some((tier1_duplicate_plane(plane),rest)),Err(error),Err(error));
}
pub(crate) open spec fn part2_plane_cleanup_run(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,maximum_u:u8,bitplanes:u16,maximum_work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Tier1RawPlane,crate::tier1::Tier1PassStatistics)> {
    if metadata.width==0{Some((Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),calls))}else{
        part2_tier1_storage_bind(part2_tier1_plane_run(plane.width,plane.height,crate::tier1::CoefficientStorageRole::CleanupOutput,calls),
            |_:Tier1RawPlane,rest|part2_ht_exponent_after_plane(plane,cleanup,metadata,maximum_u,bitplanes,maximum_work,rest))
    }
}
pub(crate) open spec fn part2_plane_cleanup_result(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,maximum_u:u8,bitplanes:u16,maximum_work:u64,
    result:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_cleanup_run(plane,cleanup,metadata,maximum_u,bitplanes,maximum_work,calls),result)
}
pub(crate) proof fn part2_plane_cleanup_normal(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,maximum_u:u8,bitplanes:u16,maximum_work:u64)
    ensures part2_plane_cleanup_result(plane,cleanup,metadata,maximum_u,bitplanes,maximum_work,ht_cleanup_plane(plane,cleanup,metadata,maximum_u,bitplanes,maximum_work)),
{
    let result=ht_cleanup_plane(plane,cleanup,metadata,maximum_u,bitplanes,maximum_work);
    if metadata.width==0{part2_tier1_storage_pure(result);}else{
        let role=crate::tier1::CoefficientStorageRole::CleanupOutput;
        part2_tier1_plane_normal(plane.width,plane.height,role);
        let output=tier1_empty_plane(plane.width,plane.height);if output.is_ok(){
            part2_ht_exponent_after_normal(plane,cleanup,metadata,maximum_u,bitplanes,maximum_work);
            part2_tier1_storage_eta(|calls|part2_ht_exponent_after_plane(plane,cleanup,metadata,maximum_u,bitplanes,maximum_work,calls),result);
        }
        part2_tier1_plane_frames(plane.width,plane.height,role,output);
        part2_tier1_storage_bind_frame(|calls|part2_tier1_plane_run(plane.width,plane.height,role,calls),
            |_:Tier1RawPlane,rest|part2_ht_exponent_after_plane(plane,cleanup,metadata,maximum_u,bitplanes,maximum_work,rest),output,result);
    }
}
pub(crate) proof fn part2_plane_cleanup_error(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,maximum_u:u8,bitplanes:u16,maximum_work:u64,error:crate::DecodeError)
    requires metadata.width!=0,part1_tier1_plane_storage_result(plane.width,plane.height,crate::tier1::CoefficientStorageRole::CleanupOutput,Err(error)),
    ensures part2_plane_cleanup_result(plane,cleanup,metadata,maximum_u,bitplanes,maximum_work,Err(error)),
{
    part2_tier1_plane_frames(plane.width,plane.height,crate::tier1::CoefficientStorageRole::CleanupOutput,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_tier1_plane_run(plane.width,plane.height,crate::tier1::CoefficientStorageRole::CleanupOutput,calls),
        |_:Tier1RawPlane,rest|part2_ht_exponent_after_plane(plane,cleanup,metadata,maximum_u,bitplanes,maximum_work,rest),Err(error),Err(error));
}
pub(crate) open spec fn part2_plane_prepare_admit(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,passes:u32,maximum_u:u8,skipped:u16,work:u64)
    ->Result<(HtMetadataOutput,u16),crate::DecodeError> {
    match ht_cleanup_segment_metadata(cleanup,plane.width,plane.height,maximum_u,work) {
        Err(error)=>Err(error),Ok(metadata)=>match ht_significant_bitplanes(passes) {
            Err(error)=>Err(error),Ok(bits)=>if bits<skipped{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}else{Ok((metadata,(bits-skipped) as u16))},
        },
    }
}
pub(crate) open spec fn part2_plane_prepare_tail(output:(Tier1RawPlane,crate::tier1::Tier1PassStatistics),bits:u16,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16)> {
    part2_tier1_storage_bind(part2_plane_duplicate_run(output.0,crate::tier1::CoefficientStorageRole::CleanupCopy,calls),
        |duplicate:Tier1RawPlane,rest|Some((Ok((output.0,duplicate,output.1,bits)),rest)))
}
pub(crate) open spec fn part2_plane_prepare_run(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16)> {
    part2_tier1_storage_bind(part2_ht_metadata_run(cleanup,plane.width,plane.height,maximum_u,work,calls),
        |metadata:HtMetadataOutput,rest|part2_plane_prepare_after_metadata(plane,cleanup,passes,maximum_u,skipped,work,metadata,rest))
}
pub(crate) open spec fn part2_plane_prepare_after_metadata(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,passes:u32,maximum_u:u8,skipped:u16,work:u64,metadata:HtMetadataOutput,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16)> {
    let admitted=match ht_significant_bitplanes(passes){Err(error)=>Err(error),Ok(bits)=>
        if bits<skipped{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}else{Ok((metadata,(bits-skipped) as u16))}};
    match admitted {
        Err(error)=>Some((Err(error),calls)),
        Ok(admitted)=>part2_tier1_storage_bind(part2_plane_cleanup_run(plane,cleanup,admitted.0,maximum_u,admitted.1,work,calls),
            |output:(Tier1RawPlane,crate::tier1::Tier1PassStatistics),rest|part2_plane_prepare_tail(output,admitted.1,rest)),
    }
}
pub(crate) open spec fn part2_plane_prepare_result(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    result:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_prepare_run(plane,cleanup,passes,maximum_u,skipped,work,calls),result)
}
pub(crate) proof fn part2_plane_prepare_tail_normal(output:(Tier1RawPlane,crate::tier1::Tier1PassStatistics),bits:u16)
    ensures part2_tier1_storage_framed(|calls|part2_plane_prepare_tail(output,bits,calls),
        match tier1_duplicate_plane(output.0) {Err(error)=>Err(error),Ok(duplicate)=>Ok((output.0,duplicate,output.1,bits))}),
{
    let role=crate::tier1::CoefficientStorageRole::CleanupCopy;
    part2_plane_duplicate_normal(output.0,role);
    let duplicate=tier1_duplicate_plane(output.0);
    let result=match duplicate{Err(error)=>Err(error),Ok(value)=>Ok((output.0,value,output.1,bits))};
    if duplicate.is_ok(){part2_tier1_storage_pure(result);}
    part2_tier1_storage_bind_frame(|calls|part2_plane_duplicate_run(output.0,role,calls),
        |duplicate:Tier1RawPlane,rest|Some((Ok((output.0,duplicate,output.1,bits)),rest)),duplicate,result);
}
pub(crate) proof fn part2_plane_prepare_after_normal(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,passes:u32,maximum_u:u8,skipped:u16,work:u64,metadata:HtMetadataOutput)
    requires ht_cleanup_segment_metadata(cleanup,plane.width,plane.height,maximum_u,work)==Ok(metadata),
    ensures part2_tier1_storage_framed(|calls|part2_plane_prepare_after_metadata(plane,cleanup,passes,maximum_u,skipped,work,metadata,calls),ht_cleanup_prepare(plane,cleanup,passes,maximum_u,skipped,work)),
{
    let result=ht_cleanup_prepare(plane,cleanup,passes,maximum_u,skipped,work);
    match part2_plane_prepare_admit(plane,cleanup,passes,maximum_u,skipped,work) {
        Err(_)=>{part2_tier1_storage_pure(result);},
        Ok(admitted)=>{
            part2_plane_cleanup_normal(plane,cleanup,admitted.0,maximum_u,admitted.1,work);
            let output=ht_cleanup_plane(plane,cleanup,admitted.0,maximum_u,admitted.1,work);
            if let Ok(value)=output{
                part2_plane_prepare_tail_normal(value,admitted.1);
                part2_tier1_storage_eta(|calls|part2_plane_prepare_tail(value,admitted.1,calls),result);
            }
            part2_tier1_storage_bind_frame(|calls|part2_plane_cleanup_run(plane,cleanup,admitted.0,maximum_u,admitted.1,work,calls),
                |output:(Tier1RawPlane,crate::tier1::Tier1PassStatistics),rest|part2_plane_prepare_tail(output,admitted.1,rest),output,result);
        },
    }
}
pub(crate) proof fn part2_plane_prepare_normal(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,passes:u32,maximum_u:u8,skipped:u16,work:u64)
    ensures part2_plane_prepare_result(plane,cleanup,passes,maximum_u,skipped,work,ht_cleanup_prepare(plane,cleanup,passes,maximum_u,skipped,work)),
{
    let metadata=ht_cleanup_segment_metadata(cleanup,plane.width,plane.height,maximum_u,work);
    let result=ht_cleanup_prepare(plane,cleanup,passes,maximum_u,skipped,work);
    part2_ht_metadata_normal(cleanup,plane.width,plane.height,maximum_u,work);
    if let Ok(value)=metadata{
        part2_plane_prepare_after_normal(plane,cleanup,passes,maximum_u,skipped,work,value);
        part2_tier1_storage_eta(|calls|part2_plane_prepare_after_metadata(plane,cleanup,passes,maximum_u,skipped,work,value,calls),result);
    }
    part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_run(cleanup,plane.width,plane.height,maximum_u,work,calls),
        |value:HtMetadataOutput,rest|part2_plane_prepare_after_metadata(plane,cleanup,passes,maximum_u,skipped,work,value,rest),metadata,result);
}
pub(crate) proof fn part2_plane_prepare_metadata_error(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,passes:u32,maximum_u:u8,skipped:u16,work:u64,error:crate::DecodeError)
    requires part2_ht_metadata_result(cleanup,plane.width,plane.height,maximum_u,work,Err(error)),
    ensures part2_plane_prepare_result(plane,cleanup,passes,maximum_u,skipped,work,Err(error)),
{
    part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_run(cleanup,plane.width,plane.height,maximum_u,work,calls),
        |value:HtMetadataOutput,rest|part2_plane_prepare_after_metadata(plane,cleanup,passes,maximum_u,skipped,work,value,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_plane_prepare_metadata_join(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,passes:u32,maximum_u:u8,skipped:u16,work:u64,metadata:HtMetadataOutput,
    result:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>)
    requires ht_cleanup_segment_metadata(cleanup,plane.width,plane.height,maximum_u,work)==Ok(metadata),
        part2_tier1_storage_framed(|calls|part2_plane_prepare_after_metadata(plane,cleanup,passes,maximum_u,skipped,work,metadata,calls),result),
    ensures part2_plane_prepare_result(plane,cleanup,passes,maximum_u,skipped,work,result),
{
    part2_ht_metadata_normal(cleanup,plane.width,plane.height,maximum_u,work);
    part2_tier1_storage_eta(|calls|part2_plane_prepare_after_metadata(plane,cleanup,passes,maximum_u,skipped,work,metadata,calls),result);
    part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_run(cleanup,plane.width,plane.height,maximum_u,work,calls),
        |value:HtMetadataOutput,rest|part2_plane_prepare_after_metadata(plane,cleanup,passes,maximum_u,skipped,work,value,rest),Ok(metadata),result);
}
pub(crate) proof fn part2_plane_prepare_cleanup_error(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    admitted:(HtMetadataOutput,u16),error:crate::DecodeError)
    requires part2_plane_prepare_admit(plane,cleanup,passes,maximum_u,skipped,work)==Ok(admitted),
        part2_plane_cleanup_result(plane,cleanup,admitted.0,maximum_u,admitted.1,work,Err(error)),
    ensures part2_plane_prepare_result(plane,cleanup,passes,maximum_u,skipped,work,Err(error)),
{
    part2_tier1_storage_bind_frame(|calls|part2_plane_cleanup_run(plane,cleanup,admitted.0,maximum_u,admitted.1,work,calls),
        |output:(Tier1RawPlane,crate::tier1::Tier1PassStatistics),rest|part2_plane_prepare_tail(output,admitted.1,rest),Err(error),Err(error));
    part2_plane_prepare_metadata_join(plane,cleanup,passes,maximum_u,skipped,work,admitted.0,Err(error));
}
pub(crate) proof fn part2_plane_prepare_duplicate_error(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    admitted:(HtMetadataOutput,u16),output:(Tier1RawPlane,crate::tier1::Tier1PassStatistics),error:crate::DecodeError)
    requires part2_plane_prepare_admit(plane,cleanup,passes,maximum_u,skipped,work)==Ok(admitted),
        part2_plane_cleanup_result(plane,cleanup,admitted.0,maximum_u,admitted.1,work,Ok(output)),
        part1_plane_duplicate_storage_result(output.0,crate::tier1::CoefficientStorageRole::CleanupCopy,Err(error)),
    ensures part2_plane_prepare_result(plane,cleanup,passes,maximum_u,skipped,work,Err(error)),
{
    part2_tier1_storage_bind_frame(|calls|part2_plane_duplicate_run(output.0,crate::tier1::CoefficientStorageRole::CleanupCopy,calls),
        |duplicate:Tier1RawPlane,rest|Some((Ok((output.0,duplicate,output.1,admitted.1)),rest)),Err(error),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_plane_cleanup_run(plane,cleanup,admitted.0,maximum_u,admitted.1,work,calls),
        |output:(Tier1RawPlane,crate::tier1::Tier1PassStatistics),rest|part2_plane_prepare_tail(output,admitted.1,rest),Ok(output),Err(error));
    part2_plane_prepare_metadata_join(plane,cleanup,passes,maximum_u,skipped,work,admitted.0,Err(error));
}
pub(crate) open spec fn part2_plane_refinement_prepared(cleanup:Tier1RawPlane,output:Tier1RawPlane,segment:HtRefinementSegmentState,passes:u8,bits:u16,work:u64)
    ->Result<HtRefinementCoreState,crate::DecodeError> {
    match ht_refinement_readers_initial(segment.significance_propagation.bytes,segment.magnitude_refinement.bytes,segment.encoded.len() as usize,passes==2,work) {
        Err(error)=>Err(error),Ok(readers)=>{
            let state=HtRefinementCoreState {output,readers,cleanup_significant:ht_cleanup_significance(cleanup.coefficients),statistics:tier1_statistics_zero()};
            if passes==2{match ht_refinement_delta(bits){
                Err(error)=>Err(error),Ok(delta)=>{let refined=ht_magref_stripes(state,output.width,output.height,0,delta.1,bits);
                    match refined.0 {Err(error)=>Err(error),Ok(())=>Ok(refined.1)}},
            }}else{Ok(state)}
        },
    }
}
pub(crate) open spec fn part2_plane_significance_run(state:HtRefinementCoreState,encoded:Seq<u8>,bits:u16,causal:bool,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<(Tier1RawPlane,crate::tier1::Tier1PassStatistics)> {
    match ht_significance_magnitude(bits) {
        Err(error)=>Some((Err(error),calls)),
        Ok(magnitude)=>part2_tier1_storage_bind(part2_plane_duplicate_run(state.output,crate::tier1::CoefficientStorageRole::RefinementDiscovery,calls),
            |discovery:Tier1RawPlane,rest|Some((ht_refinement_plane_finish(ht_sigprop_stripes(HtSigpropPlaneState {core:state,discovery},
                state.output.width,state.output.height,0,magnitude,causal),encoded),rest))),
    }
}
pub(crate) open spec fn part2_plane_refinement_after_output(cleanup:Tier1RawPlane,output:Tier1RawPlane,segment:HtRefinementSegmentState,passes:u8,bits:u16,causal:bool,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Tier1RawPlane,crate::tier1::Tier1PassStatistics)> {
    match part2_plane_refinement_prepared(cleanup,output,segment,passes,bits,work){
        Err(error)=>Some((Err(error),calls)),Ok(state)=>part2_plane_significance_run(state,segment.encoded,bits,causal,calls),
    }
}
pub(crate) open spec fn part2_plane_refinement_run(cleanup:Tier1RawPlane,segment:HtRefinementSegmentState,passes:u8,bits:u16,causal:bool,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Tier1RawPlane,crate::tier1::Tier1PassStatistics)> {
    if passes==0 || passes>2 || bits<2{Some((Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),calls))}else{
        part2_tier1_storage_bind(part2_plane_duplicate_run(cleanup,crate::tier1::CoefficientStorageRole::RefinementOutput,calls),
            |output:Tier1RawPlane,rest|part2_plane_refinement_after_output(cleanup,output,segment,passes,bits,causal,work,rest))
    }
}
pub(crate) open spec fn part2_plane_refinement_result(cleanup:Tier1RawPlane,segment:HtRefinementSegmentState,passes:u8,bits:u16,causal:bool,work:u64,
    result:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_refinement_run(cleanup,segment,passes,bits,causal,work,calls),result)
}
pub(crate) proof fn part2_plane_significance_normal(state:HtRefinementCoreState,encoded:Seq<u8>,bits:u16,causal:bool)
    ensures part2_tier1_storage_framed(|calls|part2_plane_significance_run(state,encoded,bits,causal,calls),ht_refinement_significance(state,encoded,bits,causal)),
{
    let result=ht_refinement_significance(state,encoded,bits,causal);
    match ht_significance_magnitude(bits) {
        Err(_)=>{part2_tier1_storage_pure(result);},
        Ok(magnitude)=>{
            let role=crate::tier1::CoefficientStorageRole::RefinementDiscovery;
            part2_plane_duplicate_normal(state.output,role);let discovery=tier1_duplicate_plane(state.output);
            if discovery.is_ok(){part2_tier1_storage_pure(result);}
            part2_tier1_storage_bind_frame(|calls|part2_plane_duplicate_run(state.output,role,calls),
                |discovery:Tier1RawPlane,rest|Some((ht_refinement_plane_finish(ht_sigprop_stripes(HtSigpropPlaneState {core:state,discovery},
                    state.output.width,state.output.height,0,magnitude,causal),encoded),rest)),discovery,result);
        },
    }
}
pub(crate) proof fn part2_plane_refinement_normal(cleanup:Tier1RawPlane,segment:HtRefinementSegmentState,passes:u8,bits:u16,causal:bool,work:u64)
    ensures part2_plane_refinement_result(cleanup,segment,passes,bits,causal,work,ht_refinement_plane(cleanup,segment,passes,bits,causal,work)),
{
    let result=ht_refinement_plane(cleanup,segment,passes,bits,causal,work);
    if passes==0 || passes>2 || bits<2{part2_tier1_storage_pure(result);}else{
        let role=crate::tier1::CoefficientStorageRole::RefinementOutput;
        part2_plane_duplicate_normal(cleanup,role);let output=tier1_duplicate_plane(cleanup);
        if let Ok(value)=output{
            match part2_plane_refinement_prepared(cleanup,value,segment,passes,bits,work) {
                Err(_)=>{part2_tier1_storage_pure(result);},
                Ok(state)=>{part2_plane_significance_normal(state,segment.encoded,bits,causal);part2_tier1_storage_eta(|calls|part2_plane_significance_run(state,segment.encoded,bits,causal,calls),result);},
            }
        }
        part2_tier1_storage_bind_frame(|calls|part2_plane_duplicate_run(cleanup,role,calls),
            |output:Tier1RawPlane,rest|part2_plane_refinement_after_output(cleanup,output,segment,passes,bits,causal,work,rest),output,result);
    }
}
pub(crate) proof fn part2_plane_refinement_output_error(cleanup:Tier1RawPlane,segment:HtRefinementSegmentState,passes:u8,bits:u16,causal:bool,work:u64,error:crate::DecodeError)
    requires passes>0,passes<=2,bits>=2,part1_plane_duplicate_storage_result(cleanup,crate::tier1::CoefficientStorageRole::RefinementOutput,Err(error)),
    ensures part2_plane_refinement_result(cleanup,segment,passes,bits,causal,work,Err(error)),
{
    part2_tier1_storage_bind_frame(|calls|part2_plane_duplicate_run(cleanup,crate::tier1::CoefficientStorageRole::RefinementOutput,calls),
        |output:Tier1RawPlane,rest|part2_plane_refinement_after_output(cleanup,output,segment,passes,bits,causal,work,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_plane_refinement_discovery_error(cleanup:Tier1RawPlane,segment:HtRefinementSegmentState,passes:u8,bits:u16,causal:bool,work:u64,
    output:Tier1RawPlane,state:HtRefinementCoreState,error:crate::DecodeError)
    requires passes>0,passes<=2,bits>=2,
        part1_plane_duplicate_storage_result(cleanup,crate::tier1::CoefficientStorageRole::RefinementOutput,Ok(output)),
        part2_plane_refinement_prepared(cleanup,output,segment,passes,bits,work)==Ok(state),
        ht_significance_magnitude(bits).is_ok(),
        part1_plane_duplicate_storage_result(state.output,crate::tier1::CoefficientStorageRole::RefinementDiscovery,Err(error)),
    ensures part2_plane_refinement_result(cleanup,segment,passes,bits,causal,work,Err(error)),
{
    let magnitude=ht_significance_magnitude(bits).get_Ok_0();
    part2_tier1_storage_bind_frame(|calls|part2_plane_duplicate_run(state.output,crate::tier1::CoefficientStorageRole::RefinementDiscovery,calls),
        |discovery:Tier1RawPlane,rest|Some((ht_refinement_plane_finish(ht_sigprop_stripes(HtSigpropPlaneState {core:state,discovery},
            state.output.width,state.output.height,0,magnitude,causal),segment.encoded),rest)),Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_plane_significance_run(state,segment.encoded,bits,causal,calls),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_plane_duplicate_run(cleanup,crate::tier1::CoefficientStorageRole::RefinementOutput,calls),
        |output:Tier1RawPlane,rest|part2_plane_refinement_after_output(cleanup,output,segment,passes,bits,causal,work,rest),Ok(output),Err(error));
}
}
