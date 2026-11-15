//! Actual fresh quad/previous/per-row pattern owners in the cleanup metadata producer.
use super::*;
verus! {
pub enum Part2HtMetadataRole {Quads,Previous,Current}
pub struct Part2HtMetadataContext {
    pub width:u16,pub height:u16,pub maximum_u:u8,pub work:u64,
    pub mel:Seq<u8>,pub vlc:Seq<u8>,pub row:nat,pub quads:nat,
    pub previous:Option<Seq<u8>>,pub significant:u16,pub mel_bits:nat,pub vlc_bits:nat,
}
pub type Part2HtMetadataStep=(Result<(),crate::DecodeError>,HtMetadataRowState);
pub(crate) open spec fn part2_ht_metadata_context(cleanup:HtCleanupSegmentState,width:u16,height:u16,maximum_u:u8,work:u64)->Part2HtMetadataContext {
    Part2HtMetadataContext {width,height,maximum_u,work,mel:cleanup.mel.bytes,vlc:cleanup.vlc.bytes,
        row:0,quads:0,previous:None,significant:0,mel_bits:0,vlc_bits:0}
}
pub(crate) open spec fn part2_ht_metadata_row_context(state:HtMetadataRowState,row:nat,width:u16,height:u16,maximum_u:u8)->Part2HtMetadataContext {
    Part2HtMetadataContext {width,height,maximum_u,work:state.readers.maximum_work_units,
        mel:state.readers.mel.input,vlc:state.readers.vlc.input,row,quads:state.quads.len(),
        previous:Some(state.previous),significant:state.significant,
        mel_bits:state.readers.mel.bits_read as nat,vlc_bits:state.readers.vlc.bits_read as nat}
}
pub(crate) open spec fn part2_ht_metadata_count(context:Part2HtMetadataContext,role:Part2HtMetadataRole)->nat {
    match role {
        Part2HtMetadataRole::Quads=>((context.width as nat+1)/2)*((context.height as nat+1)/2),
        Part2HtMetadataRole::Previous=>(context.width as nat+1)/2,
        Part2HtMetadataRole::Current=>match context.previous{Some(previous)=>previous.len(),None=>0nat},
    }
}
    pub(crate) open spec fn part2_ht_decode_metadata_run(input:Seq<u8>,width:u16,height:u16,maximum_u:u8,bytes:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtMetadataOutput> {
        match ht_parse_block_segments(input,None,bytes){Err(error)=>Some((Err(error),calls)),Ok(segments)=>part2_ht_metadata_run(segments.cleanup,width,height,maximum_u,work,calls)}
    }
    pub closed spec fn part1_ht_decode_metadata_storage_result(input:Seq<u8>,width:u16,height:u16,maximum_u:u8,bytes:u64,work:u64,result:Result<HtMetadataOutput,crate::DecodeError>)->bool {
        part2_tier1_storage_framed(|calls|part2_ht_decode_metadata_run(input,width,height,maximum_u,bytes,work,calls),result)
    }
    pub(crate) proof fn part2_ht_decode_metadata_normal(input:Seq<u8>,width:u16,height:u16,maximum_u:u8,bytes:u64,work:u64)
        ensures part1_ht_decode_metadata_storage_result(input,width,height,maximum_u,bytes,work,ht_decode_cleanup_metadata(input,width,height,maximum_u,bytes,work)),
    {
        reveal(part1_ht_decode_metadata_storage_result);
        match ht_parse_block_segments(input,None,bytes){
            Err(error)=>{part2_tier1_storage_pure(Err::<HtMetadataOutput,crate::DecodeError>(error));},
            Ok(segments)=>{part2_ht_metadata_normal(segments.cleanup,width,height,maximum_u,work);
                part2_tier1_storage_eta(|calls|part2_ht_metadata_run(segments.cleanup,width,height,maximum_u,work,calls),ht_cleanup_segment_metadata(segments.cleanup,width,height,maximum_u,work));},
        }
    }
    pub(crate) proof fn part2_ht_decode_metadata_observed(input:Seq<u8>,width:u16,height:u16,maximum_u:u8,bytes:u64,work:u64,segments:HtBlockSegmentsState,result:Result<HtMetadataOutput,crate::DecodeError>)
        requires ht_parse_block_segments(input,None,bytes)==Ok(segments),part2_ht_metadata_result(segments.cleanup,width,height,maximum_u,work,result),
        ensures part1_ht_decode_metadata_storage_result(input,width,height,maximum_u,bytes,work,result),
    {
        reveal(part1_ht_decode_metadata_storage_result);
        part2_tier1_storage_eta(|calls|part2_ht_metadata_run(segments.cleanup,width,height,maximum_u,work,calls),result);
    }
#[verifier::opaque]
pub(crate) open spec fn part2_ht_metadata_capacity_run(context:Part2HtMetadataContext,role:Part2HtMetadataRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=part2_ht_metadata_count(context,role);
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::HtMetadataCapacity {context:actual,role:field,elements,succeeded}=>
            if actual!=context || field!=role || elements!=count{None}else{
                Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
            },
        _=>None,
    }}
}
pub(crate) open spec fn part2_ht_metadata_capacity_result(context:Part2HtMetadataContext,role:Part2HtMetadataRole,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_metadata_capacity_run(context,role,calls),result)
}
pub(crate) proof fn part2_ht_metadata_capacity_observed(context:Part2HtMetadataContext,role:Part2HtMetadataRole,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_ht_metadata_count(context,role)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_ht_metadata_capacity_result(context,role,result),
{
    reveal(part2_ht_metadata_capacity_run);
    let count=part2_ht_metadata_count(context,role);
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::HtMetadataCapacity {context,role,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_ht_metadata_capacity_run(context,role,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_ht_metadata_capacity_run(context,role,calls),prefix,result));
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_metadata_row_run(state:HtMetadataRowState,row:nat,width:u16,height:u16,maximum_u:u8,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2HtMetadataStep> {
    part2_tier1_storage_resume(part2_ht_metadata_capacity_run(part2_ht_metadata_row_context(state,row,width,height,maximum_u),Part2HtMetadataRole::Current,calls),
        |result:Result<(),crate::DecodeError>,rest|Some((Ok(match result{Err(error)=>(Err(error),state),Ok(())=>ht_metadata_row(state,row,width,height,maximum_u)}),rest)))
}
pub(crate) open spec fn part2_ht_metadata_row_result(state:HtMetadataRowState,row:nat,width:u16,height:u16,maximum_u:u8,result:Part2HtMetadataStep)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_metadata_row_run(state,row,width,height,maximum_u,calls),Ok(result))
}
pub(crate) proof fn part2_ht_metadata_row_normal(state:HtMetadataRowState,row:nat,width:u16,height:u16,maximum_u:u8)
    ensures part2_ht_metadata_row_result(state,row,width,height,maximum_u,ht_metadata_row(state,row,width,height,maximum_u)),
{
    reveal(part2_ht_metadata_row_run);
    let context=part2_ht_metadata_row_context(state,row,width,height,maximum_u);
    let result=ht_metadata_row(state,row,width,height,maximum_u);
    part2_ht_metadata_capacity_observed(context,Part2HtMetadataRole::Current,Ok(()));
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_resume_frame(|calls|part2_ht_metadata_capacity_run(context,Part2HtMetadataRole::Current,calls),
        |value:Result<(),crate::DecodeError>,rest|Some((Ok(match value{Err(error)=>(Err(error),state),Ok(())=>result}),rest)),Ok(()),Ok(result));
}
pub(crate) proof fn part2_ht_metadata_row_refused(state:HtMetadataRowState,row:nat,width:u16,height:u16,maximum_u:u8,error:crate::DecodeError)
    requires part2_ht_metadata_capacity_result(part2_ht_metadata_row_context(state,row,width,height,maximum_u),Part2HtMetadataRole::Current,Err(error)),
    ensures part2_ht_metadata_row_result(state,row,width,height,maximum_u,(Err(error),state)),
{
    reveal(part2_ht_metadata_row_run);part2_tier1_storage_pure(Ok::<Part2HtMetadataStep,crate::DecodeError>((Err(error),state)));
    part2_tier1_resume_frame(|calls|part2_ht_metadata_capacity_run(part2_ht_metadata_row_context(state,row,width,height,maximum_u),Part2HtMetadataRole::Current,calls),
        |value:Result<(),crate::DecodeError>,rest|Some((Ok(match value{Err(e)=>(Err(e),state),Ok(())=>ht_metadata_row(state,row,width,height,maximum_u)}),rest)),Err(error),Ok((Err(error),state)));
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_metadata_rows_run(state:HtMetadataRowState,width:u16,height:u16,maximum_u:u8,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2HtMetadataStep>
    decreases count,
{
    if count==0{Some((Ok((Ok(()),state)),calls))}else{
        part2_tier1_storage_bind(part2_ht_metadata_rows_run(state,width,height,maximum_u,(count-1) as nat,calls),
            |step:Part2HtMetadataStep,rest|part2_ht_metadata_rows_next(step,(count-1) as nat,width,height,maximum_u,rest))
    }
}
pub(crate) open spec fn part2_ht_metadata_rows_next(step:Part2HtMetadataStep,row:nat,width:u16,height:u16,maximum_u:u8,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2HtMetadataStep> {
    match step.0{Err(_)=>Some((Ok(step),calls)),Ok(())=>part2_ht_metadata_row_run(step.1,row,width,height,maximum_u,calls)}
}
pub(crate) proof fn part2_ht_metadata_rows_normal(state:HtMetadataRowState,width:u16,height:u16,maximum_u:u8,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_ht_metadata_rows_run(state,width,height,maximum_u,count,calls),Ok(ht_metadata_rows(state,width,height,maximum_u,count))),
    decreases count,
{
    reveal(part2_ht_metadata_rows_run);reveal(ht_metadata_rows);
    let result=ht_metadata_rows(state,width,height,maximum_u,count);
    if count==0{part2_tier1_storage_pure(Ok(result));}else{
        part2_ht_metadata_rows_normal(state,width,height,maximum_u,(count-1) as nat);
        let prefix=ht_metadata_rows(state,width,height,maximum_u,(count-1) as nat);
        match prefix.0{
            Err(_)=>{part2_tier1_storage_pure(Ok(result));},
            Ok(())=>{part2_ht_metadata_row_normal(prefix.1,(count-1) as nat,width,height,maximum_u);
                part2_tier1_storage_eta(|calls|part2_ht_metadata_row_run(prefix.1,(count-1) as nat,width,height,maximum_u,calls),Ok(result));},
        }
        part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_rows_run(state,width,height,maximum_u,(count-1) as nat,calls),
            |step:Part2HtMetadataStep,rest|part2_ht_metadata_rows_next(step,(count-1) as nat,width,height,maximum_u,rest),Ok(prefix),Ok(result));
    }
}
pub(crate) proof fn part2_ht_metadata_rows_step(state:HtMetadataRowState,width:u16,height:u16,maximum_u:u8,row:nat,before:HtMetadataRowState,result:Part2HtMetadataStep)
    requires ht_metadata_rows(state,width,height,maximum_u,row)==(Ok(()),before),
        part2_ht_metadata_row_result(before,row,width,height,maximum_u,result),
    ensures part2_tier1_storage_framed(|calls|part2_ht_metadata_rows_run(state,width,height,maximum_u,row+1,calls),Ok(result)),
{
    reveal(part2_ht_metadata_rows_run);
    part2_ht_metadata_rows_normal(state,width,height,maximum_u,row);
    part2_tier1_storage_eta(|calls|part2_ht_metadata_row_run(before,row,width,height,maximum_u,calls),Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_rows_run(state,width,height,maximum_u,row,calls),
        |step:Part2HtMetadataStep,rest|part2_ht_metadata_rows_next(step,row,width,height,maximum_u,rest),Ok((Ok(()),before)),Ok(result));
}
pub(crate) proof fn part2_ht_metadata_rows_error(state:HtMetadataRowState,width:u16,height:u16,maximum_u:u8,prefix:nat,count:nat,result:Part2HtMetadataStep)
    requires prefix<=count,result.0.is_err(),
        part2_tier1_storage_framed(|calls|part2_ht_metadata_rows_run(state,width,height,maximum_u,prefix,calls),Ok(result)),
    ensures part2_tier1_storage_framed(|calls|part2_ht_metadata_rows_run(state,width,height,maximum_u,count,calls),Ok(result)),
    decreases count-prefix,
{
    if prefix<count{
        reveal(part2_ht_metadata_rows_run);
        part2_ht_metadata_rows_error(state,width,height,maximum_u,prefix,(count-1) as nat,result);
        part2_tier1_storage_pure(Ok(result));
        part2_tier1_storage_eta(|calls|part2_ht_metadata_rows_next(result,(count-1) as nat,width,height,maximum_u,calls),Ok(result));
        part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_rows_run(state,width,height,maximum_u,(count-1) as nat,calls),
            |step:Part2HtMetadataStep,rest|part2_ht_metadata_rows_next(step,(count-1) as nat,width,height,maximum_u,rest),Ok(result),Ok(result));
    }
}
pub(crate) open spec fn part2_ht_metadata_admit(cleanup:HtCleanupSegmentState,width:u16,height:u16,maximum_u:u8,work:u64)->Result<HtCleanupReaderState,crate::DecodeError> {
    if width==0 || height==0 || maximum_u==0 || maximum_u>75{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
    else if width as nat*height as nat>u32::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
    else if width as nat*height as nat>4096{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
    else{ht_cleanup_readers_initial(cleanup.mel.bytes,cleanup.vlc.bytes,work)}
}
pub(crate) open spec fn part2_ht_metadata_start(readers:HtCleanupReaderState,width:u16)->HtMetadataRowState {
    HtMetadataRowState {readers,quads:Seq::empty(),previous:Seq::new((width as nat+1)/2,|_:int|0u8),significant:0}
}
pub(crate) open spec fn part2_ht_metadata_after_previous(readers:HtCleanupReaderState,width:u16,height:u16,maximum_u:u8,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtMetadataOutput> {
    part2_tier1_storage_bind(part2_ht_metadata_rows_run(part2_ht_metadata_start(readers,width),width,height,maximum_u,(height as nat+1)/2,calls),
        |step:Part2HtMetadataStep,rest|Some((ht_metadata_finish(step,width,height),rest)))
}
pub(crate) open spec fn part2_ht_metadata_after_quads(cleanup:HtCleanupSegmentState,width:u16,height:u16,maximum_u:u8,work:u64,readers:HtCleanupReaderState,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtMetadataOutput> {
    part2_tier1_storage_bind(part2_ht_metadata_capacity_run(part2_ht_metadata_context(cleanup,width,height,maximum_u,work),Part2HtMetadataRole::Previous,calls),
        |_:(),rest|part2_ht_metadata_after_previous(readers,width,height,maximum_u,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_metadata_run(cleanup:HtCleanupSegmentState,width:u16,height:u16,maximum_u:u8,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtMetadataOutput> {
    match part2_ht_metadata_admit(cleanup,width,height,maximum_u,work){
        Err(error)=>Some((Err(error),calls)),Ok(readers)=>
            part2_tier1_storage_bind(part2_ht_metadata_capacity_run(part2_ht_metadata_context(cleanup,width,height,maximum_u,work),Part2HtMetadataRole::Quads,calls),
                |_:(),rest|part2_ht_metadata_after_quads(cleanup,width,height,maximum_u,work,readers,rest)),
    }
}
pub(crate) open spec fn part2_ht_metadata_result(cleanup:HtCleanupSegmentState,width:u16,height:u16,maximum_u:u8,work:u64,result:Result<HtMetadataOutput,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_metadata_run(cleanup,width,height,maximum_u,work,calls),result)
}
pub(crate) proof fn part2_ht_metadata_after_previous_normal(readers:HtCleanupReaderState,width:u16,height:u16,maximum_u:u8)
    ensures part2_tier1_storage_framed(|calls|part2_ht_metadata_after_previous(readers,width,height,maximum_u,calls),
        ht_metadata_finish(ht_metadata_rows(part2_ht_metadata_start(readers,width),width,height,maximum_u,(height as nat+1)/2),width,height)),
{
    let state=part2_ht_metadata_start(readers,width);let step=ht_metadata_rows(state,width,height,maximum_u,(height as nat+1)/2);
    let result=ht_metadata_finish(step,width,height);
    part2_ht_metadata_rows_normal(state,width,height,maximum_u,(height as nat+1)/2);part2_tier1_storage_pure(result);
    part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_rows_run(state,width,height,maximum_u,(height as nat+1)/2,calls),
        |step:Part2HtMetadataStep,rest|Some((ht_metadata_finish(step,width,height),rest)),Ok(step),result);
}
pub(crate) proof fn part2_ht_metadata_normal(cleanup:HtCleanupSegmentState,width:u16,height:u16,maximum_u:u8,work:u64)
    ensures part2_ht_metadata_result(cleanup,width,height,maximum_u,work,ht_cleanup_segment_metadata(cleanup,width,height,maximum_u,work)),
{
    reveal(part2_ht_metadata_run);
    let result=ht_cleanup_segment_metadata(cleanup,width,height,maximum_u,work);
    match part2_ht_metadata_admit(cleanup,width,height,maximum_u,work){
        Err(_)=>{part2_tier1_storage_pure(result);},Ok(readers)=>{
            let context=part2_ht_metadata_context(cleanup,width,height,maximum_u,work);
            part2_ht_metadata_after_previous_normal(readers,width,height,maximum_u);
            part2_tier1_storage_eta(|calls|part2_ht_metadata_after_previous(readers,width,height,maximum_u,calls),result);
            part2_ht_metadata_capacity_observed(context,Part2HtMetadataRole::Previous,Ok(()));
            part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_capacity_run(context,Part2HtMetadataRole::Previous,calls),
                |_:(),rest|part2_ht_metadata_after_previous(readers,width,height,maximum_u,rest),Ok(()),result);
            part2_tier1_storage_eta(|calls|part2_ht_metadata_after_quads(cleanup,width,height,maximum_u,work,readers,calls),result);
            part2_ht_metadata_capacity_observed(context,Part2HtMetadataRole::Quads,Ok(()));
            part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_capacity_run(context,Part2HtMetadataRole::Quads,calls),
                |_:(),rest|part2_ht_metadata_after_quads(cleanup,width,height,maximum_u,work,readers,rest),Ok(()),result);
        },
    }
}
pub(crate) proof fn part2_ht_metadata_join(cleanup:HtCleanupSegmentState,width:u16,height:u16,maximum_u:u8,work:u64,readers:HtCleanupReaderState,result:Result<HtMetadataOutput,crate::DecodeError>)
    requires part2_ht_metadata_admit(cleanup,width,height,maximum_u,work)==Ok(readers),
        part2_tier1_storage_framed(|calls|part2_ht_metadata_after_quads(cleanup,width,height,maximum_u,work,readers,calls),result),
    ensures part2_ht_metadata_result(cleanup,width,height,maximum_u,work,result),
{
    reveal(part2_ht_metadata_run);
    let context=part2_ht_metadata_context(cleanup,width,height,maximum_u,work);
    part2_ht_metadata_capacity_observed(context,Part2HtMetadataRole::Quads,Ok(()));
    part2_tier1_storage_eta(|calls|part2_ht_metadata_after_quads(cleanup,width,height,maximum_u,work,readers,calls),result);
    part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_capacity_run(context,Part2HtMetadataRole::Quads,calls),
        |_:(),rest|part2_ht_metadata_after_quads(cleanup,width,height,maximum_u,work,readers,rest),Ok(()),result);
}
pub(crate) proof fn part2_ht_metadata_initial_error(cleanup:HtCleanupSegmentState,width:u16,height:u16,maximum_u:u8,work:u64,readers:HtCleanupReaderState,previous:bool,error:crate::DecodeError)
    requires part2_ht_metadata_admit(cleanup,width,height,maximum_u,work)==Ok(readers),
        part2_ht_metadata_capacity_result(part2_ht_metadata_context(cleanup,width,height,maximum_u,work),
            if previous{Part2HtMetadataRole::Previous}else{Part2HtMetadataRole::Quads},Err(error)),
    ensures part2_ht_metadata_result(cleanup,width,height,maximum_u,work,Err(error)),
{
    reveal(part2_ht_metadata_run);
    let context=part2_ht_metadata_context(cleanup,width,height,maximum_u,work);
    if previous{
        part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_capacity_run(context,Part2HtMetadataRole::Previous,calls),
            |_:(),rest|part2_ht_metadata_after_previous(readers,width,height,maximum_u,rest),Err(error),Err(error));
        part2_ht_metadata_join(cleanup,width,height,maximum_u,work,readers,Err(error));
    }else{
        part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_capacity_run(context,Part2HtMetadataRole::Quads,calls),
            |_:(),rest|part2_ht_metadata_after_quads(cleanup,width,height,maximum_u,work,readers,rest),Err(error),Err(error));
    }
}
pub(crate) proof fn part2_ht_metadata_row_error(cleanup:HtCleanupSegmentState,width:u16,height:u16,maximum_u:u8,work:u64,readers:HtCleanupReaderState,row:nat,before:HtMetadataRowState,step:Part2HtMetadataStep)
    requires part2_ht_metadata_admit(cleanup,width,height,maximum_u,work)==Ok(readers),
        row<(height as nat+1)/2,step.0.is_err(),
        ht_metadata_rows(part2_ht_metadata_start(readers,width),width,height,maximum_u,row)==(Ok(()),before),
        part2_ht_metadata_row_result(before,row,width,height,maximum_u,step),
    ensures part2_ht_metadata_result(cleanup,width,height,maximum_u,work,Err(step.0.get_Err_0())),
{
    let state=part2_ht_metadata_start(readers,width);let count=(height as nat+1)/2;let error=step.0.get_Err_0();
    part2_ht_metadata_rows_step(state,width,height,maximum_u,row,before,step);
    part2_ht_metadata_rows_error(state,width,height,maximum_u,row+1,count,step);part2_tier1_storage_pure(Err::<HtMetadataOutput,crate::DecodeError>(error));
    part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_rows_run(state,width,height,maximum_u,count,calls),
        |value:Part2HtMetadataStep,rest|Some((ht_metadata_finish(value,width,height),rest)),Ok(step),Err(error));
    let context=part2_ht_metadata_context(cleanup,width,height,maximum_u,work);
    part2_ht_metadata_capacity_observed(context,Part2HtMetadataRole::Previous,Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_ht_metadata_capacity_run(context,Part2HtMetadataRole::Previous,calls),
        |_:(),rest|part2_ht_metadata_after_previous(readers,width,height,maximum_u,rest),Ok(()),Err(error));
    part2_ht_metadata_join(cleanup,width,height,maximum_u,work,readers,Err(error));
}
}
