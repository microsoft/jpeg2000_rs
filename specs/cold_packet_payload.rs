//! Real preflight/header producers before coefficient-aware packet execution.
use super::*;
verus! {
pub(crate) open spec fn part2_plane_multi_finish(decoders:Seq<Tier1DecoderState>,blocks:u64,present:bool,count:u32,header:usize,start:usize,end:usize,offset:usize,
    executed:Part1PacketBodyExecutionResult)->(Result<crate::packet::PacketBodyDecode,crate::DecodeError>,Seq<Tier1DecoderState>) {
    match executed.0{
        Err(error)=>(Err(error),executed.1.decoders),
        Ok(())=>(part1_multi_summary(blocks,present,count,header,start,end,executed.1.segments,executed.1.passes,offset),executed.1.decoders),
    }
}
pub(crate) open spec fn part2_plane_multi_body_run(decoders:Seq<Tier1DecoderState>,blocks:u64,data:Seq<u8>,contributions:Seq<Option<Part1CodeBlockContribution>>,
    present:bool,count:u32,header:usize,start:usize,offset:usize,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<(Result<crate::packet::PacketBodyDecode,crate::DecodeError>,Seq<Tier1DecoderState>)> {
    let preflight=part1_packet_body_preflight_at(Part1PacketBodyPreflight {index:0,end:start},contributions,data,offset,offset);
    match preflight.0{
        Err(error)=>Some((Ok((Err(error),decoders)),calls)),
        Ok(())=>part2_tier1_storage_bind(part2_plane_execute_run(Part1PacketBodyExecution {decoders,index:0,offset:start,segments:0,passes:0},contributions,data,offset,offset,true,
            pass_limit,byte_limit,input_limit,work,calls),|executed:Part1PacketBodyExecutionResult,rest|
                Some((Ok(part2_plane_multi_finish(decoders,blocks,present,count,header,start,preflight.1.end,offset,executed)),rest))),
    }
}
pub(crate) open spec fn part2_plane_multi_body_result(decoders:Seq<Tier1DecoderState>,blocks:u64,data:Seq<u8>,contributions:Seq<Option<Part1CodeBlockContribution>>,
    present:bool,count:u32,header:usize,start:usize,offset:usize,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,
    result:(Result<crate::packet::PacketBodyDecode,crate::DecodeError>,Seq<Tier1DecoderState>))->bool {
    part2_tier1_storage_framed(|calls|part2_plane_multi_body_run(decoders,blocks,data,contributions,present,count,header,start,offset,pass_limit,byte_limit,input_limit,work,calls),Ok(result))
}
pub(crate) proof fn part2_plane_multi_body_normal(decoders:Seq<Tier1DecoderState>,blocks:u64,data:Seq<u8>,contributions:Seq<Option<Part1CodeBlockContribution>>,
    present:bool,count:u32,header:usize,start:usize,offset:usize,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
    ensures part2_plane_multi_body_result(decoders,blocks,data,contributions,present,count,header,start,offset,pass_limit,byte_limit,input_limit,work,
        part1_multi_body_data(decoders,blocks,data,contributions,present,count,header,start,offset,pass_limit,byte_limit,input_limit,work)),
{
    let result=part1_multi_body_data(decoders,blocks,data,contributions,present,count,header,start,offset,pass_limit,byte_limit,input_limit,work);
    let preflight=part1_packet_body_preflight_at(Part1PacketBodyPreflight {index:0,end:start},contributions,data,offset,offset);
    if preflight.0.is_err(){part2_tier1_storage_pure(Ok(result));}else{
        let initial=Part1PacketBodyExecution {decoders,index:0,offset:start,segments:0,passes:0};
        part2_plane_execute_normal(initial,contributions,data,offset,offset,true,pass_limit,byte_limit,input_limit,work);
        let executed=part1_packet_body_execute_at(initial,contributions,data,offset,offset,true,pass_limit,byte_limit,input_limit,work);
        part2_tier1_storage_eta(|calls|part2_plane_execute_run(initial,contributions,data,offset,offset,true,pass_limit,byte_limit,input_limit,work,calls),Ok(executed));
        part2_tier1_storage_pure(Ok(result));
        part2_tier1_storage_bind_frame(|calls|part2_plane_execute_run(initial,contributions,data,offset,offset,true,pass_limit,byte_limit,input_limit,work,calls),
            |executed:Part1PacketBodyExecutionResult,rest|Some((Ok(part2_plane_multi_finish(decoders,blocks,present,count,header,start,preflight.1.end,offset,executed)),rest)),Ok(executed),Ok(result));
    }
}
pub(crate) proof fn part2_plane_multi_body_observed(decoders:Seq<Tier1DecoderState>,blocks:u64,data:Seq<u8>,contributions:Seq<Option<Part1CodeBlockContribution>>,
    present:bool,count:u32,header:usize,start:usize,offset:usize,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,end:usize,executed:Part1PacketBodyExecutionResult)
    requires part1_packet_body_preflight_at(Part1PacketBodyPreflight {index:0,end:start},contributions,data,offset,offset).0==Ok(()),
        part1_packet_body_preflight_at(Part1PacketBodyPreflight {index:0,end:start},contributions,data,offset,offset).1.end==end,
        part2_plane_execute_result(Part1PacketBodyExecution {decoders,index:0,offset:start,segments:0,passes:0},contributions,data,offset,offset,true,pass_limit,byte_limit,input_limit,work,executed),
    ensures part2_plane_multi_body_result(decoders,blocks,data,contributions,present,count,header,start,offset,pass_limit,byte_limit,input_limit,work,
        part2_plane_multi_finish(decoders,blocks,present,count,header,start,end,offset,executed)),
{
    let result=part2_plane_multi_finish(decoders,blocks,present,count,header,start,end,offset,executed);part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_plane_execute_run(Part1PacketBodyExecution {decoders,index:0,offset:start,segments:0,passes:0},contributions,data,offset,offset,true,
        pass_limit,byte_limit,input_limit,work,calls),|executed:Part1PacketBodyExecutionResult,rest|Some((Ok(part2_plane_multi_finish(decoders,blocks,present,count,header,start,end,offset,executed)),rest)),Ok(executed),Ok(result));
}
pub(crate) open spec fn part2_plane_payload_admit(parameters:Part1PrecinctPayloadParameters,data:Seq<u8>,packet_data:Seq<u8>,reader:Part1PacketReaderState,
    contributions:Seq<Option<Part1CodeBlockContribution>>,sop:usize)->Result<(usize,usize,usize,usize),crate::DecodeError> {
    let finished=part1_packet_reader_finish(reader);
    match finished.0{
        Err(error)=>Err(error),Ok(())=>{
            let header=finished.1.byte_index;
            if !parameters.packed && sop as nat+header as nat>usize::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
            else{
                let offset=if parameters.packed{sop}else{(sop+header) as usize};
                let packed=if parameters.packed{header}else{0usize};
                let body=if !parameters.eph{Ok((offset,packed))}
                else if header as nat+2>usize::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
                else{
                    let end=(header+2) as usize;
                    if end>packet_data.len(){Err(part1_packet_reader_error(parameters.error_offset,crate::MalformedKind::Truncated))}
                    else if !part1_eph_valid(packet_data[header as int],packet_data[header as int+1]){Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader))}
                    else if !parameters.packed && offset as nat+2>usize::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
                    else{Ok((if parameters.packed{offset}else{(offset+2) as usize},if parameters.packed{end}else{packed}))}
                };
                match body{
                    Err(error)=>Err(error),Ok(start)=>{
                        let preflight=part1_packet_body_preflight(Part1PacketBodyPreflight {index:0,end:start.0},contributions,data,parameters.error_offset);
                        match preflight.0{Err(error)=>Err(error),Ok(())=>Ok((header,start.0,start.1,preflight.1.end))}
                    },
                }
            }
        },
    }
}
pub(crate) open spec fn part2_plane_payload_finish(state:Part1PacketPrecinctState,parameters:Part1PrecinctPayloadParameters,present:bool,count:u32,args:(usize,usize,usize,usize),
    executed:Part1PacketBodyExecutionResult)->Part1PrecinctPayloadResult {
    let after=Part1PacketPrecinctState {decoders:executed.1.decoders,..state};
    match executed.0{Err(error)=>(Err(error),after),Ok(())=>part1_precinct_payload_finish(after,parameters,present,count,executed.1.segments,executed.1.passes,args.0,args.1,args.3,args.2)}
}
pub(crate) open spec fn part2_plane_payload_after_run(state:Part1PacketPrecinctState,parameters:Part1PrecinctPayloadParameters,data:Seq<u8>,packet_data:Seq<u8>,reader:Part1PacketReaderState,
    contributions:Seq<Option<Part1CodeBlockContribution>>,count:u32,present:bool,sop:usize,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrecinctPayloadResult> {
    match part2_plane_payload_admit(parameters,data,packet_data,reader,contributions,sop){
        Err(error)=>Some((Ok((Err(error),state)),calls)),
        Ok(args)=>part2_tier1_storage_bind(part2_plane_execute_run(Part1PacketBodyExecution {decoders:state.decoders,index:0,offset:args.1,segments:0,passes:0},contributions,data,
            parameters.error_offset,0,parameters.decode_tier1,pass_limit,byte_limit,input_limit,work,calls),|executed:Part1PacketBodyExecutionResult,rest|
                Some((Ok(part2_plane_payload_finish(state,parameters,present,count,args,executed)),rest))),
    }
}
pub(crate) open spec fn part2_plane_payload_after_result(state:Part1PacketPrecinctState,parameters:Part1PrecinctPayloadParameters,data:Seq<u8>,packet_data:Seq<u8>,reader:Part1PacketReaderState,
    contributions:Seq<Option<Part1CodeBlockContribution>>,count:u32,present:bool,sop:usize,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,result:Part1PrecinctPayloadResult)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_payload_after_run(state,parameters,data,packet_data,reader,contributions,count,present,sop,pass_limit,byte_limit,input_limit,work,calls),Ok(result))
}
pub(crate) proof fn part2_plane_payload_after_normal(state:Part1PacketPrecinctState,parameters:Part1PrecinctPayloadParameters,data:Seq<u8>,packet_data:Seq<u8>,reader:Part1PacketReaderState,
    contributions:Seq<Option<Part1CodeBlockContribution>>,count:u32,present:bool,sop:usize,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
    ensures part2_plane_payload_after_result(state,parameters,data,packet_data,reader,contributions,count,present,sop,pass_limit,byte_limit,input_limit,work,
        part1_precinct_payload_after_headers(state,parameters,data,packet_data,reader,contributions,count,present,sop,pass_limit,byte_limit,input_limit,work)),
{
    reveal(part1_precinct_payload_after_headers);reveal(part1_precinct_payload_body);reveal(part1_packet_body_execute);
    let result=part1_precinct_payload_after_headers(state,parameters,data,packet_data,reader,contributions,count,present,sop,pass_limit,byte_limit,input_limit,work);
    match part2_plane_payload_admit(parameters,data,packet_data,reader,contributions,sop){
        Err(_)=>{part2_tier1_storage_pure(Ok(result));},
        Ok(args)=>{
            let initial=Part1PacketBodyExecution {decoders:state.decoders,index:0,offset:args.1,segments:0,passes:0};
            part2_plane_execute_normal(initial,contributions,data,parameters.error_offset,0,parameters.decode_tier1,pass_limit,byte_limit,input_limit,work);
            let executed=part1_packet_body_execute_at(initial,contributions,data,parameters.error_offset,0,parameters.decode_tier1,pass_limit,byte_limit,input_limit,work);
            part2_tier1_storage_eta(|calls|part2_plane_execute_run(initial,contributions,data,parameters.error_offset,0,parameters.decode_tier1,pass_limit,byte_limit,input_limit,work,calls),Ok(executed));
            part2_tier1_storage_pure(Ok(result));
            part2_tier1_storage_bind_frame(|calls|part2_plane_execute_run(initial,contributions,data,parameters.error_offset,0,parameters.decode_tier1,pass_limit,byte_limit,input_limit,work,calls),
                |executed:Part1PacketBodyExecutionResult,rest|Some((Ok(part2_plane_payload_finish(state,parameters,present,count,args,executed)),rest)),Ok(executed),Ok(result));
        },
    }
}
pub(crate) proof fn part2_plane_payload_after_observed(state:Part1PacketPrecinctState,parameters:Part1PrecinctPayloadParameters,data:Seq<u8>,packet_data:Seq<u8>,reader:Part1PacketReaderState,
    contributions:Seq<Option<Part1CodeBlockContribution>>,count:u32,present:bool,sop:usize,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,args:(usize,usize,usize,usize),executed:Part1PacketBodyExecutionResult)
    requires part2_plane_payload_admit(parameters,data,packet_data,reader,contributions,sop)==Ok(args),
        part2_plane_execute_result(Part1PacketBodyExecution {decoders:state.decoders,index:0,offset:args.1,segments:0,passes:0},contributions,data,parameters.error_offset,0,parameters.decode_tier1,
            pass_limit,byte_limit,input_limit,work,executed),
    ensures part2_plane_payload_after_result(state,parameters,data,packet_data,reader,contributions,count,present,sop,pass_limit,byte_limit,input_limit,work,
        part2_plane_payload_finish(state,parameters,present,count,args,executed)),
{
    let result=part2_plane_payload_finish(state,parameters,present,count,args,executed);part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_plane_execute_run(Part1PacketBodyExecution {decoders:state.decoders,index:0,offset:args.1,segments:0,passes:0},contributions,data,
        parameters.error_offset,0,parameters.decode_tier1,pass_limit,byte_limit,input_limit,work,calls),
        |executed:Part1PacketBodyExecutionResult,rest|Some((Ok(part2_plane_payload_finish(state,parameters,present,count,args,executed)),rest)),Ok(executed),Ok(result));
}
pub struct Part2PlanePayloadHeader {
    pub packet:Seq<u8>,pub reader:Part1PacketReaderState,pub contributions:Seq<Option<Part1CodeBlockContribution>>,
    pub count:u32,pub present:bool,pub sop:usize,
}
pub(crate) open spec fn part2_plane_payload_headers(state:Part1PacketPrecinctState,data:Seq<u8>,packed:Seq<u8>,parameters:Part1PrecinctPayloadParameters,header_limit:u64,work:u64)
    ->(Result<Part2PlanePayloadHeader,crate::DecodeError>,Part1PacketPrecinctState) {
    match part1_precinct_payload_prefix(data,packed,parameters,header_limit,work){
        Err(error)=>(Err(error),state),Ok(prefix)=>{
            let initial=Part1PrecinctHeaderState {states:state.states,subbands:state.subbands,contributions:Seq::new(state.states.len(),|_:int|None),
                reader:prefix.reader,subband_index:0,local_index:0,contribution_count:0};
            let headers=if prefix.present && state.contexts.len()>0{part1_precinct_headers(initial,state.contexts,state.contexts[0].layer,parameters.style)}else{(Ok(()),initial)};
            let after=Part1PacketPrecinctState {states:headers.1.states,subbands:headers.1.subbands,..state};
            (match headers.0{Err(error)=>Err(error),Ok(())=>Ok(Part2PlanePayloadHeader {packet:prefix.packet_data,reader:headers.1.reader,contributions:headers.1.contributions,
                count:headers.1.contribution_count,present:prefix.present,sop:prefix.sop_bytes})},after)
        },
    }
}
pub struct Part2PrecinctContributionsContext {
    pub state:Part1PacketPrecinctState,pub data:Seq<u8>,pub packed:Seq<u8>,pub parameters:Part1PrecinctPayloadParameters,
    pub header_limit:u64,pub work:u64,
}
pub(crate) open spec fn part2_precinct_contributions_run(context:Part2PrecinctContributionsContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=context.state.states.len();
    if count==0 {Some((Ok(()),calls))}else if calls.len()==0 {None}else{
        match calls[0] {
            Part2Tier1StorageEvent::PrecinctContributions {context:actual,elements,succeeded}=>
                if actual!=context || elements!=count {None}else{
                    Some((if succeeded {Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
                },
            _=>None,
        }
    }
}
pub(crate) open spec fn part2_precinct_contributions_result(context:Part2PrecinctContributionsContext,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_precinct_contributions_run(context,calls),result)
}
pub(crate) proof fn part2_precinct_contributions_observed(context:Part2PrecinctContributionsContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (context.state.states.len()>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_precinct_contributions_result(context,result),
{
    let count=context.state.states.len();
    let prefix=if count==0 {Seq::empty()}else{seq![Part2Tier1StorageEvent::PrecinctContributions {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_precinct_contributions_run(context,prefix+tail)==Some((result,tail)) by{
        if count==0 {assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_precinct_contributions_run(context,calls),prefix,result));
}
pub(crate) open spec fn part2_plane_payload_prepared_run(state:Part1PacketPrecinctState,data:Seq<u8>,packed:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrecinctPayloadResult> {
    let prepared=part2_plane_payload_headers(state,data,packed,parameters,header_limit,work);
    match prepared.0{
        Err(error)=>Some((Ok((Err(error),prepared.1)),calls)),
        Ok(h)=>part2_plane_payload_after_run(prepared.1,parameters,data,h.packet,h.reader,h.contributions,h.count,h.present,h.sop,pass_limit,byte_limit,input_limit,work,calls),
    }
}
pub(crate) open spec fn part2_plane_payload_run(state:Part1PacketPrecinctState,data:Seq<u8>,packed:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrecinctPayloadResult> {
    match part1_precinct_payload_prefix(data,packed,parameters,header_limit,work) {
        Err(error)=>Some((Ok((Err(error),state)),calls)),
        Ok(_)=>part2_tier1_storage_resume(part2_precinct_contributions_run(
            Part2PrecinctContributionsContext {state,data,packed,parameters,header_limit,work},calls),
            |result:Result<(),crate::DecodeError>,rest|match result {
                Err(error)=>Some((Ok((Err(error),state)),rest)),
                Ok(())=>part2_plane_payload_prepared_run(state,data,packed,parameters,header_limit,pass_limit,byte_limit,input_limit,work,rest),
            }),
    }
}
pub(crate) open spec fn part2_plane_payload_result(state:Part1PacketPrecinctState,data:Seq<u8>,packed:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,result:Part1PrecinctPayloadResult)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_payload_run(state,data,packed,parameters,header_limit,pass_limit,byte_limit,input_limit,work,calls),Ok(result))
}
pub(crate) proof fn part2_plane_payload_prepared_normal(state:Part1PacketPrecinctState,data:Seq<u8>,packed:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
    ensures part2_tier1_storage_framed(
        |calls|part2_plane_payload_prepared_run(state,data,packed,parameters,header_limit,pass_limit,byte_limit,input_limit,work,calls),
        Ok(part1_precinct_payload(state,data,packed,parameters,header_limit,pass_limit,byte_limit,input_limit,work))),
{
    reveal(part1_precinct_payload_headers);
    let result=part1_precinct_payload(state,data,packed,parameters,header_limit,pass_limit,byte_limit,input_limit,work);
    let prepared=part2_plane_payload_headers(state,data,packed,parameters,header_limit,work);
    match prepared.0{
        Err(_)=>{part2_tier1_storage_pure(Ok(result));},
        Ok(h)=>{
            part2_plane_payload_after_normal(prepared.1,parameters,data,h.packet,h.reader,h.contributions,h.count,h.present,h.sop,pass_limit,byte_limit,input_limit,work);
            part2_tier1_storage_eta(|calls|part2_plane_payload_after_run(prepared.1,parameters,data,h.packet,h.reader,h.contributions,h.count,h.present,h.sop,pass_limit,byte_limit,input_limit,work,calls),Ok(result));
        },
    }
}
pub(crate) proof fn part2_plane_payload_capacity_then(context:Part2PrecinctContributionsContext,pass_limit:u32,byte_limit:u64,input_limit:u64,
    response:Result<(),crate::DecodeError>,result:Part1PrecinctPayloadResult)
    requires part1_precinct_payload_prefix(context.data,context.packed,context.parameters,context.header_limit,context.work).is_ok(),
        part2_precinct_contributions_result(context,response),
        match response {
            Err(error)=>result==(Err(error),context.state),
            Ok(())=>part2_tier1_storage_framed(
                |calls|part2_plane_payload_prepared_run(context.state,context.data,context.packed,context.parameters,context.header_limit,pass_limit,byte_limit,input_limit,context.work,calls),Ok(result)),
        },
    ensures part2_plane_payload_result(context.state,context.data,context.packed,context.parameters,context.header_limit,pass_limit,byte_limit,input_limit,context.work,result),
{
    if let Err(error)=response {part2_tier1_storage_pure(Ok(result));}else{
        part2_tier1_storage_eta(
            |calls|part2_plane_payload_prepared_run(context.state,context.data,context.packed,context.parameters,context.header_limit,pass_limit,byte_limit,input_limit,context.work,calls),Ok(result));
    }
    part2_tier1_resume_frame(|calls|part2_precinct_contributions_run(context,calls),
        |reply:Result<(),crate::DecodeError>,rest|match reply {
            Err(error)=>Some((Ok((Err(error),context.state)),rest)),
            Ok(())=>part2_plane_payload_prepared_run(context.state,context.data,context.packed,context.parameters,context.header_limit,pass_limit,byte_limit,input_limit,context.work,rest),
        },response,Ok(result));
}
pub(crate) proof fn part2_plane_payload_normal(state:Part1PacketPrecinctState,data:Seq<u8>,packed:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
    ensures part2_plane_payload_result(state,data,packed,parameters,header_limit,pass_limit,byte_limit,input_limit,work,
        part1_precinct_payload(state,data,packed,parameters,header_limit,pass_limit,byte_limit,input_limit,work)),
{
    let result=part1_precinct_payload(state,data,packed,parameters,header_limit,pass_limit,byte_limit,input_limit,work);
    match part1_precinct_payload_prefix(data,packed,parameters,header_limit,work) {
        Err(_)=>{reveal(part1_precinct_payload_headers);part2_tier1_storage_pure(Ok(result));},
        Ok(_)=>{
            let context=Part2PrecinctContributionsContext {state,data,packed,parameters,header_limit,work};
            part2_precinct_contributions_observed(context,Ok(()));
            part2_plane_payload_prepared_normal(state,data,packed,parameters,header_limit,pass_limit,byte_limit,input_limit,work);
            part2_plane_payload_capacity_then(context,pass_limit,byte_limit,input_limit,Ok(()),result);
        },
    }
}
pub(crate) proof fn part2_plane_payload_observed(state:Part1PacketPrecinctState,data:Seq<u8>,packed:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,after:Part1PacketPrecinctState,h:Part2PlanePayloadHeader,result:Part1PrecinctPayloadResult)
    requires part2_plane_payload_headers(state,data,packed,parameters,header_limit,work)==(Ok(h),after),
        part2_precinct_contributions_result(Part2PrecinctContributionsContext {state,data,packed,parameters,header_limit,work},Ok(())),
        part2_plane_payload_after_result(after,parameters,data,h.packet,h.reader,h.contributions,h.count,h.present,h.sop,pass_limit,byte_limit,input_limit,work,result),
    ensures part2_plane_payload_result(state,data,packed,parameters,header_limit,pass_limit,byte_limit,input_limit,work,result),
{
    part2_tier1_storage_eta(|calls|part2_plane_payload_after_run(after,parameters,data,h.packet,h.reader,h.contributions,h.count,h.present,h.sop,pass_limit,byte_limit,input_limit,work,calls),Ok(result));
    assert(part2_tier1_storage_framed(|calls|part2_plane_payload_prepared_run(state,data,packed,parameters,header_limit,pass_limit,byte_limit,input_limit,work,calls),Ok(result)));
    part2_plane_payload_capacity_then(Part2PrecinctContributionsContext {state,data,packed,parameters,header_limit,work},pass_limit,byte_limit,input_limit,Ok(()),result);
}
pub struct Part2PlaneMultiHeader {pub contributions:Seq<Option<Part1CodeBlockContribution>>,pub present:bool,pub count:u32,pub header:usize,pub start:usize}
pub(crate) open spec fn part2_plane_multi_headers(s:Part1MultiPacketState,data:Seq<u8>,sop:bool,eph:bool,offset:usize,header_limit:u64,work:u64)
    ->(Result<Part2PlaneMultiHeader,crate::DecodeError>,Part1MultiPacketState) {
    match part1_multi_packet_prefix(data,sop,offset,header_limit,work){
        Err(error)=>(Err(error),s),Ok(prefix)=>{
            let initial=Part1MultiPacketHeader {states:s.states,inclusion:s.inclusion,zero:s.zero,contexts:s.contexts,
                contributions:Seq::new(s.states.len(),|_:int|None),reader:prefix.reader,index:0,count:0};
            let headers=if prefix.present{part1_multi_headers(initial,offset)}else{(Ok(()),initial)};
            let after=Part1MultiPacketState {states:headers.1.states,inclusion:headers.1.inclusion,zero:headers.1.zero,..s};
            (match headers.0{
                Err(error)=>Err(error),Ok(())=>{
                    let finished=part1_packet_reader_finish(headers.1.reader);
                    match finished.0{Err(error)=>Err(error),Ok(())=>match part1_multi_body_start(data,prefix.sop_bytes,finished.1.byte_index,eph,offset){
                        Err(error)=>Err(error),Ok(start)=>Ok(Part2PlaneMultiHeader {contributions:headers.1.contributions,present:prefix.present,count:headers.1.count,header:finished.1.byte_index,start}),
                    }}
                },
            },after)
        },
    }
}
pub(crate) struct Part2MultiContributionsContext {
    pub state:Part1MultiPacketState,pub data:Seq<u8>,pub sop:bool,pub eph:bool,pub offset:usize,
    pub header_limit:u64,pub pass_limit:u32,pub byte_limit:u64,pub input_limit:u64,pub work:u64,
}
pub(crate) open spec fn part2_multi_contributions_run(context:Part2MultiContributionsContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=context.state.states.len();
    if count==0 {Some((Ok(()),calls))}else if calls.len()==0 {None}else{match calls[0] {
        Part2Tier1StorageEvent::MultiContributions {context:actual,elements,succeeded}=>
            if actual!=context || elements!=count {None}else{
                Some((if succeeded {Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
            },
        _=>None,
    }}
}
pub(crate) open spec fn part2_multi_contributions_result(context:Part2MultiContributionsContext,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_multi_contributions_run(context,calls),result)
}
pub(crate) proof fn part2_multi_contributions_observed(context:Part2MultiContributionsContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (context.state.states.len()>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_multi_contributions_result(context,result),
{
    let count=context.state.states.len();
    let prefix=if count==0 {Seq::empty()}else{
        seq![Part2Tier1StorageEvent::MultiContributions {context,elements:count,succeeded:result.is_ok()}]
    };
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_multi_contributions_run(context,prefix+tail)==Some((result,tail)) by {
        if count==0 {assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_multi_contributions_run(context,calls),prefix,result));
}
pub(crate) open spec fn part2_multi_contributions_after(context:Part2MultiContributionsContext,reply:Result<(),crate::DecodeError>,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1MultiPacketResult> {
    match reply {
        Err(error)=>Some((Ok((Err(error),context.state)),calls)),
        Ok(())=>part2_plane_multi_payload_after_capacity_run(context.state,context.data,context.sop,context.eph,context.offset,
            context.header_limit,context.pass_limit,context.byte_limit,context.input_limit,context.work,calls),
    }
}
pub(crate) open spec fn part2_plane_multi_payload_run(s:Part1MultiPacketState,data:Seq<u8>,sop:bool,eph:bool,offset:usize,header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1MultiPacketResult> {
    match part1_multi_packet_prefix(data,sop,offset,header_limit,work) {
        Err(error)=>Some((Ok((Err(error),s)),calls)),Ok(_)=>{
            let context=Part2MultiContributionsContext {state:s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work};
            part2_tier1_storage_resume(part2_multi_contributions_run(context,calls),
                |reply,rest|part2_multi_contributions_after(context,reply,rest))
        },
    }
}
pub(crate) open spec fn part2_plane_multi_payload_after_capacity_run(s:Part1MultiPacketState,data:Seq<u8>,sop:bool,eph:bool,offset:usize,header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1MultiPacketResult> {
    let prepared=part2_plane_multi_headers(s,data,sop,eph,offset,header_limit,work);
    match prepared.0{
        Err(error)=>Some((Ok((Err(error),prepared.1)),calls)),Ok(h)=>
            part2_tier1_storage_bind(part2_plane_multi_body_run(prepared.1.decoders,prepared.1.states.len() as u64,data,h.contributions,h.present,h.count,h.header,h.start,offset,pass_limit,byte_limit,input_limit,work,calls),
                |decoded:(Result<crate::packet::PacketBodyDecode,crate::DecodeError>,Seq<Tier1DecoderState>),rest|Some((Ok((decoded.0,Part1MultiPacketState {decoders:decoded.1,..prepared.1})),rest))),
    }
}
pub(crate) open spec fn part2_plane_multi_payload_result(s:Part1MultiPacketState,data:Seq<u8>,sop:bool,eph:bool,offset:usize,header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,
    result:Part1MultiPacketResult)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_multi_payload_run(s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work,calls),Ok(result))
}
pub(crate) proof fn part2_plane_multi_payload_after_capacity_normal(s:Part1MultiPacketState,data:Seq<u8>,sop:bool,eph:bool,offset:usize,header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
    ensures part2_tier1_storage_framed(|calls|part2_plane_multi_payload_after_capacity_run(
        s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work,calls),
        Ok(part1_multi_payload(s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work))),
{
    reveal(part1_multi_payload);
    reveal(part1_multi_body);
    let result=part1_multi_payload(s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work);
    let prepared=part2_plane_multi_headers(s,data,sop,eph,offset,header_limit,work);
    match prepared.0{
        Err(_)=>{part2_tier1_storage_pure(Ok(result));},Ok(h)=>{
            let before=prepared.1;
            part2_plane_multi_body_normal(before.decoders,before.states.len() as u64,data,h.contributions,h.present,h.count,h.header,h.start,offset,pass_limit,byte_limit,input_limit,work);
            let decoded=part1_multi_body_data(before.decoders,before.states.len() as u64,data,h.contributions,h.present,h.count,h.header,h.start,offset,pass_limit,byte_limit,input_limit,work);
            part2_tier1_storage_pure(Ok(result));
            part2_tier1_storage_bind_frame(|calls|part2_plane_multi_body_run(before.decoders,before.states.len() as u64,data,h.contributions,h.present,h.count,h.header,h.start,offset,pass_limit,byte_limit,input_limit,work,calls),
                |decoded:(Result<crate::packet::PacketBodyDecode,crate::DecodeError>,Seq<Tier1DecoderState>),rest|Some((Ok((decoded.0,Part1MultiPacketState {decoders:decoded.1,..before})),rest)),Ok(decoded),Ok(result));
        },
    }
}
pub(crate) proof fn part2_plane_multi_payload_observed(s:Part1MultiPacketState,data:Seq<u8>,sop:bool,eph:bool,offset:usize,header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,
    before:Part1MultiPacketState,h:Part2PlaneMultiHeader,decoded:(Result<crate::packet::PacketBodyDecode,crate::DecodeError>,Seq<Tier1DecoderState>))
    requires part2_plane_multi_headers(s,data,sop,eph,offset,header_limit,work)==(Ok(h),before),
        part2_plane_multi_body_result(before.decoders,before.states.len() as u64,data,h.contributions,h.present,h.count,h.header,h.start,offset,pass_limit,byte_limit,input_limit,work,decoded),
    ensures part2_plane_multi_payload_result(s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work,(decoded.0,Part1MultiPacketState {decoders:decoded.1,..before})),
{
    let result=(decoded.0,Part1MultiPacketState {decoders:decoded.1,..before});part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_plane_multi_body_run(before.decoders,before.states.len() as u64,data,h.contributions,h.present,h.count,h.header,h.start,offset,pass_limit,byte_limit,input_limit,work,calls),
        |decoded:(Result<crate::packet::PacketBodyDecode,crate::DecodeError>,Seq<Tier1DecoderState>),rest|Some((Ok((decoded.0,Part1MultiPacketState {decoders:decoded.1,..before})),rest)),Ok(decoded),Ok(result));
    part2_multi_contributions_after_capacity_frames(Part2MultiContributionsContext {
        state:s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work,
    },result);
}
pub(crate) proof fn part2_multi_contributions_after_capacity_frames(context:Part2MultiContributionsContext,result:Part1MultiPacketResult)
    requires part1_multi_packet_prefix(context.data,context.sop,context.offset,context.header_limit,context.work).is_ok(),
        part2_tier1_storage_framed(|calls|part2_plane_multi_payload_after_capacity_run(context.state,context.data,context.sop,
            context.eph,context.offset,context.header_limit,context.pass_limit,context.byte_limit,context.input_limit,context.work,calls),Ok(result)),
    ensures part2_plane_multi_payload_result(context.state,context.data,context.sop,context.eph,context.offset,context.header_limit,
        context.pass_limit,context.byte_limit,context.input_limit,context.work,result),
{
    part2_multi_contributions_observed(context,Ok(()));
    part2_tier1_storage_eta(|calls|part2_plane_multi_payload_after_capacity_run(context.state,context.data,context.sop,
        context.eph,context.offset,context.header_limit,context.pass_limit,context.byte_limit,context.input_limit,context.work,calls),Ok(result));
    part2_tier1_storage_eta(|calls|part2_multi_contributions_after(context,Ok(()),calls),Ok(result));
    part2_tier1_resume_frame(|calls|part2_multi_contributions_run(context,calls),
        |reply,rest|part2_multi_contributions_after(context,reply,rest),Ok(()),Ok(result));
}
pub(crate) proof fn part2_plane_multi_payload_normal(s:Part1MultiPacketState,data:Seq<u8>,sop:bool,eph:bool,offset:usize,header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
    ensures part2_plane_multi_payload_result(s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work,
        part1_multi_payload(s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work)),
{
    let context=Part2MultiContributionsContext {state:s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work};
    match part1_multi_packet_prefix(data,sop,offset,header_limit,work) {
        Err(_)=>{
            reveal(part1_multi_payload);part2_tier1_storage_pure(Ok(part1_multi_payload(
                s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work)));
        },
        Ok(_)=>{
            part2_plane_multi_payload_after_capacity_normal(s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work);
            part2_multi_contributions_after_capacity_frames(context,part1_multi_payload(
                s,data,sop,eph,offset,header_limit,pass_limit,byte_limit,input_limit,work));
        },
    }
}
pub(crate) proof fn part2_multi_contributions_refused(context:Part2MultiContributionsContext,error:crate::DecodeError)
    requires part1_multi_packet_prefix(context.data,context.sop,context.offset,context.header_limit,context.work).is_ok(),
        part2_multi_contributions_result(context,Err(error)),
    ensures part2_plane_multi_payload_result(context.state,context.data,context.sop,context.eph,context.offset,context.header_limit,
        context.pass_limit,context.byte_limit,context.input_limit,context.work,(Err(error),context.state)),
{
    let result=Ok((Err::<crate::packet::PacketBodyDecode,crate::DecodeError>(error),context.state));
    part2_tier1_storage_pure(result);
    part2_tier1_resume_frame(|calls|part2_multi_contributions_run(context,calls),
        |reply,rest|part2_multi_contributions_after(context,reply,rest),Err(error),result);
}
pub(crate) open spec fn part2_plane_precinct_admit(s:Part1PacketPrecinctState,part:Part2OwnedTilePart,offset:usize,packed_offset:usize,expected:Option<u32>,sequence:u16,decode:bool,
    blocks:u64,work:u64)->Result<Part1PrecinctPayloadParameters,crate::DecodeError> {
    if s.states.len()!=s.contexts.len() || s.states.len()!=s.decoders.len() || (s.states.len()==0)!=(s.subbands.len()==0){Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader))}
    else if s.states.len() as u64>blocks{Err(part1_packet_reader_limit(crate::Resource::CodeBlocks,blocks,s.states.len() as u64))}
    else if s.states.len() as u64>work{Err(part1_packet_reader_limit(crate::Resource::WorkUnits,work,s.states.len() as u64))}
    else if offset>part.data.len(){Err(part1_packet_reader_error(offset,crate::MalformedKind::InvalidPacketLength))}
    else{match crate::codestream::component_coding_style_result(&part.component_coding_styles,s.component){
        Err(error)=>Err(error),Ok(style)=>match crate::codestream::coding_style_tier1_result(style){
            Err(error)=>Err(error),Ok(tier1)=>{
                let markers=crate::codestream::coding_style_packet_markers(&part.coding_style);
                Ok(Part1PrecinctPayloadParameters {error_offset:offset,packed_offset,expected_packet_length:expected,expected_sop_sequence:sequence,
                    style:tier1,sop:markers.0,eph:markers.1,packed:!matches!(part.packed_packet_headers.source,Part1PackedHeaderSource::None),decode_tier1:decode})
            },
        },
    }}
}
pub(crate) open spec fn part2_plane_precinct_run(s:Part1PacketPrecinctState,part:Part2OwnedTilePart,offset:usize,packed:Seq<u8>,packed_offset:usize,expected:Option<u32>,sequence:u16,decode:bool,
    blocks:u64,header:u64,passes:u32,bytes:u64,input:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrecinctPayloadResult> {
    match part2_plane_precinct_admit(s,part,offset,packed_offset,expected,sequence,decode,blocks,work){
        Err(error)=>Some((Ok((Err(error),s)),calls)),Ok(parameters)=>part2_plane_payload_run(s,part.data.subrange(offset as int,part.data.len() as int),packed,parameters,header,passes,bytes,input,work,calls),
    }
}
pub(crate) open spec fn part2_plane_precinct_result(s:Part1PacketPrecinctState,part:Part2OwnedTilePart,offset:usize,packed:Seq<u8>,packed_offset:usize,expected:Option<u32>,sequence:u16,decode:bool,
    blocks:u64,header:u64,passes:u32,bytes:u64,input:u64,work:u64,result:Part1PrecinctPayloadResult)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_precinct_run(s,part,offset,packed,packed_offset,expected,sequence,decode,blocks,header,passes,bytes,input,work,calls),Ok(result))
}
pub(crate) proof fn part2_plane_precinct_normal(s:Part1PacketPrecinctState,part:Part2OwnedTilePart,offset:usize,packed:Seq<u8>,packed_offset:usize,expected:Option<u32>,sequence:u16,decode:bool,
    blocks:u64,header:u64,passes:u32,bytes:u64,input:u64,work:u64)
    ensures part2_plane_precinct_result(s,part,offset,packed,packed_offset,expected,sequence,decode,blocks,header,passes,bytes,input,work,
        part1_precinct_packet_owned(s,part,offset,packed,packed_offset,expected,sequence,decode,blocks,header,passes,bytes,input,work)),
{
    let result=part1_precinct_packet_owned(s,part,offset,packed,packed_offset,expected,sequence,decode,blocks,header,passes,bytes,input,work);
    match part2_plane_precinct_admit(s,part,offset,packed_offset,expected,sequence,decode,blocks,work){
        Err(_)=>{part2_tier1_storage_pure(Ok(result));},Ok(p)=>{
            let data=part.data.subrange(offset as int,part.data.len() as int);
            part2_plane_payload_normal(s,data,packed,p,header,passes,bytes,input,work);
            part2_tier1_storage_eta(|calls|part2_plane_payload_run(s,data,packed,p,header,passes,bytes,input,work,calls),Ok(result));
        },
    }
}
pub(crate) proof fn part2_plane_precinct_observed(s:Part1PacketPrecinctState,part:Part2OwnedTilePart,offset:usize,packed:Seq<u8>,packed_offset:usize,expected:Option<u32>,sequence:u16,decode:bool,
    blocks:u64,header:u64,passes:u32,bytes:u64,input:u64,work:u64,parameters:Part1PrecinctPayloadParameters,result:Part1PrecinctPayloadResult)
    requires part2_plane_precinct_admit(s,part,offset,packed_offset,expected,sequence,decode,blocks,work)==Ok(parameters),
        part2_plane_payload_result(s,part.data.subrange(offset as int,part.data.len() as int),packed,parameters,header,passes,bytes,input,work,result),
    ensures part2_plane_precinct_result(s,part,offset,packed,packed_offset,expected,sequence,decode,blocks,header,passes,bytes,input,work,result),
{part2_tier1_storage_eta(|calls|part2_plane_payload_run(s,part.data.subrange(offset as int,part.data.len() as int),packed,parameters,header,passes,bytes,input,work,calls),Ok(result));}
pub(crate) open spec fn part2_jpip_inner_inline(part:Part2OwnedTilePart,data:Seq<u8>)->Part2OwnedTilePart {
    Part2OwnedTilePart {tile_part_index:0,tile_part_count:1,data,
        packet_lengths:Part1PacketLengths {source:Part1PacketLengthSource::None,packet_count:0,encoded_bytes:0},
        packed_packet_headers:Part1PackedHeaders {source:Part1PackedHeaderSource::None,length:0,fragments:0},..part}
}
pub(crate) open spec fn part2_jpip_inner_finish(packet:Part1PrecinctPayloadResult)->(Result<usize,crate::DecodeError>,Part1PacketPrecinctState) {
    let result=match packet.0 {
        Err(error)=>Err(error),
        Ok((decoded,consumed,packed))=>if packed!=0 {Err(part1_packet_reader_error(0,crate::MalformedKind::InvalidPacketLength))}
            else if decoded.bytes_consumed as nat>usize::MAX {Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
            else if consumed!=decoded.bytes_consumed as nat {Err(part1_packet_reader_error(0,crate::MalformedKind::InvalidPacketLength))}
            else{Ok(consumed)},
    };
    (result,packet.1)
}
pub(crate) open spec fn part2_jpip_inline_copy_run(source:Part2OwnedTilePart,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    if calls.len()==0 {None}else{match calls[0] {
        Part2Tier1StorageEvent::PayloadMetadataCopy {source:actual,calls:inner}=>if actual!=source {None}else{
            match part1_mct_copy_run(part2_payload_duplicate_tail(source,0),inner) {
                Some((reply,rest))=>if rest.len()!=0 {None}else{Some((reply,calls.drop_first()))},
                None=>None,
            }
        },
        _=>None,
    }}
}
pub(crate) proof fn part2_jpip_inline_copy_observed(source:Part2OwnedTilePart,result:Result<Part2OwnedTilePart,crate::DecodeError>)
    requires part1_mct_copy_result(part2_payload_duplicate_tail(source,0),match result {Ok(_)=>Ok(()),Err(error)=>Err(error)}),
        result.is_ok() ==> result==Ok(source),
    ensures part2_tier1_storage_framed(|calls|part2_jpip_inline_copy_run(source,calls),
        match result {Ok(_)=>Ok(()),Err(error)=>Err(error)}),
{
    reveal(part1_mct_copy_result);
    let reply=match result {Ok(_)=>Ok(()),Err(error)=>Err(error)};
    let inner=choose|inner:Seq<Part1ColdStorageEvent>|part1_mct_copy_run(part2_payload_duplicate_tail(source,0),inner)==Some((reply,Seq::empty()));
    let prefix=seq![Part2Tier1StorageEvent::PayloadMetadataCopy {source,calls:inner}];
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_jpip_inline_copy_run(source,prefix+tail)==Some((reply,tail)) by {
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_tier1_storage_prefix(|calls|part2_jpip_inline_copy_run(source,calls),prefix,reply));
}
pub(crate) proof fn part2_jpip_inline_copy_normal(source:Part2OwnedTilePart)
    ensures part2_tier1_storage_framed(|calls|part2_jpip_inline_copy_run(source,calls),Ok(())),
{
    reveal(part1_mct_copy_result);
    let requests=part2_payload_duplicate_tail(source,0);
    part1_mct_copy_normal(requests,Seq::empty());
    assert(part1_mct_copy_run(requests,part1_mct_copy_normal_calls(requests))==Some((Ok(()),Seq::empty())));
    part2_jpip_inline_copy_observed(source,Ok(source));
}
pub(crate) open spec fn part2_jpip_inner_after_copy_run(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Result<usize,crate::DecodeError>,Part1PacketPrecinctState)> {
    part2_tier1_storage_bind(part2_plane_precinct_run(part1_precinct_context_layer(initial,layer),part2_jpip_inner_inline(part,data),0,Seq::empty(),0,None,sequence,false,
        crate::limits::resource_code_block_limit(limits),crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls),
        |packet:Part1PrecinctPayloadResult,rest|Some((Ok(part2_jpip_inner_finish(packet)),rest)))
}
pub(crate) open spec fn part2_jpip_inner_run(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Result<usize,crate::DecodeError>,Part1PacketPrecinctState)> {
    part2_tier1_storage_resume(part2_jpip_inline_copy_run(part,calls),|reply:Result<(),crate::DecodeError>,rest|match reply {
        Err(error)=>Some((Ok((Err(error),part1_precinct_context_layer(initial,layer))),rest)),
        Ok(())=>part2_jpip_inner_after_copy_run(initial,part,data,sequence,layer,limits,rest),
    })
}
pub(crate) open spec fn part2_jpip_inner_result(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,result:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState))->bool {
    part2_tier1_storage_framed(|calls|part2_jpip_inner_run(initial,part,data,sequence,layer,limits,calls),Ok(result))
}
pub(crate) proof fn part2_jpip_inner_after_copy_frames(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,result:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState))
    requires part2_tier1_storage_framed(|calls|part2_jpip_inner_after_copy_run(initial,part,data,sequence,layer,limits,calls),Ok(result)),
    ensures part2_jpip_inner_result(initial,part,data,sequence,layer,limits,result),
{
    part2_jpip_inline_copy_normal(part);
    part2_tier1_storage_eta(|calls|part2_jpip_inner_after_copy_run(initial,part,data,sequence,layer,limits,calls),Ok(result));
    part2_tier1_resume_frame(|calls|part2_jpip_inline_copy_run(part,calls),|reply:Result<(),crate::DecodeError>,rest|match reply {
        Err(error)=>Some((Ok((Err(error),part1_precinct_context_layer(initial,layer))),rest)),
        Ok(())=>part2_jpip_inner_after_copy_run(initial,part,data,sequence,layer,limits,rest),
    },Ok(()),Ok(result));
}
pub(crate) proof fn part2_jpip_inner_copy_error(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,error:crate::DecodeError)
    requires part2_tier1_storage_framed(|calls|part2_jpip_inline_copy_run(part,calls),Err(error)),
    ensures part2_jpip_inner_result(initial,part,data,sequence,layer,limits,(Err(error),part1_precinct_context_layer(initial,layer))),
{
    let result=Ok((Err::<usize,crate::DecodeError>(error),part1_precinct_context_layer(initial,layer)));
    part2_tier1_storage_pure(result);
    part2_tier1_resume_frame(|calls|part2_jpip_inline_copy_run(part,calls),|reply:Result<(),crate::DecodeError>,rest|match reply {
        Err(error)=>Some((Ok((Err(error),part1_precinct_context_layer(initial,layer))),rest)),
        Ok(())=>part2_jpip_inner_after_copy_run(initial,part,data,sequence,layer,limits,rest),
    },Err(error),result);
}
pub(crate) proof fn part2_jpip_inner_observed(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,
    limits:&crate::ResourceLimits,packet:Part1PrecinctPayloadResult)
    requires part2_plane_precinct_result(part1_precinct_context_layer(initial,layer),part2_jpip_inner_inline(part,data),0,Seq::empty(),0,None,sequence,false,
        crate::limits::resource_code_block_limit(limits),crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),packet),
    ensures part2_jpip_inner_result(initial,part,data,sequence,layer,limits,part2_jpip_inner_finish(packet)),
{
    part2_tier1_storage_pure(Ok(part2_jpip_inner_finish(packet)));
    part2_tier1_storage_bind_frame(|calls|part2_plane_precinct_run(part1_precinct_context_layer(initial,layer),part2_jpip_inner_inline(part,data),0,Seq::empty(),0,None,sequence,false,
        crate::limits::resource_code_block_limit(limits),crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls),
        |packet:Part1PrecinctPayloadResult,rest|Some((Ok(part2_jpip_inner_finish(packet)),rest)),Ok(packet),Ok(part2_jpip_inner_finish(packet)));
    part2_jpip_inner_after_copy_frames(initial,part,data,sequence,layer,limits,part2_jpip_inner_finish(packet));
}
pub(crate) proof fn part2_jpip_inner_normal(initial:Part1PacketPrecinctState,part:Part2OwnedTilePart,data:Seq<u8>,sequence:u16,layer:u16,limits:&crate::ResourceLimits)
    ensures part2_jpip_inner_result(initial,part,data,sequence,layer,limits,
        part2_jpip_inner_finish(part1_precinct_packet_owned(part1_precinct_context_layer(initial,layer),part2_jpip_inner_inline(part,data),0,Seq::empty(),0,None,sequence,false,
            crate::limits::resource_code_block_limit(limits),crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits)))),
{
    let state=part1_precinct_context_layer(initial,layer);let inline=part2_jpip_inner_inline(part,data);
    part2_plane_precinct_normal(state,inline,0,Seq::empty(),0,None,sequence,false,
        crate::limits::resource_code_block_limit(limits),crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));
    part2_jpip_inner_observed(initial,part,data,sequence,layer,limits,part1_precinct_packet_owned(state,inline,0,Seq::empty(),0,None,sequence,false,
        crate::limits::resource_code_block_limit(limits),crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits)));
}
pub(crate) open spec fn part2_plane_multi_packet_run(s:Part1MultiPacketState,part:&crate::codestream::TilePartPayload<'_>,offset:usize,limits:&crate::ResourceLimits,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1MultiPacketResult> {
    match part1_multi_packet_admission(s,part,offset,crate::limits::resource_code_block_limit(limits),crate::limits::resource_work_limit(limits)){
        Err(error)=>Some((Ok((Err(error),s)),calls)),Ok(data)=>{
            let markers=crate::codestream::coding_style_packet_markers(&part.coding_style);
            part2_plane_multi_payload_run(s,data,markers.0,markers.1,offset,crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls)
        },
    }
}
pub closed spec fn part2_plane_multi_packet_result(s:Part1MultiPacketState,part:&crate::codestream::TilePartPayload<'_>,offset:usize,limits:&crate::ResourceLimits,result:Part1MultiPacketResult)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_multi_packet_run(s,part,offset,limits,calls),Ok(result))
}
pub(crate) proof fn part2_plane_multi_packet_normal(s:Part1MultiPacketState,part:&crate::codestream::TilePartPayload<'_>,offset:usize,limits:&crate::ResourceLimits)
    ensures part2_plane_multi_packet_result(s,part,offset,limits,part1_multi_code_block_packet(s,part,offset,limits)),
{
    let result=part1_multi_code_block_packet(s,part,offset,limits);
    match part1_multi_packet_admission(s,part,offset,crate::limits::resource_code_block_limit(limits),crate::limits::resource_work_limit(limits)){
        Err(_)=>{part2_tier1_storage_pure(Ok(result));},Ok(data)=>{
            let markers=crate::codestream::coding_style_packet_markers(&part.coding_style);
            part2_plane_multi_payload_normal(s,data,markers.0,markers.1,offset,crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));
            part2_tier1_storage_eta(|calls|part2_plane_multi_payload_run(s,data,markers.0,markers.1,offset,crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls),Ok(result));
        },
    }
}
pub(crate) proof fn part2_plane_multi_packet_observed(s:Part1MultiPacketState,part:&crate::codestream::TilePartPayload<'_>,offset:usize,limits:&crate::ResourceLimits,data:Seq<u8>,result:Part1MultiPacketResult)
    requires part1_multi_packet_admission(s,part,offset,crate::limits::resource_code_block_limit(limits),crate::limits::resource_work_limit(limits))==Ok(data),
        part2_plane_multi_payload_result(s,data,crate::codestream::coding_style_packet_markers(&part.coding_style).0,crate::codestream::coding_style_packet_markers(&part.coding_style).1,offset,
            crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),result),
    ensures part2_plane_multi_packet_result(s,part,offset,limits,result),
{part2_tier1_storage_eta(|calls|part2_plane_multi_payload_run(s,data,crate::codestream::coding_style_packet_markers(&part.coding_style).0,crate::codestream::coding_style_packet_markers(&part.coding_style).1,offset,
    crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
    crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),calls),Ok(result));}
}
