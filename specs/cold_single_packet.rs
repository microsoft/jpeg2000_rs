//! Header-derived standalone packet body inputs and exact partial header/decoder state.
use super::*;
verus! {
pub(crate) open spec fn part2_plane_single_admit(s:Part1SinglePacketState,payload:Seq<u8>,context:crate::packet::CodeBlockPacketContext,header_limit:u64,work:u64)
    ->(Result<Option<(Part1CodeBlockContribution,usize)>,crate::DecodeError>,Part1SinglePacketState) {
    match part1_packet_reader_initial(payload,header_limit,work) {
        Err(error)=>(Err(error),s),
        Ok(reader)=>{
            let first=part1_packet_reader_read(reader);
            match first.0 {
                Err(error)=>(Err(error),s),
                Ok(false)=>{
                    let finished=part1_packet_reader_finish(first.1);
                    match finished.0 {Err(error)=>(Err(error),s),Ok(())=>if finished.1.byte_index!=payload.len(){
                        (Err(part1_packet_reader_error(finished.1.byte_index,crate::MalformedKind::TrailingData)),s)
                    }else{(Ok(None),s)}}
                },
                Ok(true)=>{
                    let header=part1_packet_header_decode(s.state,s.inclusion,s.zero,context,first.1);
                    let after=Part1SinglePacketState {state:header.1,inclusion:header.2,zero:header.3,..s};
                    match header.0 {
                        Err(error)=>(Err(error),after),
                        Ok(None)=>(Err(part1_packet_reader_error(header.4.byte_index,crate::MalformedKind::InvalidPacketHeader)),after),
                        Ok(Some(c))=>{
                            let finished=part1_packet_reader_finish(header.4);
                            match finished.0 {
                                Err(error)=>(Err(error),after),
                                Ok(())=>if finished.1.byte_index>payload.len(){(Err(part1_packet_reader_error(finished.1.byte_index,crate::MalformedKind::Truncated)),after)}
                                    else{(Ok(Some((c,finished.1.byte_index))),after)},
                            }
                        },
                    }
                },
            }
        },
    }
}
pub(crate) open spec fn part2_plane_single_finish(header:Part1SinglePacketState,decoded:HtCodeBlockBodyResult)->Part1SinglePacketResult {
    (match decoded.0{Err(error)=>Err(error),Ok(value)=>Ok(Some(value))},Part1SinglePacketState {decoder:decoded.1,..header})
}
pub(crate) open spec fn part2_plane_single_run(s:Part1SinglePacketState,payload:Seq<u8>,context:crate::packet::CodeBlockPacketContext,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1SinglePacketResult> {
    let admitted=part2_plane_single_admit(s,payload,context,header_limit,work);
    match admitted.0 {
        Ok(Some(args))=>part2_tier1_storage_bind(part2_plane_body_transaction_run(admitted.1.decoder,args.0,payload.subrange(args.1 as int,payload.len() as int),pass_limit,byte_limit,input_limit,work,calls),
            |decoded:HtCodeBlockBodyResult,rest|Some((Ok(part2_plane_single_finish(admitted.1,decoded)),rest))),
        _=>Some((Ok(part1_single_code_block_packet(s,payload,context,header_limit,pass_limit,byte_limit,input_limit,work)),calls)),
    }
}
pub closed spec fn part2_plane_single_result(s:Part1SinglePacketState,payload:Seq<u8>,context:crate::packet::CodeBlockPacketContext,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,result:Part1SinglePacketResult)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_single_run(s,payload,context,header_limit,pass_limit,byte_limit,input_limit,work,calls),Ok(result))
}
pub(crate) proof fn part2_plane_single_normal(s:Part1SinglePacketState,payload:Seq<u8>,context:crate::packet::CodeBlockPacketContext,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
    ensures part2_plane_single_result(s,payload,context,header_limit,pass_limit,byte_limit,input_limit,work,
        part1_single_code_block_packet(s,payload,context,header_limit,pass_limit,byte_limit,input_limit,work)),
{
    let result=part1_single_code_block_packet(s,payload,context,header_limit,pass_limit,byte_limit,input_limit,work);
    let admitted=part2_plane_single_admit(s,payload,context,header_limit,work);
    match admitted.0 {
        Ok(Some(args))=>{
            let body=payload.subrange(args.1 as int,payload.len() as int);
            part2_plane_body_transaction_normal(admitted.1.decoder,args.0,body,pass_limit,byte_limit,input_limit,work);
            let decoded=part1_code_block_body_transaction(admitted.1.decoder,args.0,body,pass_limit,byte_limit,input_limit,work);
            part2_plane_body_transaction_frames(admitted.1.decoder,args.0,body,pass_limit,byte_limit,input_limit,work,decoded);
            part2_tier1_storage_pure(Ok(result));
            part2_tier1_storage_bind_frame(|calls|part2_plane_body_transaction_run(admitted.1.decoder,args.0,body,pass_limit,byte_limit,input_limit,work,calls),
                |decoded:HtCodeBlockBodyResult,rest|Some((Ok(part2_plane_single_finish(admitted.1,decoded)),rest)),Ok(decoded),Ok(result));
        },
        _=>{part2_tier1_storage_pure(Ok(result));},
    }
}
pub(crate) proof fn part2_plane_single_observed(s:Part1SinglePacketState,payload:Seq<u8>,context:crate::packet::CodeBlockPacketContext,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,header:Part1SinglePacketState,contribution:Part1CodeBlockContribution,offset:usize,decoded:HtCodeBlockBodyResult)
    requires part2_plane_single_admit(s,payload,context,header_limit,work)==(Ok(Some((contribution,offset))),header),
        part2_plane_body_transaction_result(header.decoder,contribution,payload.subrange(offset as int,payload.len() as int),pass_limit,byte_limit,input_limit,work,decoded),
    ensures part2_plane_single_result(s,payload,context,header_limit,pass_limit,byte_limit,input_limit,work,part2_plane_single_finish(header,decoded)),
{
    let body=payload.subrange(offset as int,payload.len() as int);let result=part2_plane_single_finish(header,decoded);
    part2_plane_body_transaction_frames(header.decoder,contribution,body,pass_limit,byte_limit,input_limit,work,decoded);part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_plane_body_transaction_run(header.decoder,contribution,body,pass_limit,byte_limit,input_limit,work,calls),
        |decoded:HtCodeBlockBodyResult,rest|Some((Ok(part2_plane_single_finish(header,decoded)),rest)),Ok(decoded),Ok(result));
}
}
