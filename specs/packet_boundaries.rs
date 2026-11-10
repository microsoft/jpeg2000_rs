use super::*;
use vstd::prelude::*;

verus! {

pub struct Part1SinglePacketState {
    pub state:Part1CodeBlockPacketState,
    pub inclusion:Part1TagTree,
    pub zero:Part1TagTree,
    pub decoder:Tier1DecoderState,
}

pub type Part1SinglePacketResult=(Result<Option<crate::packet::CodeBlockBodyDecode>,crate::DecodeError>,Part1SinglePacketState);

pub struct Part1MultiPacketState {
    pub states:Seq<Part1CodeBlockPacketState>,
    pub inclusion:Part1TagTree,
    pub zero:Part1TagTree,
    pub contexts:Seq<crate::packet::CodeBlockPacketContext>,
    pub decoders:Seq<Tier1DecoderState>,
}

#[verifier::opaque]
pub open spec fn part1_multi_contexts(
    contexts:Seq<crate::packet::CodeBlockPacketContext>,style:crate::tier1::Tier1CodingStyle,
    layer:u16,width:u32,index:usize,error_offset:usize,
) ->Result<(),crate::DecodeError>
    decreases contexts.len()-index as nat,
{
    if index>=contexts.len() {Ok(())}
    else if index>u32::MAX || width==0 {Err(part1_packet_reader_error(error_offset,crate::MalformedKind::ArithmeticOverflow))}
    else{
        let context=contexts[index as int];
        if context.layer!=layer || context.leaf_x!=(index as u32)%width || context.leaf_y!=(index as u32)/width
            || !part1_packet_styles_equal(context.tier1_style,style) {
            Err(part1_packet_reader_error(error_offset,crate::MalformedKind::InvalidPacketHeader))
        }else if index==usize::MAX {Err(part1_packet_reader_error(error_offset,crate::MalformedKind::ArithmeticOverflow))}
        else{part1_multi_contexts(contexts,style,layer,width,(index+1) as usize,error_offset)}
    }
}

pub open spec fn part1_multi_packet_admission(
    s:Part1MultiPacketState,part:&crate::codestream::TilePartPayload<'_>,offset:usize,
    maximum_blocks:u64,maximum_work:u64,
) ->Result<Seq<u8>,crate::DecodeError> {
    if s.states.len()==0 || s.states.len()!=s.contexts.len() || s.states.len()!=s.decoders.len() {
        Err(part1_packet_reader_error(offset,crate::MalformedKind::InvalidPacketHeader))
    }else if s.states.len() as u64>maximum_blocks {
        Err(part1_packet_reader_limit(crate::Resource::CodeBlocks,maximum_blocks,s.states.len() as u64))
    }else if s.states.len() as u64>maximum_work {
        Err(part1_packet_reader_limit(crate::Resource::WorkUnits,maximum_work,s.states.len() as u64))
    }else if s.inclusion.levels.len()==0 || s.zero.levels.len()==0 {
        Err(part1_packet_reader_error(offset,crate::MalformedKind::InvalidTagTree))
    }else{
        let inclusion=s.inclusion.levels[0];
        let zero=s.zero.levels[0];
        if inclusion.width==0 || inclusion.height==0 {
            Err(part1_packet_reader_error(offset,crate::MalformedKind::InvalidTagTree))
        }else{
            match part1_tag_leaf_count(s.inclusion) {
                Err(error)=>Err(error),
                Ok(n)=>if n!=s.states.len() as u64 {Err(part1_packet_reader_error(offset,crate::MalformedKind::InvalidTagTree))}
                else{match part1_tag_leaf_count(s.zero) {
                    Err(error)=>Err(error),
                    Ok(n)=>if n!=s.states.len() as u64 || inclusion.width!=zero.width || inclusion.height!=zero.height {
                        Err(part1_packet_reader_error(offset,crate::MalformedKind::InvalidTagTree))
                    }else if offset>part.data@.len() {Err(part1_packet_reader_error(offset,crate::MalformedKind::Truncated))}
                    else{match crate::codestream::coding_style_tier1_result(part.coding_style) {
                        Err(error)=>Err(error),
                        Ok(style)=>match part1_multi_contexts(s.contexts,style,s.contexts[0].layer,inclusion.width,0,offset) {
                            Err(error)=>Err(error),
                            Ok(())=>Ok(part.data@.subrange(offset as int,part.data@.len() as int)),
                        },
                    }}
                }}
            }
        }
    }
}

pub open spec fn part1_multi_packet_prefix(
    data:Seq<u8>,sop:bool,offset:usize,header_limit:u64,work_limit:u64,
) ->Result<Part1PrecinctPayloadReader,crate::DecodeError> {
    let prefix=if !sop || data.len()<2 || data[0]!=0xff || data[1]<0x90 {Ok(0usize)}
    else if data.len()<4 {Err(part1_packet_reader_error(offset,crate::MalformedKind::Truncated))}
    else if !part1_sop_valid(data[0],data[1],data[2],data[3]) {Err(part1_packet_reader_error(offset,crate::MalformedKind::InvalidPacketHeader))}
    else if data.len()<6 {Err(part1_packet_reader_error(offset,crate::MalformedKind::Truncated))}
    else{Ok(6usize)};
    match prefix {
        Err(error)=>Err(error),
        Ok(skip)=>{
            let input=data.subrange(skip as int,data.len() as int);
            let first=part1_packet_reader_read(part1_packet_reader_prefix(input,header_limit,work_limit));
            match first.0 {
                Err(error)=>Err(error),
                Ok(present)=>Ok(Part1PrecinctPayloadReader {reader:first.1,packet_data:input,present,sop_bytes:skip}),
            }
        },
    }
}

pub struct Part1MultiPacketHeader {
    pub states:Seq<Part1CodeBlockPacketState>,
    pub inclusion:Part1TagTree,
    pub zero:Part1TagTree,
    pub contexts:Seq<crate::packet::CodeBlockPacketContext>,
    pub contributions:Seq<Option<Part1CodeBlockContribution>>,
    pub reader:Part1PacketReaderState,
    pub index:usize,
    pub count:u32,
}

pub type Part1MultiHeaderResult=(Result<(),crate::DecodeError>,Part1MultiPacketHeader);

pub open spec fn part1_multi_header_slot(s:Part1MultiPacketHeader,error_offset:usize)->Part1MultiHeaderResult {
    if s.index>=s.contexts.len() || s.index>=s.states.len() {
        (Err(part1_packet_reader_error(error_offset,crate::MalformedKind::InvalidPacketHeader)),s)
    }else{
        let decoded=part1_packet_header_decode(s.states[s.index as int],s.inclusion,s.zero,s.contexts[s.index as int],s.reader);
        let s=Part1MultiPacketHeader {
            states:s.states.update(s.index as int,decoded.1),inclusion:decoded.2,zero:decoded.3,reader:decoded.4,..s
        };
        match decoded.0 {
            Err(error)=>(Err(error),s),
            Ok(contribution)=>if contribution.is_some() && s.count==u32::MAX {
                (Err(part1_packet_reader_error(error_offset,crate::MalformedKind::ArithmeticOverflow)),s)
            }else{
                let s=Part1MultiPacketHeader {count:if contribution.is_some(){(s.count+1) as u32}else{s.count},..s};
                if s.index>=s.contributions.len() {(Err(part1_packet_reader_error(error_offset,crate::MalformedKind::InvalidPacketHeader)),s)}
                else{
                    let s=Part1MultiPacketHeader {contributions:s.contributions.update(s.index as int,contribution),..s};
                    if s.index==usize::MAX {(Err(part1_packet_reader_error(error_offset,crate::MalformedKind::ArithmeticOverflow)),s)}
                    else{(Ok(()),Part1MultiPacketHeader {index:(s.index+1) as usize,..s})}
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_multi_headers(s:Part1MultiPacketHeader,error_offset:usize)->Part1MultiHeaderResult
    decreases s.contexts.len()-s.index as nat,
{
    if s.index>=s.contexts.len() {(Ok(()),s)}
    else{
        let step=part1_multi_header_slot(s,error_offset);
        match step.0 {Err(_)=>step,Ok(())=>part1_multi_headers(step.1,error_offset)}
    }
}

pub open spec fn part1_multi_body_start(
    data:Seq<u8>,sop:usize,header:usize,eph:bool,error_offset:usize,
)->Result<usize,crate::DecodeError> {
    if sop as nat+header as nat>usize::MAX {Err(part1_packet_reader_error(error_offset,crate::MalformedKind::ArithmeticOverflow))}
    else{
        let start=(sop+header) as usize;
        if !eph {Ok(start)}
        else if start as nat+2>usize::MAX {Err(part1_packet_reader_error(error_offset,crate::MalformedKind::ArithmeticOverflow))}
        else if start as nat+2>data.len() {Err(part1_packet_reader_error(error_offset,crate::MalformedKind::Truncated))}
        else if !part1_eph_valid(data[start as int],data[start as int+1]) {
            Err(part1_packet_reader_error(error_offset,crate::MalformedKind::InvalidPacketHeader))
        }else{Ok((start+2) as usize)}
    }
}

pub type Part1MultiPacketResult=(Result<crate::packet::PacketBodyDecode,crate::DecodeError>,Part1MultiPacketState);

pub open spec fn part1_multi_summary(
    blocks:u64,present:bool,count:u32,header:usize,start:usize,end:usize,segments:u32,passes:u32,offset:usize,
)->Result<crate::packet::PacketBodyDecode,crate::DecodeError> {
    if end<start || blocks>u32::MAX || header>u32::MAX
        || end-start>u32::MAX || end>u32::MAX {
        Err(part1_packet_reader_error(offset,crate::MalformedKind::ArithmeticOverflow))
    }else{Ok(crate::packet::PacketBodyDecode {
        present,code_blocks:blocks as u32,contributions:count,segments,passes,
        header_bytes:header as u32,body_bytes:(end-start) as u32,bytes_consumed:end as u32,
    })}
}

#[verifier::opaque]
pub open spec fn part1_multi_body(
    state:Part1MultiPacketState,data:Seq<u8>,contributions:Seq<Option<Part1CodeBlockContribution>>,
    present:bool,count:u32,header:usize,start:usize,offset:usize,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
)->Part1MultiPacketResult {
    let decoded=part1_multi_body_data(state.decoders,state.states.len() as u64,data,contributions,
        present,count,header,start,offset,pass_limit,byte_limit,input_limit,work_limit);
    (decoded.0,Part1MultiPacketState {decoders:decoded.1,..state})
}

pub open spec fn part1_multi_body_data(
    decoders:Seq<Tier1DecoderState>,blocks:u64,data:Seq<u8>,contributions:Seq<Option<Part1CodeBlockContribution>>,
    present:bool,count:u32,header:usize,start:usize,offset:usize,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
)->(Result<crate::packet::PacketBodyDecode,crate::DecodeError>,Seq<Tier1DecoderState>) {
    let preflight=part1_packet_body_preflight_at(Part1PacketBodyPreflight {index:0,end:start},contributions,data,offset,offset);
    match preflight.0 {
        Err(error)=>(Err(error),decoders),
        Ok(())=>{
            let executed=part1_packet_body_execute_at(Part1PacketBodyExecution {
                decoders,index:0,offset:start,segments:0,passes:0,
            },contributions,data,offset,offset,true,pass_limit,byte_limit,input_limit,work_limit);
            match executed.0 {
                Err(error)=>(Err(error),executed.1.decoders),
                Ok(())=>(part1_multi_summary(blocks,present,count,header,start,preflight.1.end,executed.1.segments,executed.1.passes,offset),
                    executed.1.decoders),
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_multi_payload(
    state:Part1MultiPacketState,data:Seq<u8>,sop:bool,eph:bool,offset:usize,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
)->Part1MultiPacketResult {
    match part1_multi_packet_prefix(data,sop,offset,header_limit,work_limit) {
        Err(error)=>(Err(error),state),
        Ok(prefix)=>{
            let initial=Part1MultiPacketHeader {
                states:state.states,inclusion:state.inclusion,zero:state.zero,contexts:state.contexts,
                contributions:Seq::new(state.states.len(),|i:int|None),reader:prefix.reader,index:0,count:0,
            };
            let headers=if prefix.present {part1_multi_headers(initial,offset)}else{(Ok(()),initial)};
            let state=Part1MultiPacketState {states:headers.1.states,inclusion:headers.1.inclusion,zero:headers.1.zero,..state};
            match headers.0 {
                Err(error)=>(Err(error),state),
                Ok(())=>{
                    let finished=part1_packet_reader_finish(headers.1.reader);
                    match finished.0 {
                        Err(error)=>(Err(error),state),
                        Ok(())=>match part1_multi_body_start(data,prefix.sop_bytes,finished.1.byte_index,eph,offset) {
                            Err(error)=>(Err(error),state),
                            Ok(start)=>part1_multi_body(state,data,headers.1.contributions,prefix.present,headers.1.count,
                                finished.1.byte_index,start,offset,pass_limit,byte_limit,input_limit,work_limit),
                        },
                    }
                },
            }
        },
    }
}

pub open spec fn part1_multi_code_block_packet(
    state:Part1MultiPacketState,part:&crate::codestream::TilePartPayload<'_>,offset:usize,limits:&crate::ResourceLimits,
)->Part1MultiPacketResult {
    match part1_multi_packet_admission(state,part,offset,crate::limits::resource_code_block_limit(limits),crate::limits::resource_work_limit(limits)) {
        Err(error)=>(Err(error),state),
        Ok(data)=>{
            let markers=crate::codestream::coding_style_packet_markers(&part.coding_style);
            part1_multi_payload(state,data,markers.0,markers.1,offset,
                crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),
                crate::limits::resource_work_limit(limits))
        },
    }
}

pub open spec fn part1_single_packet_body(
    s:Part1SinglePacketState,payload:Seq<u8>,reader:Part1PacketReaderState,contribution:Part1CodeBlockContribution,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
) ->Part1SinglePacketResult {
    let offset=reader.byte_index;
    if offset>payload.len() {(Err(part1_packet_reader_error(offset,crate::MalformedKind::Truncated)),s)}
    else {
        let body=part1_code_block_body_transaction(s.decoder,contribution,
            payload.subrange(offset as int,payload.len() as int),pass_limit,byte_limit,input_limit,work_limit);
        (match body.0 {Err(error)=>Err(error),Ok(decoded)=>Ok(Some(decoded))},
            Part1SinglePacketState {decoder:body.1,..s})
    }
}

pub open spec fn part1_single_packet_present(
    s:Part1SinglePacketState,payload:Seq<u8>,reader:Part1PacketReaderState,context:crate::packet::CodeBlockPacketContext,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
) ->Part1SinglePacketResult {
    let header=part1_packet_header_decode(s.state,s.inclusion,s.zero,context,reader);
    let s=Part1SinglePacketState {state:header.1,inclusion:header.2,zero:header.3,..s};
    match header.0 {
        Err(error)=>(Err(error),s),
        Ok(None)=>(Err(part1_packet_reader_error(header.4.byte_index,crate::MalformedKind::InvalidPacketHeader)),s),
        Ok(Some(contribution))=>{
            let finished=part1_packet_reader_finish(header.4);
            match finished.0 {
                Err(error)=>(Err(error),s),
                Ok(())=>part1_single_packet_body(s,payload,finished.1,contribution,
                    pass_limit,byte_limit,input_limit,work_limit),
            }
        },
    }
}

pub open spec fn part1_single_code_block_packet(
    s:Part1SinglePacketState,payload:Seq<u8>,context:crate::packet::CodeBlockPacketContext,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
) ->Part1SinglePacketResult {
    match part1_packet_reader_initial(payload,header_limit,work_limit) {
        Err(error)=>(Err(error),s),
        Ok(reader)=>{
            let first=part1_packet_reader_read(reader);
            match first.0 {
                Err(error)=>(Err(error),s),
                Ok(false)=>{
                    let finished=part1_packet_reader_finish(first.1);
                    match finished.0 {
                        Err(error)=>(Err(error),s),
                        Ok(())=>if finished.1.byte_index!=payload.len() {
                            (Err(part1_packet_reader_error(finished.1.byte_index,crate::MalformedKind::TrailingData)),s)
                        }else{(Ok(None),s)},
                    }
                },
                Ok(true)=>part1_single_packet_present(s,payload,first.1,context,pass_limit,byte_limit,input_limit,work_limit),
            }
        },
    }
}

pub open spec fn part1_jpip_precinct_packet_inner(
    state:Part1PacketPrecinctState,template:&crate::codestream::TilePartPayload<'_>,
    data:Seq<u8>,sequence:u16,layer:u16,limits:&crate::ResourceLimits,
) ->(Result<usize,crate::DecodeError>,Part1PacketPrecinctState) {
    let state=part1_precinct_context_layer(state,layer);
    let packet=part1_precinct_packet_fields(state,data,&template.component_coding_styles,&template.coding_style,false,
        0,Seq::empty(),0,None,sequence,false,crate::limits::resource_code_block_limit(limits),
        crate::limits::resource_packet_header_byte_limit(limits),crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),
        crate::limits::resource_work_limit(limits));
    match packet.0 {
        Err(error)=>(Err(error),packet.1),
        Ok((decoded,consumed,packed))=>if packed!=0 {(Err(part1_packet_reader_error(0,crate::MalformedKind::InvalidPacketLength)),packet.1)}
        else if decoded.bytes_consumed as nat>usize::MAX {(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),packet.1)}
        else if consumed!=decoded.bytes_consumed as nat {(Err(part1_packet_reader_error(0,crate::MalformedKind::InvalidPacketLength)),packet.1)}
        else{(Ok(consumed),packet.1)},
    }
}

pub open spec fn part1_jpip_precinct_packet(
    state:Part1PacketPrecinctState,template:&crate::codestream::TilePartPayload<'_>,
    data:Seq<u8>,sequence:u16,layer:u16,limits:&crate::ResourceLimits,
) ->(Result<usize,crate::DecodeError>,Part1PacketPrecinctState) {
    let result=part1_jpip_precinct_packet_inner(state,template,data,sequence,layer,limits);
    if result.0.is_err() {(result.0,state)}else{result}
}

}
