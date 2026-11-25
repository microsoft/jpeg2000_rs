use super::*;
verus! {

pub struct PrivatePacketBodyExecution {
    pub logical:Part1PacketBodyExecution,
    pub packed:Seq<bool>,
}

pub type PrivatePacketBodyEffect=(Result<(),crate::DecodeError>,PrivatePacketBodyExecution);
pub type PrivatePrecinctPacketEffect=(Result<(crate::packet::PacketBodyDecode,usize,usize),crate::DecodeError>,PrivateHtPrecinctState);

pub struct PrivatePrecinctPacketContext {
    pub before:PrivateHtPrecinctState,pub part:Part2OwnedTilePart,pub offset:usize,pub sequence:u16,
    pub caps:(u64,u64,u32,u64,u64,u64),
}

pub(crate) open spec fn private_packet_body_wf(state:PrivatePacketBodyExecution)->bool {
    state.packed.len()==state.logical.decoders.len()
        && forall|i:int|0<=i<state.logical.decoders.len() ==>
            #[trigger] private_ht_state_wf(PrivateHtDecoderState {
                logical:state.logical.decoders[i],packed:state.packed[i],
            })
}

pub(crate) open spec fn private_packet_after_body(before:PrivatePacketBodyExecution,
    header:Part1CodeBlockContribution,decoded:PrivateHtBodyEffect)->PrivatePacketBodyEffect {
    let finished=part2_plane_execute_finish(before.logical,header,0,(decoded.0,decoded.1.logical));
    (finished.0,PrivatePacketBodyExecution {
        logical:finished.1,packed:before.packed.update(before.logical.index as int,decoded.1.packed),
    })
}

pub(crate) open spec fn private_packet_slot_value(before:PrivatePacketBodyExecution,header:Part1CodeBlockContribution,
    data:Seq<u8>,error:usize,passes:u32,bytes:u64,input:u64,work:u64)->PrivatePacketBodyEffect {
    if !part2_plane_execute_admit(before.logical,header,data,true) {
        let result=part1_packet_body_execute_slot_at(before.logical,header,data,error,0,true,passes,bytes,input,work);
        (result.0,PrivatePacketBodyExecution{logical:result.1,packed:before.packed})
    }else{
        let state=PrivateHtDecoderState {
            logical:before.logical.decoders[before.logical.index as int],packed:before.packed[before.logical.index as int],
        };
        let body=data.subrange(before.logical.offset as int,before.logical.offset as int+header.data_length as int);
        private_packet_after_body(before,header,private_ht_body_value(state,header,body,passes,bytes,input,work))
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_packet_slot_run(before:PrivatePacketBodyExecution,header:Part1CodeBlockContribution,
    data:Seq<u8>,error:usize,passes:u32,bytes:u64,input:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<PrivatePacketBodyEffect> {
    if !part2_plane_execute_admit(before.logical,header,data,true) {
        Some((Ok(private_packet_slot_value(before,header,data,error,passes,bytes,input,work)),calls))
    }else{
        let state=PrivateHtDecoderState {
            logical:before.logical.decoders[before.logical.index as int],packed:before.packed[before.logical.index as int],
        };
        let body=data.subrange(before.logical.offset as int,before.logical.offset as int+header.data_length as int);
        part2_tier1_storage_bind(private_ht_body_run(state,header,body,passes,bytes,input,work,calls),
            |decoded:PrivateHtBodyEffect,rest|Some((Ok(private_packet_after_body(before,header,decoded)),rest)))
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_packet_body_run(before:PrivatePacketBodyExecution,
    contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,
    passes:u32,bytes:u64,input:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<PrivatePacketBodyEffect>
    decreases if before.logical.index<contributions.len(){((contributions.len()-before.logical.index as nat)*2+1) as nat}else{0nat},
{
    if before.logical.index>=contributions.len(){Some((Ok((Ok(()),before)),calls))}
    else{
        let slot=match contributions[before.logical.index as int] {
            None=>Some((Ok((Ok(()),before)),calls)),
            Some(header)=>private_packet_slot_run(before,header,data,error,passes,bytes,input,work,calls),
        };
        part2_tier1_storage_bind(slot,|step:PrivatePacketBodyEffect,rest|
            private_packet_body_next(step,before.logical.index,contributions,data,error,passes,bytes,input,work,rest))
    }
}

pub(crate) open spec fn private_packet_body_next(step:PrivatePacketBodyEffect,index:usize,
    contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,
    passes:u32,bytes:u64,input:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<PrivatePacketBodyEffect>
    decreases if index<contributions.len(){((contributions.len()-index as nat)*2) as nat}else{0nat},
{
    if step.1.logical.index!=index{None}else{
    match step.0 {
        Err(_)=>Some((Ok(step),calls)),
        Ok(())=>if step.1.logical.index==usize::MAX {
            Some((Ok((Err(part1_packet_reader_error(0,crate::MalformedKind::ArithmeticOverflow)),step.1)),calls))
        }else if step.1.logical.index>=contributions.len(){Some((Ok(step),calls))}
        else{private_packet_body_run(PrivatePacketBodyExecution {
            logical:Part1PacketBodyExecution{index:(step.1.logical.index+1) as usize,..step.1.logical},packed:step.1.packed,
        },contributions,data,error,passes,bytes,input,work,calls)},
    }}
}

#[verifier::opaque]
pub(crate) open spec fn private_packet_body_value(before:PrivatePacketBodyExecution,
    contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,
    passes:u32,bytes:u64,input:u64,work:u64)->PrivatePacketBodyEffect
    decreases contributions.len()-before.logical.index as nat,
{
    if before.logical.index>=contributions.len(){(Ok(()),before)}
    else{
        let step=match contributions[before.logical.index as int] {
            None=>(Ok(()),before),
            Some(header)=>private_packet_slot_value(before,header,data,error,passes,bytes,input,work),
        };
        match step.0 {
            Err(_)=>step,
            Ok(())=>if step.1.logical.index==usize::MAX {
                (Err(part1_packet_reader_error(0,crate::MalformedKind::ArithmeticOverflow)),step.1)
            }else{private_packet_body_value(PrivatePacketBodyExecution{
                logical:Part1PacketBodyExecution{index:(step.1.logical.index+1) as usize,..step.1.logical},packed:step.1.packed,
            },contributions,data,error,passes,bytes,input,work)},
        }
    }
}

pub(crate) open spec fn private_packet_body_result(before:PrivatePacketBodyExecution,
    contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,
    passes:u32,bytes:u64,input:u64,work:u64,result:PrivatePacketBodyEffect)->bool {
    part2_tier1_storage_framed(|calls|private_packet_body_run(before,contributions,data,error,passes,bytes,input,work,calls),Ok(result))
}

pub(crate) proof fn private_packet_slot_observed(before:PrivatePacketBodyExecution,header:Part1CodeBlockContribution,
    data:Seq<u8>,error:usize,passes:u32,bytes:u64,input:u64,work:u64,decoded:PrivateHtBodyEffect)
    requires part2_plane_execute_admit(before.logical,header,data,true),
        private_ht_body_result(PrivateHtDecoderState {
            logical:before.logical.decoders[before.logical.index as int],packed:before.packed[before.logical.index as int],
        },header,data.subrange(before.logical.offset as int,before.logical.offset as int+header.data_length as int),
            passes,bytes,input,work,decoded),
    ensures part2_tier1_storage_framed(|calls|private_packet_slot_run(before,header,data,error,passes,bytes,input,work,calls),
        Ok(private_packet_after_body(before,header,decoded))),
{
    reveal(private_packet_slot_run);
    let source=PrivateHtDecoderState {
        logical:before.logical.decoders[before.logical.index as int],packed:before.packed[before.logical.index as int],
    };
    part2_tier1_storage_pure(Ok(private_packet_after_body(before,header,decoded)));
    part2_tier1_storage_bind_frame(|calls|private_ht_body_run(source,header,
        data.subrange(before.logical.offset as int,before.logical.offset as int+header.data_length as int),
        passes,bytes,input,work,calls),
        |actual,rest|Some((Ok(private_packet_after_body(before,header,actual)),rest)),
        Ok(decoded),Ok(private_packet_after_body(before,header,decoded)));
}

pub(crate) open spec fn private_packet_prefix(initial:PrivatePacketBodyExecution,current:PrivatePacketBodyExecution,
    contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,
    passes:u32,bytes:u64,input:u64,work:u64,prefix:Seq<Part2Tier1StorageEvent>)->bool {
    forall|tail| #[trigger] private_packet_body_run(initial,contributions,data,error,passes,bytes,input,work,prefix+tail)
        ==private_packet_body_run(current,contributions,data,error,passes,bytes,input,work,tail)
}

pub(crate) proof fn private_packet_step(initial:PrivatePacketBodyExecution,current:PrivatePacketBodyExecution,
    contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,
    passes:u32,bytes:u64,input:u64,work:u64,prefix:Seq<Part2Tier1StorageEvent>,step:PrivatePacketBodyEffect)
    ->(extended:Seq<Part2Tier1StorageEvent>)
    requires current.logical.index<contributions.len(),
        private_packet_prefix(initial,current,contributions,data,error,passes,bytes,input,work,prefix),
        step.1.logical.index==current.logical.index,
        match contributions[current.logical.index as int] {
            None=>step==(Ok(()),current),
            Some(header)=>part2_tier1_storage_framed(|calls|private_packet_slot_run(current,header,data,error,passes,bytes,input,work,calls),Ok(step)),
        },
    ensures step.0.is_err() ==> private_packet_body_result(initial,contributions,data,error,passes,bytes,input,work,step),
        step.0.is_ok() && current.logical.index<usize::MAX ==> private_packet_prefix(initial,PrivatePacketBodyExecution {
            logical:Part1PacketBodyExecution{index:(current.logical.index+1) as usize,..step.1.logical},packed:step.1.packed,
        },contributions,data,error,passes,bytes,input,work,extended),
{
    reveal_with_fuel(private_packet_body_run,2);reveal_with_fuel(private_packet_body_next,1);
    private_unit_result_fields(step.0);
    let child=|calls|match contributions[current.logical.index as int]{
        None=>Some((Ok((Ok(()),current)),calls)),
        Some(header)=>private_packet_slot_run(current,header,data,error,passes,bytes,input,work,calls),
    };
    if contributions[current.logical.index as int].is_none(){part2_tier1_storage_pure::<PrivatePacketBodyEffect>(Ok((Ok(()),current)));}
    if let Some(header)=contributions[current.logical.index as int]{
        part2_tier1_storage_eta(|calls|private_packet_slot_run(current,header,data,error,passes,bytes,input,work,calls),Ok(step));
    }
    assert(part2_tier1_storage_framed(child,Ok(step)));
    let calls=choose|calls:Seq<Part2Tier1StorageEvent>| #[trigger] part2_tier1_storage_prefix(child,calls,Ok(step));
    assert forall|tail|private_packet_body_run(initial,contributions,data,error,passes,bytes,input,work,(prefix+calls)+tail)
        ==private_packet_body_next(step,current.logical.index,contributions,data,error,passes,bytes,input,work,tail) by {
        assert((prefix+calls)+tail =~=prefix+(calls+tail));
        part2_tier1_storage_at(child,calls,Ok(step),tail);
    }
    if step.0.is_err(){
        assert forall|tail|private_packet_body_run(initial,contributions,data,error,passes,bytes,input,work,(prefix+calls)+tail)==Some((Ok(step),tail)) by {
            assert(private_packet_body_run(initial,contributions,data,error,passes,bytes,input,work,(prefix+calls)+tail)
                ==private_packet_body_next(step,current.logical.index,contributions,data,error,passes,bytes,input,work,tail));
        }
        assert(part2_tier1_storage_prefix(|tail|private_packet_body_run(initial,contributions,data,error,passes,bytes,input,work,tail),prefix+calls,Ok(step)));
    }else if current.logical.index<usize::MAX{
        let after=PrivatePacketBodyExecution {
            logical:Part1PacketBodyExecution{index:(current.logical.index+1) as usize,..step.1.logical},packed:step.1.packed,
        };
        assert forall|tail|private_packet_body_run(initial,contributions,data,error,passes,bytes,input,work,(prefix+calls)+tail)==
            private_packet_body_run(after,contributions,data,error,passes,bytes,input,work,tail) by {
            assert(private_packet_body_run(initial,contributions,data,error,passes,bytes,input,work,(prefix+calls)+tail)==
                private_packet_body_next(step,current.logical.index,contributions,data,error,passes,bytes,input,work,tail));
        }
        assert(private_packet_prefix(initial,after,contributions,data,error,passes,bytes,input,work,prefix+calls));
    }
    prefix+calls
}

pub(crate) proof fn private_packet_finish(initial:PrivatePacketBodyExecution,current:PrivatePacketBodyExecution,
    contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,
    passes:u32,bytes:u64,input:u64,work:u64,prefix:Seq<Part2Tier1StorageEvent>)
    requires current.logical.index>=contributions.len(),
        private_packet_prefix(initial,current,contributions,data,error,passes,bytes,input,work,prefix),
    ensures private_packet_body_result(initial,contributions,data,error,passes,bytes,input,work,(Ok(()),current)),
{
    reveal_with_fuel(private_packet_body_run,1);
    assert(part2_tier1_storage_prefix(|calls|private_packet_body_run(initial,contributions,data,error,passes,bytes,input,work,calls),prefix,Ok((Ok(()),current))));
}

pub(crate) proof fn private_packet_scalar_error(initial:PrivatePacketBodyExecution,current:PrivatePacketBodyExecution,
    contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error_offset:usize,
    passes:u32,bytes:u64,input:u64,work:u64,prefix:Seq<Part2Tier1StorageEvent>,
    header:Part1CodeBlockContribution,error:crate::DecodeError)
    requires current.logical.index<contributions.len(),
        contributions[current.logical.index as int]==Some(header),
        private_packet_prefix(initial,current,contributions,data,error_offset,passes,bytes,input,work,prefix),
        !part2_plane_execute_admit(current.logical,header,data,true),
        part1_packet_body_execute_slot_at(current.logical,header,data,error_offset,0,true,passes,bytes,input,work)==(Err(error),current.logical),
    ensures private_packet_body_result(initial,contributions,data,error_offset,passes,bytes,input,work,(Err(error),current)),
{
    reveal(private_packet_slot_run);
    part2_tier1_storage_pure::<PrivatePacketBodyEffect>(Ok((Err(error),current)));
    let extended=private_packet_step(initial,current,contributions,data,error_offset,passes,bytes,input,work,prefix,(Err(error),current));
}

pub(crate) proof fn private_packet_slot_value_fields(before:PrivatePacketBodyExecution,header:Part1CodeBlockContribution,
    data:Seq<u8>,error:usize,passes:u32,bytes:u64,input:u64,work:u64)
    requires private_packet_body_wf(before),
    ensures private_packet_body_wf(private_packet_slot_value(before,header,data,error,passes,bytes,input,work).1),
        (private_packet_slot_value(before,header,data,error,passes,bytes,input,work).0,
            private_packet_slot_value(before,header,data,error,passes,bytes,input,work).1.logical)
            ==part1_packet_body_execute_slot_at(before.logical,header,data,error,0,true,passes,bytes,input,work),
{
    if part2_plane_execute_admit(before.logical,header,data,true) {
        private_ht_body_value_fields(PrivateHtDecoderState {
            logical:before.logical.decoders[before.logical.index as int],packed:before.packed[before.logical.index as int],
        },header,data.subrange(before.logical.offset as int,before.logical.offset as int+header.data_length as int),
            passes,bytes,input,work);
    }
}

pub(crate) proof fn private_packet_slot_normal(before:PrivatePacketBodyExecution,header:Part1CodeBlockContribution,
    data:Seq<u8>,error:usize,passes:u32,bytes:u64,input:u64,work:u64)
    requires private_packet_body_wf(before),
    ensures part2_tier1_storage_framed(|calls|private_packet_slot_run(before,header,data,error,passes,bytes,input,work,calls),
        Ok(private_packet_slot_value(before,header,data,error,passes,bytes,input,work))),
{
    reveal(private_packet_slot_run);
    if !part2_plane_execute_admit(before.logical,header,data,true){
        part2_tier1_storage_pure(Ok(private_packet_slot_value(before,header,data,error,passes,bytes,input,work)));
    }else{
        let decoder=PrivateHtDecoderState{logical:before.logical.decoders[before.logical.index as int],packed:before.packed[before.logical.index as int]};
        let body=data.subrange(before.logical.offset as int,before.logical.offset as int+header.data_length as int);
        private_ht_body_normal(PrivateHtBodyContext{before:decoder,header,body,passes,bytes,input,work});
        private_packet_slot_observed(before,header,data,error,passes,bytes,input,work,
            private_ht_body_value(decoder,header,body,passes,bytes,input,work));
    }
}

pub(crate) proof fn private_packet_body_normal(before:PrivatePacketBodyExecution,contributions:Seq<Option<Part1CodeBlockContribution>>,
    data:Seq<u8>,error:usize,passes:u32,bytes:u64,input:u64,work:u64)
    requires private_packet_body_wf(before),
    ensures private_packet_body_result(before,contributions,data,error,passes,bytes,input,work,
        private_packet_body_value(before,contributions,data,error,passes,bytes,input,work)),
    decreases contributions.len()-before.logical.index as nat,
{
    reveal_with_fuel(private_packet_body_run,2);reveal_with_fuel(private_packet_body_next,1);reveal_with_fuel(private_packet_body_value,1);
    let result=private_packet_body_value(before,contributions,data,error,passes,bytes,input,work);
    if before.logical.index>=contributions.len(){part2_tier1_storage_pure(Ok(result));}else{
        let step=match contributions[before.logical.index as int]{
            None=>(Ok(()),before),Some(header)=>{
                private_packet_slot_normal(before,header,data,error,passes,bytes,input,work);
                private_packet_slot_value_fields(before,header,data,error,passes,bytes,input,work);
                private_packet_slot_value(before,header,data,error,passes,bytes,input,work)
            },
        };
        let child=|calls|match contributions[before.logical.index as int]{
            None=>Some((Ok((Ok(()),before)),calls)),Some(header)=>private_packet_slot_run(before,header,data,error,passes,bytes,input,work,calls),
        };
        private_unit_result_fields(step.0);
        if contributions[before.logical.index as int].is_none(){part2_tier1_storage_pure(Ok(step));}
        if let Some(header)=contributions[before.logical.index as int]{
            part2_tier1_storage_eta(|calls|private_packet_slot_run(before,header,data,error,passes,bytes,input,work,calls),Ok(step));
        }
        if step.0.is_err() || step.1.logical.index==usize::MAX{part2_tier1_storage_pure(Ok(result));}else{
            let after=PrivatePacketBodyExecution{
                logical:Part1PacketBodyExecution{index:(step.1.logical.index+1) as usize,..step.1.logical},packed:step.1.packed,
            };
            private_packet_body_normal(after,contributions,data,error,passes,bytes,input,work);
            part2_tier1_storage_eta(|calls|private_packet_body_run(after,contributions,data,error,passes,bytes,input,work,calls),Ok(result));
        }
        part2_tier1_storage_bind_frame(child,|value,rest|private_packet_body_next(value,before.logical.index,contributions,data,error,passes,bytes,input,work,rest),
            Ok(step),Ok(result));
    }
}

pub(crate) proof fn private_packet_body_value_fields(before:PrivatePacketBodyExecution,
    contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,
    passes:u32,bytes:u64,input:u64,work:u64)
    requires private_packet_body_wf(before),
    ensures private_packet_body_wf(private_packet_body_value(before,contributions,data,error,passes,bytes,input,work).1),
        (private_packet_body_value(before,contributions,data,error,passes,bytes,input,work).0,
            private_packet_body_value(before,contributions,data,error,passes,bytes,input,work).1.logical)
            ==part1_packet_body_execute_at(before.logical,contributions,data,error,0,true,passes,bytes,input,work),
    decreases contributions.len()-before.logical.index as nat,
{
    reveal_with_fuel(private_packet_body_value,1);reveal_with_fuel(part1_packet_body_execute_at,1);
    if before.logical.index<contributions.len(){
        let step=match contributions[before.logical.index as int] {
            None=>(Ok(()),before),
            Some(header)=>{
                private_packet_slot_value_fields(before,header,data,error,passes,bytes,input,work);
                private_packet_slot_value(before,header,data,error,passes,bytes,input,work)
            },
        };
        if step.0.is_ok() && step.1.logical.index<usize::MAX {
            private_packet_body_value_fields(PrivatePacketBodyExecution {
                logical:Part1PacketBodyExecution{index:(step.1.logical.index+1) as usize,..step.1.logical},packed:step.1.packed,
            },contributions,data,error,passes,bytes,input,work);
        }
    }
}

    pub(crate) open spec fn private_payload_finish(state:PrivateHtPrecinctState,parameters:Part1PrecinctPayloadParameters,
        header:Part2PlanePayloadHeader,args:(usize,usize,usize,usize),executed:PrivatePacketBodyEffect)->PrivatePrecinctPacketEffect {
        let finished=part2_plane_payload_finish(state.logical,parameters,header.present,header.count,args,
            (executed.0,executed.1.logical));
        (finished.0,PrivateHtPrecinctState{logical:finished.1,packed:executed.1.packed})
    }

    pub(crate) open spec fn private_payload_after_run(state:PrivateHtPrecinctState,parameters:Part1PrecinctPayloadParameters,
        data:Seq<u8>,header:Part2PlanePayloadHeader,caps:(u64,u64,u32,u64,u64,u64),calls:Seq<Part2Tier1StorageEvent>)
        ->Part2Tier1Run<PrivatePrecinctPacketEffect> {
        match part2_plane_payload_admit(parameters,data,header.packet,header.reader,header.contributions,header.sop){
            Err(error)=>Some((Ok((Err(error),state)),calls)),
            Ok(args)=>part2_tier1_storage_bind(private_packet_body_run(PrivatePacketBodyExecution{
                logical:Part1PacketBodyExecution{decoders:state.logical.decoders,index:0,offset:args.1,segments:0,passes:0},
                packed:state.packed,
            },header.contributions,data,parameters.error_offset,caps.2,caps.3,caps.4,caps.5,calls),
                |executed:PrivatePacketBodyEffect,rest|Some((Ok(private_payload_finish(state,parameters,header,args,executed)),rest))),
        }
    }

    pub(crate) open spec fn private_payload_after_value(state:PrivateHtPrecinctState,parameters:Part1PrecinctPayloadParameters,
        data:Seq<u8>,header:Part2PlanePayloadHeader,caps:(u64,u64,u32,u64,u64,u64))->PrivatePrecinctPacketEffect {
        match part2_plane_payload_admit(parameters,data,header.packet,header.reader,header.contributions,header.sop){
            Err(error)=>(Err(error),state),
            Ok(args)=>private_payload_finish(state,parameters,header,args,
                private_packet_body_value(PrivatePacketBodyExecution{
                    logical:Part1PacketBodyExecution{decoders:state.logical.decoders,index:0,offset:args.1,segments:0,passes:0},
                    packed:state.packed,
                },header.contributions,data,parameters.error_offset,caps.2,caps.3,caps.4,caps.5)),
        }
    }

    pub(crate) open spec fn private_payload_prepared_run(state:PrivateHtPrecinctState,data:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
        caps:(u64,u64,u32,u64,u64,u64),calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<PrivatePrecinctPacketEffect> {
        let headers=part2_plane_payload_headers(state.logical,data,Seq::empty(),parameters,caps.1,caps.5);
        let after=PrivateHtPrecinctState{logical:headers.1,packed:state.packed};
        match headers.0{
            Err(error)=>Some((Ok((Err(error),after)),calls)),
            Ok(header)=>private_payload_after_run(after,parameters,data,header,caps,calls),
        }
    }

    pub(crate) open spec fn private_payload_run(state:PrivateHtPrecinctState,data:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
        caps:(u64,u64,u32,u64,u64,u64),calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<PrivatePrecinctPacketEffect> {
        match part1_precinct_payload_prefix(data,Seq::empty(),parameters,caps.1,caps.5){
            Err(error)=>Some((Ok((Err(error),state)),calls)),
            Ok(_)=>part2_tier1_storage_resume(part2_precinct_contributions_run(Part2PrecinctContributionsContext{
                state:state.logical,data,packed:Seq::empty(),parameters,header_limit:caps.1,work:caps.5,
            },calls),|capacity:Result<(),crate::DecodeError>,rest|match capacity{
                Err(error)=>Some((Ok((Err(error),state)),rest)),
                Ok(())=>private_payload_prepared_run(state,data,parameters,caps,rest),
            }),
        }
    }

    pub(crate) open spec fn private_precinct_packet_run(ctx:PrivatePrecinctPacketContext,calls:Seq<Part2Tier1StorageEvent>)
        ->Part2Tier1Run<PrivatePrecinctPacketEffect> {
        match part2_plane_precinct_admit(ctx.before.logical,ctx.part,ctx.offset,0,None,ctx.sequence,true,ctx.caps.0,ctx.caps.5){
            Err(error)=>Some((Ok((Err(error),ctx.before)),calls)),
            Ok(parameters)=>private_payload_run(ctx.before,ctx.part.data.subrange(ctx.offset as int,ctx.part.data.len() as int),parameters,ctx.caps,calls),
        }
    }

    pub(crate) open spec fn private_precinct_packet_result(ctx:PrivatePrecinctPacketContext,result:PrivatePrecinctPacketEffect)->bool {
        part2_tier1_storage_framed(|calls|private_precinct_packet_run(ctx,calls),Ok(result))
    }

    pub(crate) open spec fn private_precinct_packet_value(ctx:PrivatePrecinctPacketContext)->PrivatePrecinctPacketEffect {
        match part2_plane_precinct_admit(ctx.before.logical,ctx.part,ctx.offset,0,None,ctx.sequence,true,ctx.caps.0,ctx.caps.5){
            Err(error)=>(Err(error),ctx.before),
            Ok(parameters)=>{
                let data=ctx.part.data.subrange(ctx.offset as int,ctx.part.data.len() as int);
                let headers=part2_plane_payload_headers(ctx.before.logical,data,Seq::empty(),parameters,ctx.caps.1,ctx.caps.5);
                let after=PrivateHtPrecinctState{logical:headers.1,packed:ctx.before.packed};
                match headers.0{Err(error)=>(Err(error),after),Ok(header)=>private_payload_after_value(after,parameters,data,header,ctx.caps)}
            },
        }
    }

    pub(crate) open spec fn private_payload_result(state:PrivateHtPrecinctState,data:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
        caps:(u64,u64,u32,u64,u64,u64),result:PrivatePrecinctPacketEffect)->bool {
        part2_tier1_storage_framed(|calls|private_payload_run(state,data,parameters,caps,calls),Ok(result))
    }

    pub(crate) open spec fn private_payload_value(state:PrivateHtPrecinctState,data:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
        caps:(u64,u64,u32,u64,u64,u64))->PrivatePrecinctPacketEffect {
        let prepared=part2_plane_payload_headers(state.logical,data,Seq::empty(),parameters,caps.1,caps.5);
        let after=PrivateHtPrecinctState{logical:prepared.1,packed:state.packed};
        match prepared.0 {Err(error)=>(Err(error),after),Ok(header)=>private_payload_after_value(after,parameters,data,header,caps)}
    }

    pub(crate) open spec fn private_payload_after_result(state:PrivateHtPrecinctState,parameters:Part1PrecinctPayloadParameters,
        data:Seq<u8>,header:Part2PlanePayloadHeader,caps:(u64,u64,u32,u64,u64,u64),result:PrivatePrecinctPacketEffect)->bool {
        part2_tier1_storage_framed(|calls|private_payload_after_run(state,parameters,data,header,caps,calls),Ok(result))
    }

    pub(crate) proof fn private_after_executed(state:PrivateHtPrecinctState,parameters:Part1PrecinctPayloadParameters,
        data:Seq<u8>,header:Part2PlanePayloadHeader,caps:(u64,u64,u32,u64,u64,u64),
        args:(usize,usize,usize,usize),executed:PrivatePacketBodyEffect)
        requires part2_plane_payload_admit(parameters,data,header.packet,header.reader,header.contributions,header.sop)==Ok(args),
            private_packet_body_result(PrivatePacketBodyExecution {
                logical:Part1PacketBodyExecution{decoders:state.logical.decoders,index:0,offset:args.1,segments:0,passes:0},packed:state.packed,
            },header.contributions,data,parameters.error_offset,caps.2,caps.3,caps.4,caps.5,executed),
        ensures private_payload_after_result(state,parameters,data,header,caps,private_payload_finish(state,parameters,header,args,executed)),
    {
        let outcome=private_payload_finish(state,parameters,header,args,executed);
        part2_tier1_storage_pure(Ok(outcome));
        part2_tier1_storage_bind_frame(|calls|private_packet_body_run(PrivatePacketBodyExecution {
            logical:Part1PacketBodyExecution{decoders:state.logical.decoders,index:0,offset:args.1,segments:0,passes:0},packed:state.packed,
        },header.contributions,data,parameters.error_offset,caps.2,caps.3,caps.4,caps.5,calls),
            |actual,rest|Some((Ok(private_payload_finish(state,parameters,header,args,actual)),rest)),Ok(executed),Ok(outcome));
    }

    pub(crate) proof fn private_payload_prepared_observed(before:PrivateHtPrecinctState,data:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
        caps:(u64,u64,u32,u64,u64,u64),header:Part2PlanePayloadHeader,state:PrivateHtPrecinctState,effect:PrivatePrecinctPacketEffect)
        requires part2_plane_payload_headers(before.logical,data,Seq::empty(),parameters,caps.1,caps.5)==(Ok(header),state.logical),
            state.packed==before.packed,private_payload_after_result(state,parameters,data,header,caps,effect),
        ensures part2_tier1_storage_framed(|calls|private_payload_prepared_run(before,data,parameters,caps,calls),Ok(effect)),
    {
        part2_tier1_storage_eta(|calls|private_payload_after_run(state,parameters,data,header,caps,calls),Ok(effect));
    }

    pub(crate) proof fn private_payload_capacity_observed(before:PrivateHtPrecinctState,data:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
        caps:(u64,u64,u32,u64,u64,u64),effect:PrivatePrecinctPacketEffect)
        requires part1_precinct_payload_prefix(data,Seq::empty(),parameters,caps.1,caps.5).is_ok(),
            part2_precinct_contributions_result(Part2PrecinctContributionsContext {
                state:before.logical,data,packed:Seq::empty(),parameters,header_limit:caps.1,work:caps.5,
            },Ok(())),
            part2_tier1_storage_framed(|calls|private_payload_prepared_run(before,data,parameters,caps,calls),Ok(effect)),
        ensures private_payload_result(before,data,parameters,caps,effect),
    {
        part2_tier1_storage_eta(|calls|private_payload_prepared_run(before,data,parameters,caps,calls),Ok(effect));
        let context=Part2PrecinctContributionsContext {
            state:before.logical,data,packed:Seq::empty(),parameters,header_limit:caps.1,work:caps.5,
        };
        part2_tier1_resume_frame(|calls|part2_precinct_contributions_run(context,calls),
            |capacity:Result<(),crate::DecodeError>,rest|match capacity {
                Err(error)=>Some((Ok((Err(error),before)),rest)),
                Ok(())=>private_payload_prepared_run(before,data,parameters,caps,rest),
            },Ok(()),Ok(effect));
    }

    pub(crate) proof fn private_payload_capacity_error(before:PrivateHtPrecinctState,data:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
        caps:(u64,u64,u32,u64,u64,u64),error:crate::DecodeError)
        requires part1_precinct_payload_prefix(data,Seq::empty(),parameters,caps.1,caps.5).is_ok(),
            part2_precinct_contributions_result(Part2PrecinctContributionsContext {
                state:before.logical,data,packed:Seq::empty(),parameters,header_limit:caps.1,work:caps.5,
            },Err(error)),
        ensures private_payload_result(before,data,parameters,caps,(Err(error),before)),
    {
        part2_tier1_storage_pure::<PrivatePrecinctPacketEffect>(Ok((Err(error),before)));
        let context=Part2PrecinctContributionsContext {
            state:before.logical,data,packed:Seq::empty(),parameters,header_limit:caps.1,work:caps.5,
        };
        part2_tier1_resume_frame(|calls|part2_precinct_contributions_run(context,calls),
            |capacity:Result<(),crate::DecodeError>,rest|match capacity {
                Err(error)=>Some((Ok((Err(error),before)),rest)),
                Ok(())=>private_payload_prepared_run(before,data,parameters,caps,rest),
            },Err(error),Ok((Err(error),before)));
    }

    pub(crate) proof fn private_packet_payload_observed(ctx:PrivatePrecinctPacketContext,parameters:Part1PrecinctPayloadParameters,
        effect:PrivatePrecinctPacketEffect)
        requires part2_plane_precinct_admit(ctx.before.logical,ctx.part,ctx.offset,0,None,ctx.sequence,true,ctx.caps.0,ctx.caps.5)==Ok(parameters),
            private_payload_result(ctx.before,ctx.part.data.subrange(ctx.offset as int,ctx.part.data.len() as int),parameters,ctx.caps,effect),
        ensures private_precinct_packet_result(ctx,effect),
    {
        part2_tier1_storage_eta(|calls|private_payload_run(ctx.before,ctx.part.data.subrange(ctx.offset as int,ctx.part.data.len() as int),parameters,ctx.caps,calls),Ok(effect));
    }

    pub(crate) proof fn private_packet_admit_error(ctx:PrivatePrecinctPacketContext,error:crate::DecodeError)
        requires part2_plane_precinct_admit(ctx.before.logical,ctx.part,ctx.offset,0,None,ctx.sequence,true,ctx.caps.0,ctx.caps.5)==Err(error),
        ensures private_precinct_packet_result(ctx,(Err(error),ctx.before)),
    {part2_tier1_storage_pure::<PrivatePrecinctPacketEffect>(Ok((Err(error),ctx.before)));}

    pub(crate) proof fn private_payload_prefix_error(before:PrivateHtPrecinctState,data:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
        caps:(u64,u64,u32,u64,u64,u64),error:crate::DecodeError)
        requires part1_precinct_payload_prefix(data,Seq::empty(),parameters,caps.1,caps.5)==Err(error),
        ensures private_payload_result(before,data,parameters,caps,(Err(error),before)),
    {part2_tier1_storage_pure::<PrivatePrecinctPacketEffect>(Ok((Err(error),before)));}

    pub(crate) proof fn private_prepared_header_error(before:PrivateHtPrecinctState,data:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
        caps:(u64,u64,u32,u64,u64,u64),after:PrivateHtPrecinctState,error:crate::DecodeError)
        requires part2_plane_payload_headers(before.logical,data,Seq::empty(),parameters,caps.1,caps.5)==(Err(error),after.logical),
            after.packed==before.packed,
        ensures part2_tier1_storage_framed(|calls|private_payload_prepared_run(before,data,parameters,caps,calls),Ok((Err(error),after))),
    {part2_tier1_storage_pure::<PrivatePrecinctPacketEffect>(Ok((Err(error),after)));}

    pub(crate) proof fn private_payload_after_error(state:PrivateHtPrecinctState,parameters:Part1PrecinctPayloadParameters,
        data:Seq<u8>,header:Part2PlanePayloadHeader,caps:(u64,u64,u32,u64,u64,u64),error:crate::DecodeError)
        requires part2_plane_payload_admit(parameters,data,header.packet,header.reader,header.contributions,header.sop)==Err(error),
        ensures private_payload_after_result(state,parameters,data,header,caps,(Err(error),state)),
    {part2_tier1_storage_pure::<PrivatePrecinctPacketEffect>(Ok((Err(error),state)));}

    pub(crate) proof fn private_payload_after_normal(state:PrivateHtPrecinctState,parameters:Part1PrecinctPayloadParameters,
        data:Seq<u8>,header:Part2PlanePayloadHeader,caps:(u64,u64,u32,u64,u64,u64))
        requires private_precinct_wf(state),
        ensures private_payload_after_result(state,parameters,data,header,caps,private_payload_after_value(state,parameters,data,header,caps)),
    {
        match part2_plane_payload_admit(parameters,data,header.packet,header.reader,header.contributions,header.sop){
            Err(error)=>{private_payload_after_error(state,parameters,data,header,caps,error);},
            Ok(args)=>{
                let initial=PrivatePacketBodyExecution {
                    logical:Part1PacketBodyExecution{decoders:state.logical.decoders,index:0,offset:args.1,segments:0,passes:0},packed:state.packed,
                };
                private_packet_body_normal(initial,header.contributions,data,parameters.error_offset,caps.2,caps.3,caps.4,caps.5);
                private_after_executed(state,parameters,data,header,caps,args,
                    private_packet_body_value(initial,header.contributions,data,parameters.error_offset,caps.2,caps.3,caps.4,caps.5));
            },
        }
    }

    pub(crate) proof fn private_payload_normal(before:PrivateHtPrecinctState,data:Seq<u8>,parameters:Part1PrecinctPayloadParameters,
        caps:(u64,u64,u32,u64,u64,u64))
        requires private_precinct_wf(before),
        ensures private_payload_result(before,data,parameters,caps,private_payload_value(before,data,parameters,caps)),
    {
        let prepared=part2_plane_payload_headers(before.logical,data,Seq::empty(),parameters,caps.1,caps.5);
        let state=PrivateHtPrecinctState{logical:prepared.1,packed:before.packed};
        let result=private_payload_value(before,data,parameters,caps);
        match part1_precinct_payload_prefix(data,Seq::empty(),parameters,caps.1,caps.5){
            Err(error)=>{private_payload_prefix_error(before,data,parameters,caps,error);},
            Ok(_)=>{
                let context=Part2PrecinctContributionsContext{state:before.logical,data,packed:Seq::empty(),parameters,header_limit:caps.1,work:caps.5};
                part2_precinct_contributions_observed(context,Ok(()));
                match prepared.0{
                    Err(error)=>{private_prepared_header_error(before,data,parameters,caps,state,error);},
                    Ok(header)=>{
                        private_payload_after_normal(state,parameters,data,header,caps);
                        private_payload_prepared_observed(before,data,parameters,caps,header,state,result);
                    },
                }
                private_payload_capacity_observed(before,data,parameters,caps,result);
            },
        }
    }

    pub(crate) proof fn private_precinct_packet_normal(ctx:PrivatePrecinctPacketContext)
        requires private_precinct_wf(ctx.before),
        ensures private_precinct_packet_result(ctx,private_precinct_packet_value(ctx)),
    {
        match part2_plane_precinct_admit(ctx.before.logical,ctx.part,ctx.offset,0,None,ctx.sequence,true,ctx.caps.0,ctx.caps.5){
            Err(error)=>{private_packet_admit_error(ctx,error);},
            Ok(parameters)=>{
                private_payload_normal(ctx.before,ctx.part.data.subrange(ctx.offset as int,ctx.part.data.len() as int),parameters,ctx.caps);
                private_packet_payload_observed(ctx,parameters,private_precinct_packet_value(ctx));
            },
        }
    }

    pub(crate) proof fn private_precinct_packet_value_fields(ctx:PrivatePrecinctPacketContext)
        requires ctx.before.packed.len()==ctx.before.logical.decoders.len(),
            forall|i:int|0<=i<ctx.before.logical.decoders.len() ==> #[trigger] private_ht_state_wf(
                PrivateHtDecoderState{logical:ctx.before.logical.decoders[i],packed:ctx.before.packed[i]}),
        ensures (private_precinct_packet_value(ctx).0,private_precinct_packet_value(ctx).1.logical)==
            part1_precinct_packet_owned(ctx.before.logical,ctx.part,ctx.offset,Seq::empty(),0,None,ctx.sequence,true,
                ctx.caps.0,ctx.caps.1,ctx.caps.2,ctx.caps.3,ctx.caps.4,ctx.caps.5),
            private_precinct_packet_value(ctx).1.packed.len()==private_precinct_packet_value(ctx).1.logical.decoders.len(),
            forall|i:int|0<=i<private_precinct_packet_value(ctx).1.logical.decoders.len() ==> #[trigger] private_ht_state_wf(
                PrivateHtDecoderState{
                    logical:private_precinct_packet_value(ctx).1.logical.decoders[i],
                    packed:private_precinct_packet_value(ctx).1.packed[i],
                }),
            (match ctx.part.packed_packet_headers.source{Part1PackedHeaderSource::None=>true,_=>false}) ==>
                match private_precinct_packet_value(ctx).0{Err(_)=>true,Ok(value)=>value.2==0},
    {
        reveal(part1_precinct_payload_headers);reveal(part1_precinct_payload_after_headers);
        reveal(part1_precinct_payload_body);reveal(part1_packet_body_execute);
        if let Ok(parameters)=part2_plane_precinct_admit(ctx.before.logical,ctx.part,ctx.offset,0,None,ctx.sequence,true,ctx.caps.0,ctx.caps.5){
            let data=ctx.part.data.subrange(ctx.offset as int,ctx.part.data.len() as int);
            let headers=part2_plane_payload_headers(ctx.before.logical,data,Seq::empty(),parameters,ctx.caps.1,ctx.caps.5);
            if let Ok(header)=headers.0 {
                if let Ok(args)=part2_plane_payload_admit(parameters,data,header.packet,header.reader,header.contributions,header.sop){
                    private_packet_body_value_fields(PrivatePacketBodyExecution{
                        logical:Part1PacketBodyExecution{decoders:headers.1.decoders,index:0,offset:args.1,segments:0,passes:0},
                        packed:ctx.before.packed,
                    },header.contributions,data,parameters.error_offset,ctx.caps.2,ctx.caps.3,ctx.caps.4,ctx.caps.5);
                }
            }
        }
}
}
