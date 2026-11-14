//! Actual packet decoder-vector updates, including transactional coefficient failures.
use super::*;
verus! {
pub(crate) open spec fn part2_plane_execute_admit(s:Part1PacketBodyExecution,contribution:Part1CodeBlockContribution,data:Seq<u8>,decode:bool)->bool {
    contribution.data_length as nat<=usize::MAX && s.offset as nat+contribution.data_length as nat<=usize::MAX
        && s.offset as nat+contribution.data_length as nat<=data.len() && decode && s.index<s.decoders.len()
}
pub(crate) open spec fn part2_plane_execute_finish(s:Part1PacketBodyExecution,contribution:Part1CodeBlockContribution,local:usize,decoded:HtCodeBlockBodyResult)->Part1PacketBodyExecutionResult {
    let updated=Part1PacketBodyExecution {decoders:s.decoders.update(s.index as int,decoded.1),..s};
    match decoded.0{
        Err(error)=>(Err(error),updated),
        Ok(value)=>if s.segments as nat+value.segments as nat>u32::MAX{(Err(part1_packet_reader_error(local,crate::MalformedKind::ArithmeticOverflow)),updated)}
        else{
            let updated=Part1PacketBodyExecution {segments:(s.segments+value.segments) as u32,..updated};
            if s.passes as nat+value.passes as nat>u32::MAX{(Err(part1_packet_reader_error(local,crate::MalformedKind::ArithmeticOverflow)),updated)}
            else{(Ok(()),Part1PacketBodyExecution {passes:(s.passes+value.passes) as u32,offset:(s.offset+contribution.data_length) as usize,..updated})}
        },
    }
}
pub(crate) open spec fn part2_plane_execute_slot_run(s:Part1PacketBodyExecution,contribution:Part1CodeBlockContribution,data:Seq<u8>,error:usize,local:usize,decode:bool,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PacketBodyExecutionResult> {
    if part2_plane_execute_admit(s,contribution,data,decode){
        let body=data.subrange(s.offset as int,s.offset as int+contribution.data_length as int);
        part2_tier1_storage_bind(part2_plane_body_transaction_run(s.decoders[s.index as int],contribution,body,pass_limit,byte_limit,input_limit,work,calls),
            |decoded:HtCodeBlockBodyResult,rest|Some((Ok(part2_plane_execute_finish(s,contribution,local,decoded)),rest)))
    }else{Some((Ok(part1_packet_body_execute_slot_at(s,contribution,data,error,local,decode,pass_limit,byte_limit,input_limit,work)),calls))}
}
#[verifier::opaque]
pub(crate) open spec fn part2_plane_execute_run(s:Part1PacketBodyExecution,contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,local:usize,decode:bool,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PacketBodyExecutionResult>
    decreases if s.index<contributions.len(){((contributions.len()-s.index as nat)*2+1) as nat}else{0nat},
{
    if s.index>=contributions.len(){Some((Ok((Ok(()),s)),calls))}else{
        let slot=match contributions[s.index as int]{None=>Some((Ok((Ok(()),s)),calls)),Some(c)=>part2_plane_execute_slot_run(s,c,data,error,local,decode,pass_limit,byte_limit,input_limit,work,calls)};
        part2_tier1_storage_bind(slot,|step:Part1PacketBodyExecutionResult,rest|
            part2_plane_execute_next(step,s.index,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work,rest))
    }
}
pub(crate) open spec fn part2_plane_execute_next(step:Part1PacketBodyExecutionResult,index:usize,contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,local:usize,decode:bool,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PacketBodyExecutionResult>
    decreases if index<contributions.len(){((contributions.len()-index as nat)*2) as nat}else{0nat},
{
    if step.1.index!=index{None}else{
    match step.0{
        Err(_)=>Some((Ok(step),calls)),
        Ok(())=>if step.1.index==usize::MAX{Some((Ok((Err(part1_packet_reader_error(local,crate::MalformedKind::ArithmeticOverflow)),step.1)),calls))}
            else if step.1.index>=contributions.len(){Some((Ok(step),calls))}
            else{part2_plane_execute_run(Part1PacketBodyExecution {index:(step.1.index+1) as usize,..step.1},contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work,calls)},
    }}
}
pub(crate) open spec fn part2_plane_execute_result(s:Part1PacketBodyExecution,contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,local:usize,decode:bool,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,result:Part1PacketBodyExecutionResult)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_execute_run(s,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work,calls),Ok(result))
}
pub(crate) proof fn part2_plane_execute_slot_normal(s:Part1PacketBodyExecution,contribution:Part1CodeBlockContribution,data:Seq<u8>,error:usize,local:usize,decode:bool,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
    ensures part2_tier1_storage_framed(|calls|part2_plane_execute_slot_run(s,contribution,data,error,local,decode,pass_limit,byte_limit,input_limit,work,calls),
        Ok(part1_packet_body_execute_slot_at(s,contribution,data,error,local,decode,pass_limit,byte_limit,input_limit,work))),
{
    let result=part1_packet_body_execute_slot_at(s,contribution,data,error,local,decode,pass_limit,byte_limit,input_limit,work);
    if part2_plane_execute_admit(s,contribution,data,decode){
        let body=data.subrange(s.offset as int,s.offset as int+contribution.data_length as int);
        part2_plane_body_transaction_normal(s.decoders[s.index as int],contribution,body,pass_limit,byte_limit,input_limit,work);
        let decoded=part1_code_block_body_transaction(s.decoders[s.index as int],contribution,body,pass_limit,byte_limit,input_limit,work);
        part2_plane_body_transaction_frames(s.decoders[s.index as int],contribution,body,pass_limit,byte_limit,input_limit,work,decoded);
        part2_tier1_storage_pure(Ok(result));
        part2_tier1_storage_bind_frame(|calls|part2_plane_body_transaction_run(s.decoders[s.index as int],contribution,body,pass_limit,byte_limit,input_limit,work,calls),
            |decoded:HtCodeBlockBodyResult,rest|Some((Ok(part2_plane_execute_finish(s,contribution,local,decoded)),rest)),Ok(decoded),Ok(result));
    }else{part2_tier1_storage_pure(Ok(result));}
}
pub(crate) proof fn part2_plane_execute_normal(s:Part1PacketBodyExecution,contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,local:usize,decode:bool,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
    ensures part2_plane_execute_result(s,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work,
        part1_packet_body_execute_at(s,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work)),
    decreases if s.index<contributions.len(){((contributions.len()-s.index as nat)*2+1) as nat}else{0nat},
{
    reveal_with_fuel(part2_plane_execute_run,2);reveal_with_fuel(part2_plane_execute_next,1);reveal_with_fuel(part1_packet_body_execute_at,1);
    let result=part1_packet_body_execute_at(s,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work);
    if s.index>=contributions.len(){part2_tier1_storage_pure(Ok(result));}else{
        let step=match contributions[s.index as int]{None=>(Ok(()),s),Some(c)=>part1_packet_body_execute_slot_at(s,c,data,error,local,decode,pass_limit,byte_limit,input_limit,work)};
        let child=|calls|match contributions[s.index as int]{None=>Some((Ok((Ok(()),s)),calls)),Some(c)=>part2_plane_execute_slot_run(s,c,data,error,local,decode,pass_limit,byte_limit,input_limit,work,calls)};
        match contributions[s.index as int] {
            None=>{part2_tier1_storage_pure(Ok(step));},
            Some(c)=>{
                part2_plane_execute_slot_normal(s,c,data,error,local,decode,pass_limit,byte_limit,input_limit,work);
                part2_tier1_storage_eta(|calls|part2_plane_execute_slot_run(s,c,data,error,local,decode,pass_limit,byte_limit,input_limit,work,calls),Ok(step));
            },
        }
        if step.0.is_ok() && step.1.index<usize::MAX {
            let next=Part1PacketBodyExecution {index:(step.1.index+1) as usize,..step.1};
            part2_plane_execute_normal(next,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work);
            part2_tier1_storage_eta(|calls|part2_plane_execute_run(next,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work,calls),Ok(result));
        }else{part2_tier1_storage_pure(Ok(result));}
        part2_tier1_storage_bind_frame(child,|step:Part1PacketBodyExecutionResult,rest|part2_plane_execute_next(step,s.index,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work,rest),Ok(step),Ok(result));
    }
}
pub(crate) proof fn part2_plane_execute_body_step(s:Part1PacketBodyExecution,contributions:Seq<Option<Part1CodeBlockContribution>>,contribution:Part1CodeBlockContribution,data:Seq<u8>,
    error:usize,local:usize,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
    requires s.index<contributions.len(),contributions[s.index as int]==Some(contribution),part2_plane_execute_admit(s,contribution,data,true),
    ensures forall|calls:Seq<Part2Tier1StorageEvent>| #[trigger] part2_plane_execute_run(s,contributions,data,error,local,true,pass_limit,byte_limit,input_limit,work,calls)
        ==part2_tier1_storage_bind(part2_plane_body_transaction_run(s.decoders[s.index as int],contribution,data.subrange(s.offset as int,s.offset as int+contribution.data_length as int),pass_limit,byte_limit,input_limit,work,calls),
            |decoded:HtCodeBlockBodyResult,rest|part2_plane_execute_next(part2_plane_execute_finish(s,contribution,local,decoded),s.index,contributions,data,error,local,true,pass_limit,byte_limit,input_limit,work,rest)),
{
    reveal_with_fuel(part2_plane_execute_run,2);reveal_with_fuel(part2_plane_execute_next,1);
    assert forall|calls:Seq<Part2Tier1StorageEvent>| #[trigger] part2_plane_execute_run(s,contributions,data,error,local,true,pass_limit,byte_limit,input_limit,work,calls)
        ==part2_tier1_storage_bind(part2_plane_body_transaction_run(s.decoders[s.index as int],contribution,data.subrange(s.offset as int,s.offset as int+contribution.data_length as int),pass_limit,byte_limit,input_limit,work,calls),
            |decoded:HtCodeBlockBodyResult,rest|part2_plane_execute_next(part2_plane_execute_finish(s,contribution,local,decoded),s.index,contributions,data,error,local,true,pass_limit,byte_limit,input_limit,work,rest)) by{
        let raw=part2_plane_body_transaction_run(s.decoders[s.index as int],contribution,data.subrange(s.offset as int,s.offset as int+contribution.data_length as int),pass_limit,byte_limit,input_limit,work,calls);
        match raw {
            None=>{},Some((Err(_),_))=>{},Some((Ok(_),_))=>{},
        }
    }
}
pub(crate) proof fn part2_plane_execute_pure_step(s:Part1PacketBodyExecution,contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,local:usize,decode:bool,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
    requires s.index<contributions.len(),contributions[s.index as int].is_none() || !decode,
    ensures forall|calls:Seq<Part2Tier1StorageEvent>| #[trigger] part2_plane_execute_run(s,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work,calls)
        ==part2_plane_execute_next(match contributions[s.index as int]{None=>(Ok(()),s),Some(c)=>part1_packet_body_execute_slot_at(s,c,data,error,local,decode,pass_limit,byte_limit,input_limit,work)},
            s.index,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work,calls),
{reveal_with_fuel(part2_plane_execute_run,2);reveal_with_fuel(part2_plane_execute_next,1);}
pub(crate) proof fn part2_plane_execute_join(s:Part1PacketBodyExecution,contributions:Seq<Option<Part1CodeBlockContribution>>,data:Seq<u8>,error:usize,local:usize,decode:bool,
    pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,root:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PacketBodyExecutionResult>,result:Part1PacketBodyExecutionResult)
    requires part2_tier1_storage_framed(root,Ok(result)),forall|calls| #[trigger] root(calls)==part2_plane_execute_run(s,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work,calls),
    ensures part2_plane_execute_result(s,contributions,data,error,local,decode,pass_limit,byte_limit,input_limit,work,result),
{part2_tier1_storage_eta(root,Ok(result));}
}
