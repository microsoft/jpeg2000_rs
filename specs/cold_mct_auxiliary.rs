//! Original dependency and spectral preparation owners, retaining first errors and work.
use super::*;
verus! {
pub(crate) open spec fn part2_mct_auxiliary_program_run<T,S>(
    requests:Seq<(Part2MctRuntimeCapacity,S)>,ordinary:(Result<T,crate::DecodeError>,S),
    calls:Seq<Part2Tier1StorageEvent>,
)->Part2Tier1Run<(Result<T,crate::DecodeError>,S)>
    decreases requests.len(),
{
    if requests.len()==0 {Some((Ok(ordinary),calls))}else{
        part2_tier1_storage_resume(part2_mct_runtime_capacity_run(requests[0].0,calls),
            |reply:Result<(),crate::DecodeError>,rest|match reply {
                Err(error)=>Some((Ok((Err(error),requests[0].1)),rest)),
                Ok(())=>part2_mct_auxiliary_program_run(requests.drop_first(),ordinary,rest),
            })
    }
}
pub(crate) open spec fn part2_mct_auxiliary_program_result<T,S>(
    requests:Seq<(Part2MctRuntimeCapacity,S)>,ordinary:(Result<T,crate::DecodeError>,S),
    result:(Result<T,crate::DecodeError>,S),
)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_auxiliary_program_run(requests,ordinary,calls),Ok(result))
}
pub(crate) proof fn part2_mct_auxiliary_program_normal<T,S>(
    requests:Seq<(Part2MctRuntimeCapacity,S)>,ordinary:(Result<T,crate::DecodeError>,S),
)
    ensures part2_mct_auxiliary_program_result(requests,ordinary,ordinary),
    decreases requests.len(),
{
    if requests.len()==0 {part2_tier1_storage_pure(Ok(ordinary));}else{
        part2_mct_runtime_capacity_normal(requests[0].0);
        part2_mct_auxiliary_program_normal(requests.drop_first(),ordinary);
        part2_tier1_storage_eta(|calls|part2_mct_auxiliary_program_run(requests.drop_first(),ordinary,calls),Ok(ordinary));
        part2_tier1_resume_frame(|calls|part2_mct_runtime_capacity_run(requests[0].0,calls),
            |reply:Result<(),crate::DecodeError>,rest|match reply {
                Err(error)=>Some((Ok((Err(error),requests[0].1)),rest)),
                Ok(())=>part2_mct_auxiliary_program_run(requests.drop_first(),ordinary,rest),
            },Ok(()),Ok(ordinary));
    }
}
pub(crate) proof fn part2_mct_auxiliary_program_refused_at<T,S>(
    requests:Seq<(Part2MctRuntimeCapacity,S)>,ordinary:(Result<T,crate::DecodeError>,S),
    position:nat,error:crate::DecodeError,
)
    requires position<requests.len(),part2_mct_runtime_capacity_result(requests[position as int].0,Err(error)),
    ensures part2_mct_auxiliary_program_result(requests,ordinary,(Err(error),requests[position as int].1)),
    decreases position,
{
    let result=(Err::<T,crate::DecodeError>(error),requests[position as int].1);
    if position==0 {
        part2_tier1_storage_pure(Ok(result));
        part2_tier1_resume_frame(|calls|part2_mct_runtime_capacity_run(requests[0].0,calls),
            |reply:Result<(),crate::DecodeError>,rest|match reply {
                Err(error)=>Some((Ok((Err(error),requests[0].1)),rest)),
                Ok(())=>part2_mct_auxiliary_program_run(requests.drop_first(),ordinary,rest),
            },Err(error),Ok(result));
    }else{
        assert(requests.drop_first()[position as int-1]==requests[position as int]);
        part2_mct_auxiliary_program_refused_at(requests.drop_first(),ordinary,(position-1) as nat,error);
        part2_tier1_storage_eta(|calls|part2_mct_auxiliary_program_run(requests.drop_first(),ordinary,calls),Ok(result));
        part2_mct_runtime_capacity_normal(requests[0].0);
        part2_tier1_resume_frame(|calls|part2_mct_runtime_capacity_run(requests[0].0,calls),
            |reply:Result<(),crate::DecodeError>,rest|match reply {
                Err(error)=>Some((Ok((Err(error),requests[0].1)),rest)),
                Ok(())=>part2_mct_auxiliary_program_run(requests.drop_first(),ordinary,rest),
            },Ok(()),Ok(result));
    }
}
pub(crate) proof fn part2_mct_auxiliary_program_refused<T,S>(
    requests:Seq<(Part2MctRuntimeCapacity,S)>,ordinary:(Result<T,crate::DecodeError>,S),
    capacity:Part2MctRuntimeCapacity,state:S,error:crate::DecodeError,
)
    requires requests.contains((capacity,state)),part2_mct_runtime_capacity_result(capacity,Err(error)),
    ensures part2_mct_auxiliary_program_result(requests,ordinary,(Err(error),state)),
{
    let position=choose|i:int|0<=i<requests.len() && requests[i]==(capacity,state);
    part2_mct_auxiliary_program_refused_at(requests,ordinary,position as nat,error);
}
pub(crate) proof fn part2_mct_auxiliary_program_error_at<T,S>(
    requests:Seq<(Part2MctRuntimeCapacity,S)>,ordinary:(Result<T,crate::DecodeError>,S),
    calls:Seq<Part2Tier1StorageEvent>,error:crate::DecodeError,state:S,rest:Seq<Part2Tier1StorageEvent>,
)
    requires part2_mct_auxiliary_program_run(requests,ordinary,calls)==Some((Ok((Err(error),state)),rest)),
    ensures ordinary==(Err(error),state) || (exists|capacity:Part2MctRuntimeCapacity|
        requests.contains((capacity,state)) && part2_mct_runtime_capacity_result(capacity,Err(error))),
    decreases requests.len(),
{
    if requests.len()>0 {
        if let Some((reply,after))=part2_mct_runtime_capacity_run(requests[0].0,calls) {
            match reply {
                Err(failed)=>{
                    part2_mct_runtime_capacity_observed(requests[0].0,Err(failed));
                    assert(requests.contains(requests[0]));
                },
                Ok(())=>{
                    part2_mct_auxiliary_program_error_at(requests.drop_first(),ordinary,after,error,state,rest);
                    if ordinary!=(Err(error),state) {
                        let capacity=choose|capacity:Part2MctRuntimeCapacity|requests.drop_first().contains((capacity,state))
                            && part2_mct_runtime_capacity_result(capacity,Err(error));
                        assert(requests.contains((capacity,state)));
                    }
                },
            }
        }
    }
}
pub(crate) proof fn part2_mct_auxiliary_program_error_info<T,S>(
    requests:Seq<(Part2MctRuntimeCapacity,S)>,ordinary:(Result<T,crate::DecodeError>,S),
    error:crate::DecodeError,state:S,
)
    requires part2_mct_auxiliary_program_result(requests,ordinary,(Err(error),state)),
    ensures ordinary==(Err(error),state) || (exists|capacity:Part2MctRuntimeCapacity|
        requests.contains((capacity,state)) && part2_mct_runtime_capacity_result(capacity,Err(error))),
{
    let run=|calls|part2_mct_auxiliary_program_run(requests,ordinary,calls);
    let result=Ok((Err::<T,crate::DecodeError>(error),state));
    let prefix=choose|prefix:Seq<Part2Tier1StorageEvent>|part2_tier1_storage_prefix(run,prefix,result);
    part2_tier1_storage_at(run,prefix,result,Seq::empty());
    assert(prefix+Seq::<Part2Tier1StorageEvent>::empty() =~= prefix);
    part2_mct_auxiliary_program_error_at(requests,ordinary,prefix,error,state,Seq::empty());
}
pub(crate) proof fn part2_mct_auxiliary_program_child_error<A,B,S,R>(
    whole:Seq<(Part2MctRuntimeCapacity,R)>,ordinary:(Result<B,crate::DecodeError>,R),
    child:Seq<(Part2MctRuntimeCapacity,S)>,child_value:(Result<A,crate::DecodeError>,S),
    error:crate::DecodeError,child_state:S,state:R,
)
    requires part2_mct_auxiliary_program_result(child,child_value,(Err(error),child_state)),
        child_value==(Err(error),child_state) ==> ordinary==(Err(error),state),
        forall|capacity:Part2MctRuntimeCapacity|child.contains((capacity,child_state)) ==> whole.contains((capacity,state)),
    ensures part2_mct_auxiliary_program_result(whole,ordinary,(Err(error),state)),
{
    part2_mct_auxiliary_program_error_info(child,child_value,error,child_state);
    if child_value==(Err(error),child_state) {part2_mct_auxiliary_program_normal(whole,ordinary);}else{
        let capacity=choose|capacity:Part2MctRuntimeCapacity|child.contains((capacity,child_state))
            && part2_mct_runtime_capacity_result(capacity,Err(error));
        part2_mct_auxiliary_program_refused(whole,ordinary,capacity,state,error);
    }
}
pub(crate) open spec fn part2_mct_pair_requests<S>(
    components:Seq<Part2MctComponent>,inputs:Seq<u16>,outputs:Seq<u16>,count:usize,state:S,
)->Seq<(Part2MctRuntimeCapacity,S)> {
    seq![(Part2MctRuntimeCapacity::PairIndexes {components,inputs,outputs,count,destination:false},state),
        (Part2MctRuntimeCapacity::PairIndexes {components,inputs,outputs,count,destination:true},state)]
}
pub(crate) open spec fn part2_mct_pair_storage_result(
    components:Seq<Part2MctComponent>,inputs:Seq<u16>,outputs:Seq<u16>,count:usize,
    result:Result<(Seq<usize>,Seq<usize>),crate::DecodeError>,
)->bool {
    part2_mct_auxiliary_program_result(part2_mct_pair_requests(components,inputs,outputs,count,()),
        (part2_mct_component_pairs(components,inputs,outputs,count as nat),()),(result,()))
}
pub(crate) proof fn part2_mct_pair_storage_normal(
    components:Seq<Part2MctComponent>,inputs:Seq<u16>,outputs:Seq<u16>,count:usize,
)
    ensures part2_mct_pair_storage_result(components,inputs,outputs,count,
        part2_mct_component_pairs(components,inputs,outputs,count as nat)),
{
    part2_mct_auxiliary_program_normal(part2_mct_pair_requests(components,inputs,outputs,count,()),
        (part2_mct_component_pairs(components,inputs,outputs,count as nat),()));
}
pub(crate) proof fn part2_mct_pair_storage_refused(
    components:Seq<Part2MctComponent>,inputs:Seq<u16>,outputs:Seq<u16>,count:usize,destination:bool,error:crate::DecodeError,
)
    requires part2_mct_runtime_capacity_result(Part2MctRuntimeCapacity::PairIndexes {components,inputs,outputs,count,destination},Err(error)),
    ensures part2_mct_pair_storage_result(components,inputs,outputs,count,Err(error)),
{
    let capacity=Part2MctRuntimeCapacity::PairIndexes {components,inputs,outputs,count,destination};
    let requests=part2_mct_pair_requests(components,inputs,outputs,count,());
    assert(requests[if destination {1int}else{0int}]==(capacity,()));
    assert(requests.contains((capacity,())));
    part2_mct_auxiliary_program_refused(requests,(part2_mct_component_pairs(components,inputs,outputs,count as nat),()),capacity,(),error);
}
pub(crate) proof fn part2_mct_auxiliary_concat_member<A>(left:Seq<A>,right:Seq<A>,value:A)
    requires left.contains(value) || right.contains(value),
    ensures (left+right).contains(value),
{
    if left.contains(value) {
        let index=choose|i:int|0<=i<left.len() && left[i]==value;
        assert((left+right)[index]==value);
    }else{
        let index=choose|i:int|0<=i<right.len() && right[i]==value;
        assert((left+right)[left.len()+index]==value);
    }
}
pub(crate) proof fn part2_mct_pair_request_state<S,R>(
    components:Seq<Part2MctComponent>,inputs:Seq<u16>,outputs:Seq<u16>,count:usize,from:S,to:R,
)
    ensures forall|capacity:Part2MctRuntimeCapacity|
        part2_mct_pair_requests(components,inputs,outputs,count,from).contains((capacity,from))
        ==> part2_mct_pair_requests(components,inputs,outputs,count,to).contains((capacity,to)),
{
    let left=part2_mct_pair_requests(components,inputs,outputs,count,from);
    let right=part2_mct_pair_requests(components,inputs,outputs,count,to);
    assert forall|capacity:Part2MctRuntimeCapacity|left.contains((capacity,from)) ==> right.contains((capacity,to)) by {
        if left.contains((capacity,from)) {
            let index=choose|i:int|0<=i<left.len() && left[i]==(capacity,from);
            assert(right[index]==(capacity,to));
        }
    }
}
pub(crate) open spec fn part2_mct_partition_requests<S>(count:usize,wavelet:Part2MctWavelet,state:S)
    ->Seq<(Part2MctRuntimeCapacity,S)> {
    seq![(Part2MctRuntimeCapacity::WaveletPartition {count,wavelet,high:false},state),
        (Part2MctRuntimeCapacity::WaveletPartition {count,wavelet,high:true},state)]
}
pub(crate) open spec fn part2_mct_partition_storage_result(count:usize,wavelet:Part2MctWavelet,
    result:Result<(Seq<bool>,Seq<usize>,usize),crate::DecodeError>)->bool {
    part2_mct_auxiliary_program_result(part2_mct_partition_requests(count,wavelet,()),
        (part2_mct_wavelet_partition(count,wavelet),()),(result,()))
}
pub(crate) proof fn part2_mct_partition_storage_normal(count:usize,wavelet:Part2MctWavelet)
    ensures part2_mct_partition_storage_result(count,wavelet,part2_mct_wavelet_partition(count,wavelet)),
{
    part2_mct_auxiliary_program_normal(part2_mct_partition_requests(count,wavelet,()),
        (part2_mct_wavelet_partition(count,wavelet),()));
}
pub(crate) proof fn part2_mct_partition_storage_refused(count:usize,wavelet:Part2MctWavelet,high:bool,error:crate::DecodeError)
    requires part2_mct_runtime_capacity_result(Part2MctRuntimeCapacity::WaveletPartition {count,wavelet,high},Err(error)),
    ensures part2_mct_partition_storage_result(count,wavelet,Err(error)),
{
    let capacity=Part2MctRuntimeCapacity::WaveletPartition {count,wavelet,high};
    let requests=part2_mct_partition_requests(count,wavelet,());
    assert(requests[if high {1int}else{0int}]==(capacity,()));
    assert(requests.contains((capacity,())));
    part2_mct_auxiliary_program_refused(requests,(part2_mct_wavelet_partition(count,wavelet),()),capacity,(),error);
}
pub(crate) open spec fn part2_mct_dependency_prepare_value(context:Part2MctRuntimeContext)
    ->(Result<Part2MctDependencyPreparation,crate::DecodeError>,u64) {
    part2_mct_prepare_dependency(context.components,context.collection,context.work,context.maximum_work,context.maximum_bytes)
}
pub(crate) open spec fn part2_mct_dependency_prepare_requests(context:Part2MctRuntimeContext)
    ->Seq<(Part2MctRuntimeCapacity,u64)> {
    match part2_mct_dependency_dimensions(context.collection) {
        Err(_)=>Seq::empty(),Ok((count,_))=>part2_mct_pair_requests(
            context.components,context.collection.1,context.collection.2,count,context.work),
    }
}
pub(crate) open spec fn part2_mct_dependency_prepare_storage_result(context:Part2MctRuntimeContext,
    result:(Result<Part2MctDependencyPreparation,crate::DecodeError>,u64))->bool {
    part2_mct_auxiliary_program_result(part2_mct_dependency_prepare_requests(context),
        part2_mct_dependency_prepare_value(context),result)
}
pub(crate) proof fn part2_mct_dependency_prepare_storage_normal(context:Part2MctRuntimeContext)
    ensures part2_mct_dependency_prepare_storage_result(context,part2_mct_dependency_prepare_value(context)),
{part2_mct_auxiliary_program_normal(part2_mct_dependency_prepare_requests(context),part2_mct_dependency_prepare_value(context));}
pub(crate) proof fn part2_mct_dependency_prepare_pair_error(context:Part2MctRuntimeContext,count:usize,coefficients:usize,error:crate::DecodeError)
    requires part2_mct_dependency_dimensions(context.collection)==Ok((count,coefficients)),
        part2_mct_pair_storage_result(context.components,context.collection.1,context.collection.2,count,Err(error)),
    ensures part2_mct_dependency_prepare_storage_result(context,(Err(error),context.work)),
{
    part2_mct_pair_request_state(context.components,context.collection.1,context.collection.2,count,(),context.work);
    part2_mct_auxiliary_program_child_error(
        part2_mct_dependency_prepare_requests(context),part2_mct_dependency_prepare_value(context),
        part2_mct_pair_requests(context.components,context.collection.1,context.collection.2,count,()),
        (part2_mct_component_pairs(context.components,context.collection.1,context.collection.2,count as nat),()),
        error,(),context.work);
}
pub(crate) open spec fn part2_mct_wavelet_pair_admitted(context:Part2MctRuntimeContext)->bool {
    context.collection.6.is_some() && context.collection.1.len()>0
        && context.collection.1.len()==context.collection.2.len() && context.collection.1.len()<=usize::MAX
}
pub(crate) open spec fn part2_mct_wavelet_before_partition(context:Part2MctRuntimeContext)
    ->Option<(Part2MctWavelet,usize,usize)> {
    if !part2_mct_wavelet_pair_admitted(context){None}else{
        let wavelet=context.collection.6.unwrap();let count=context.collection.1.len() as usize;
        match part2_mct_component_pairs(context.components,context.collection.1,context.collection.2,count as nat) {
            Err(_)=>None,Ok((source,destination))=>match part2_mct_validate_dependency_layout(
                context.components,source,destination,part2_mct_wavelet_reversible(wavelet)) {
                    Err(_)=>None,Ok(samples)=>Some((wavelet,count,samples)),
                },
        }
    }
}
pub(crate) open spec fn part2_mct_wavelet_prepare_value(context:Part2MctRuntimeContext)
    ->(Result<Part2MctWaveletPreparation,crate::DecodeError>,u64) {
    part2_mct_prepare_wavelet(context.components,context.collection,context.work,context.maximum_work,context.maximum_bytes)
}
pub(crate) open spec fn part2_mct_wavelet_after_partition_requests(context:Part2MctRuntimeContext)
    ->Seq<(Part2MctRuntimeCapacity,u64)> {
    match part2_mct_wavelet_before_partition(context) {
        None=>Seq::empty(),Some((wavelet,count,samples))=>match part2_mct_wavelet_partition(count,wavelet) {
            Err(_)=>Seq::empty(),Ok(_)=>{
                let admitted=part2_mct_wavelet_admission(samples,count,wavelet.1,context.work,context.maximum_work,context.maximum_bytes);
                if admitted.0.is_err(){Seq::empty()}else{
                    seq![(Part2MctRuntimeCapacity::WaveletFractions {context},admitted.1)]
                }
            },
        },
    }
}
pub(crate) open spec fn part2_mct_wavelet_partition_tail_requests(context:Part2MctRuntimeContext)
    ->Seq<(Part2MctRuntimeCapacity,u64)> {
    match part2_mct_wavelet_before_partition(context) {
        None=>Seq::empty(),Some((wavelet,count,_))=>part2_mct_partition_requests(count,wavelet,context.work)
            +part2_mct_wavelet_after_partition_requests(context),
    }
}
pub(crate) open spec fn part2_mct_wavelet_prepare_requests(context:Part2MctRuntimeContext)
    ->Seq<(Part2MctRuntimeCapacity,u64)> {
    if !part2_mct_wavelet_pair_admitted(context){Seq::empty()}else{
        part2_mct_pair_requests(context.components,context.collection.1,context.collection.2,
            context.collection.1.len() as usize,context.work)+part2_mct_wavelet_partition_tail_requests(context)
    }
}
pub(crate) open spec fn part2_mct_wavelet_prepare_storage_run(context:Part2MctRuntimeContext,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<(Result<Part2MctWaveletPreparation,crate::DecodeError>,u64)> {
    part2_mct_auxiliary_program_run(part2_mct_wavelet_prepare_requests(context),part2_mct_wavelet_prepare_value(context),calls)
}
pub(crate) open spec fn part2_mct_wavelet_prepare_storage_result(context:Part2MctRuntimeContext,
    result:(Result<Part2MctWaveletPreparation,crate::DecodeError>,u64))->bool {
    part2_mct_auxiliary_program_result(part2_mct_wavelet_prepare_requests(context),part2_mct_wavelet_prepare_value(context),result)
}
pub(crate) proof fn part2_mct_wavelet_prepare_storage_normal(context:Part2MctRuntimeContext)
    ensures part2_mct_wavelet_prepare_storage_result(context,part2_mct_wavelet_prepare_value(context)),
{part2_mct_auxiliary_program_normal(part2_mct_wavelet_prepare_requests(context),part2_mct_wavelet_prepare_value(context));}
pub(crate) proof fn part2_mct_wavelet_prepare_storage_frames(context:Part2MctRuntimeContext,
    result:(Result<Part2MctWaveletPreparation,crate::DecodeError>,u64))
    requires part2_mct_wavelet_prepare_storage_result(context,result),
    ensures part2_tier1_storage_framed(|calls|part2_mct_wavelet_prepare_storage_run(context,calls),Ok(result)),
{
    part2_tier1_storage_eta(|calls|part2_mct_auxiliary_program_run(
        part2_mct_wavelet_prepare_requests(context),part2_mct_wavelet_prepare_value(context),calls),Ok(result));
}
pub(crate) proof fn part2_mct_wavelet_prepare_pair_error(context:Part2MctRuntimeContext,error:crate::DecodeError)
    requires part2_mct_wavelet_pair_admitted(context),
        part2_mct_pair_storage_result(context.components,context.collection.1,context.collection.2,
            context.collection.1.len() as usize,Err(error)),
    ensures part2_mct_wavelet_prepare_storage_result(context,(Err(error),context.work)),
{
    let count=context.collection.1.len() as usize;
    let child=part2_mct_pair_requests(context.components,context.collection.1,context.collection.2,count,());
    let prefix=part2_mct_pair_requests(context.components,context.collection.1,context.collection.2,count,context.work);
    part2_mct_pair_request_state(context.components,context.collection.1,context.collection.2,count,(),context.work);
    assert forall|capacity:Part2MctRuntimeCapacity|child.contains((capacity,())) ==>
        part2_mct_wavelet_prepare_requests(context).contains((capacity,context.work)) by {
        if child.contains((capacity,())) {
            part2_mct_auxiliary_concat_member(prefix,part2_mct_wavelet_partition_tail_requests(context),(capacity,context.work));
        }
    }
    part2_mct_auxiliary_program_child_error(part2_mct_wavelet_prepare_requests(context),part2_mct_wavelet_prepare_value(context),
        child,(part2_mct_component_pairs(context.components,context.collection.1,context.collection.2,count as nat),()),error,(),context.work);
}
pub(crate) proof fn part2_mct_wavelet_prepare_partition_error(context:Part2MctRuntimeContext,wavelet:Part2MctWavelet,
    count:usize,samples:usize,error:crate::DecodeError)
    requires part2_mct_wavelet_before_partition(context)==Some((wavelet,count,samples)),
        part2_mct_partition_storage_result(count,wavelet,Err(error)),
    ensures part2_mct_wavelet_prepare_storage_result(context,(Err(error),context.work)),
{
    let child=part2_mct_partition_requests(count,wavelet,());
    let partition=part2_mct_partition_requests(count,wavelet,context.work);
    let prefix=part2_mct_pair_requests(context.components,context.collection.1,context.collection.2,count,context.work);
    assert forall|capacity:Part2MctRuntimeCapacity|child.contains((capacity,())) ==>
        part2_mct_wavelet_prepare_requests(context).contains((capacity,context.work)) by {
        if child.contains((capacity,())) {
            let index=choose|i:int|0<=i<child.len() && child[i]==(capacity,());
            assert(partition[index]==(capacity,context.work));
            assert(partition.contains((capacity,context.work)));
            part2_mct_auxiliary_concat_member(partition,part2_mct_wavelet_after_partition_requests(context),(capacity,context.work));
            part2_mct_auxiliary_concat_member(prefix,part2_mct_wavelet_partition_tail_requests(context),(capacity,context.work));
        }
    }
    part2_mct_auxiliary_program_child_error(part2_mct_wavelet_prepare_requests(context),part2_mct_wavelet_prepare_value(context),
        child,(part2_mct_wavelet_partition(count,wavelet),()),error,(),context.work);
}
pub(crate) proof fn part2_mct_wavelet_prepare_fraction_error(context:Part2MctRuntimeContext,plan:Part2MctWaveletPreparation,
    charged:u64,error:crate::DecodeError)
    requires part2_mct_wavelet_prepare_value(context)==(Ok(plan),charged),
        part2_mct_runtime_capacity_result(Part2MctRuntimeCapacity::WaveletFractions {context},Err(error)),
    ensures part2_mct_wavelet_prepare_storage_result(context,(Err(error),charged)),
{
    let request=(Part2MctRuntimeCapacity::WaveletFractions {context},charged);
    let tail=part2_mct_wavelet_after_partition_requests(context);
    assert(tail==seq![request]);assert(tail[0]==request);assert(tail.contains(request));
    let wavelet=context.collection.6.unwrap();let count=context.collection.1.len() as usize;
    part2_mct_auxiliary_concat_member(part2_mct_partition_requests(count,wavelet,context.work),tail,request);
    part2_mct_auxiliary_concat_member(part2_mct_pair_requests(context.components,context.collection.1,context.collection.2,count,context.work),
        part2_mct_wavelet_partition_tail_requests(context),request);
    part2_mct_auxiliary_program_refused(part2_mct_wavelet_prepare_requests(context),part2_mct_wavelet_prepare_value(context),
        request.0,charged,error);
}
pub(crate) open spec fn part2_mct_dependency_prefix_requests(context:Part2MctRuntimeContext)
    ->Seq<(Part2MctRuntimeCapacity,(Seq<Part2MctComponent>,u64))> {
    let requests=part2_mct_dependency_prepare_requests(context);
    Seq::new(requests.len(),|i:int|(requests[i].0,(context.components,requests[i].1)))
}
pub(crate) open spec fn part2_mct_dependency_scratch_requests(context:Part2MctRuntimeContext)
    ->Seq<(Part2MctRuntimeCapacity,(Seq<Part2MctComponent>,u64))> {
    let preparation=part2_mct_dependency_prepare_value(context);
    match preparation.0 {
        Err(_)=>Seq::empty(),Ok(_)=>seq![
            (Part2MctRuntimeCapacity::DependencyScratch {context,role:Part2MctRuntimeRole::SourceSamples},(context.components,preparation.1)),
            (Part2MctRuntimeCapacity::DependencyScratch {context,role:Part2MctRuntimeRole::OutputSamples},(context.components,preparation.1)),
            (Part2MctRuntimeCapacity::DependencyScratch {context,role:Part2MctRuntimeRole::FractionBits},(context.components,preparation.1)),
        ],
    }
}
pub(crate) open spec fn part2_mct_dependency_requests(context:Part2MctRuntimeContext)
    ->Seq<(Part2MctRuntimeCapacity,(Seq<Part2MctComponent>,u64))> {
    part2_mct_dependency_prefix_requests(context)+part2_mct_dependency_scratch_requests(context)
}
pub(crate) open spec fn part2_mct_dependency_value(context:Part2MctRuntimeContext)
    ->(Result<(),crate::DecodeError>,(Seq<Part2MctComponent>,u64)) {
    let value=part2_mct_dependency(context.components,context.collection,context.work,context.maximum_work,context.maximum_bytes);
    (value.0,(value.1,value.2))
}
pub(crate) open spec fn part2_mct_dependency_storage_run(context:Part2MctRuntimeContext,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<Part2MctLineEffect> {
    part2_tier1_storage_bind(part2_mct_auxiliary_program_run(
        part2_mct_dependency_requests(context),part2_mct_dependency_value(context),calls),
        |effect:(Result<(),crate::DecodeError>,(Seq<Part2MctComponent>,u64)),rest|
            Some((Ok((effect.0,effect.1.0,effect.1.1)),rest)))
}
pub(crate) open spec fn part2_mct_dependency_storage_result(context:Part2MctRuntimeContext,result:Part2MctLineEffect)->bool {
    part2_mct_auxiliary_program_result(part2_mct_dependency_requests(context),part2_mct_dependency_value(context),
        (result.0,(result.1,result.2)))
}
pub(crate) proof fn part2_mct_dependency_storage_frames(context:Part2MctRuntimeContext,result:Part2MctLineEffect)
    requires part2_mct_dependency_storage_result(context,result),
    ensures part2_tier1_storage_framed(|calls|part2_mct_dependency_storage_run(context,calls),Ok(result)),
{
    let nested=(result.0,(result.1,result.2));
    part2_tier1_storage_eta(|calls|part2_mct_auxiliary_program_run(
        part2_mct_dependency_requests(context),part2_mct_dependency_value(context),calls),Ok(nested));
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_mct_auxiliary_program_run(
        part2_mct_dependency_requests(context),part2_mct_dependency_value(context),calls),
        |effect:(Result<(),crate::DecodeError>,(Seq<Part2MctComponent>,u64)),rest|
            Some((Ok((effect.0,effect.1.0,effect.1.1)),rest)),Ok(nested),Ok(result));
}
pub(crate) proof fn part2_mct_dependency_storage_normal(context:Part2MctRuntimeContext)
    ensures part2_mct_dependency_storage_result(context,part2_mct_dependency(
        context.components,context.collection,context.work,context.maximum_work,context.maximum_bytes)),
{
    part2_mct_auxiliary_program_normal(part2_mct_dependency_requests(context),part2_mct_dependency_value(context));
}
pub(crate) proof fn part2_mct_dependency_storage_prepare_error(context:Part2MctRuntimeContext,error:crate::DecodeError,charged:u64)
    requires part2_mct_dependency_prepare_storage_result(context,(Err(error),charged)),
    ensures part2_mct_dependency_storage_result(context,(Err(error),context.components,charged)),
{
    let child=part2_mct_dependency_prepare_requests(context);
    let prefix=part2_mct_dependency_prefix_requests(context);
    assert forall|capacity:Part2MctRuntimeCapacity|child.contains((capacity,charged)) ==>
        part2_mct_dependency_requests(context).contains((capacity,(context.components,charged))) by {
        if child.contains((capacity,charged)) {
            let index=choose|i:int|0<=i<child.len() && child[i]==(capacity,charged);
            assert(prefix[index]==(capacity,(context.components,charged)));
            assert(prefix.contains((capacity,(context.components,charged))));
            part2_mct_auxiliary_concat_member(prefix,part2_mct_dependency_scratch_requests(context),
                (capacity,(context.components,charged)));
        }
    }
    part2_mct_auxiliary_program_child_error(part2_mct_dependency_requests(context),part2_mct_dependency_value(context),
        child,part2_mct_dependency_prepare_value(context),error,charged,(context.components,charged));
}
pub(crate) proof fn part2_mct_dependency_storage_scratch_error(context:Part2MctRuntimeContext,
    plan:Part2MctDependencyPreparation,charged:u64,role:Part2MctRuntimeRole,error:crate::DecodeError)
    requires part2_mct_dependency_prepare_value(context)==(Ok(plan),charged),
        role==Part2MctRuntimeRole::SourceSamples || role==Part2MctRuntimeRole::OutputSamples || role==Part2MctRuntimeRole::FractionBits,
        part2_mct_runtime_capacity_result(Part2MctRuntimeCapacity::DependencyScratch {context,role},Err(error)),
    ensures part2_mct_dependency_storage_result(context,(Err(error),context.components,charged)),
{
    let request=(Part2MctRuntimeCapacity::DependencyScratch {context,role},(context.components,charged));
    let scratch=part2_mct_dependency_scratch_requests(context);
    let index=if role==Part2MctRuntimeRole::SourceSamples {0int}else if role==Part2MctRuntimeRole::OutputSamples {1int}else{2int};
    assert(scratch[index]==request);assert(scratch.contains(request));
    part2_mct_auxiliary_concat_member(part2_mct_dependency_prefix_requests(context),scratch,request);
    part2_mct_auxiliary_program_refused(part2_mct_dependency_requests(context),part2_mct_dependency_value(context),
        request.0,request.1,error);
}
}
