//! Source-derived storage at the reached MCT preparation and pixel cutpoints.
use super::*;
verus! {
pub(crate) struct Part2MctRuntimeContext {
    pub components:Seq<Part2MctComponent>,
    pub collection:Part2MctCollection,
    pub work:u64,
    pub maximum_work:u64,
    pub maximum_bytes:u64,
}
pub(crate) enum Part2MctRuntimeRole {
    SourceIndexes,DestinationIndexes,FractionBits,SourceSamples,OutputSamples,
}
pub(crate) enum Part2MctRuntimeCapacity {
    Collection {context:Part2MctRuntimeContext,role:Part2MctRuntimeRole},
    Inverse {matrix:Part2MctArray,source:Seq<i64>},
    PairIndexes {components:Seq<Part2MctComponent>,inputs:Seq<u16>,outputs:Seq<u16>,count:usize,destination:bool},
    WaveletPartition {count:usize,wavelet:Part2MctWavelet,high:bool},
    DependencyScratch {context:Part2MctRuntimeContext,role:Part2MctRuntimeRole},
    WaveletFractions {context:Part2MctRuntimeContext},
    WaveletSource {context:Part2MctRuntimeContext},
    WaveletReconstruction {source:Seq<i64>,high:Seq<usize>,first:Seq<bool>,reversible:bool,low:usize,count:usize},
}
pub(crate) open spec fn part2_mct_runtime_preparation(context:Part2MctRuntimeContext)
    ->(Result<Part2MctDecorrelationPreparation,crate::DecodeError>,u64) {
    part2_mct_prepare_decorrelation(context.components,context.collection,context.work,context.maximum_work,context.maximum_bytes)
}
pub(crate) open spec fn part2_mct_inverse_storage_admitted(matrix:Part2MctArray,source:Seq<i64>)->bool {
    matrix.3==0 && part2_validate_reversible_mct_coefficients(matrix.4,source.len() as usize)==Ok(())
        && source.len()<usize::MAX
}
pub(crate) open spec fn part2_mct_runtime_capacity_count(capacity:Part2MctRuntimeCapacity)->nat {
    match capacity {
        Part2MctRuntimeCapacity::PairIndexes {count,..}=>count as nat,
        Part2MctRuntimeCapacity::WaveletPartition {wavelet,..}=>wavelet.1 as nat,
        Part2MctRuntimeCapacity::DependencyScratch {context,role}=>match part2_mct_prepare_dependency(
            context.components,context.collection,context.work,context.maximum_work,context.maximum_bytes).0 {
                Err(_)=>0,Ok(plan)=>if role==Part2MctRuntimeRole::SourceSamples || role==Part2MctRuntimeRole::OutputSamples
                    || role==Part2MctRuntimeRole::FractionBits {plan.3 as nat}else{0},
            },
        Part2MctRuntimeCapacity::WaveletFractions {context}|Part2MctRuntimeCapacity::WaveletSource {context}=>
            match part2_mct_prepare_wavelet(context.components,context.collection,context.work,context.maximum_work,context.maximum_bytes).0 {
                Err(_)=>0,Ok(plan)=>plan.6 as nat,
            },
        Part2MctRuntimeCapacity::WaveletReconstruction {low,..}=>low as nat,
        Part2MctRuntimeCapacity::Inverse {matrix,source}=>if part2_mct_inverse_storage_admitted(matrix,source){source.len()}else{0},
        Part2MctRuntimeCapacity::Collection {context,role}=>match role {
            Part2MctRuntimeRole::SourceIndexes=>match part2_mct_decorrelation_dimensions(context.collection){Ok((_,columns))=>columns as nat,_=>0},
            Part2MctRuntimeRole::DestinationIndexes=>match part2_mct_decorrelation_dimensions(context.collection){Ok((rows,_))=>rows as nat,_=>0},
            _=>match part2_mct_runtime_preparation(context).0 {
                Err(_)=>0,Ok(plan)=>match role {
                    Part2MctRuntimeRole::FractionBits=>plan.0.len(),
                    Part2MctRuntimeRole::SourceSamples=>plan.5 as nat,
                    Part2MctRuntimeRole::OutputSamples=>plan.4 as nat,
                    _=>0,
                },
            },
        },
    }
}
pub(crate) open spec fn part2_mct_runtime_capacity_run(capacity:Part2MctRuntimeCapacity,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=part2_mct_runtime_capacity_count(capacity);
    if count==0 {Some((Ok(()),calls))}else if calls.len()==0 {None}else{
        match calls[0] {
            Part2Tier1StorageEvent::MctRuntimeCapacity {context:actual,elements,succeeded}=>
                if actual!=capacity || elements!=count {None}else{
                    Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
                },
            _=>None,
        }
    }
}
pub(crate) open spec fn part2_mct_runtime_capacity_result(capacity:Part2MctRuntimeCapacity,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_runtime_capacity_run(capacity,calls),result)
}
pub(crate) proof fn part2_mct_runtime_capacity_observed(capacity:Part2MctRuntimeCapacity,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_mct_runtime_capacity_count(capacity)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_mct_runtime_capacity_result(capacity,result),
{
    let count=part2_mct_runtime_capacity_count(capacity);
    let prefix=if count==0 {Seq::empty()}else{
        seq![Part2Tier1StorageEvent::MctRuntimeCapacity {context:capacity,elements:count,succeeded:result.is_ok()}]
    };
    assert forall|tail:Seq<Part2Tier1StorageEvent>|
        part2_mct_runtime_capacity_run(capacity,prefix+tail)==Some((result,tail)) by {
        if count==0 {assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_mct_runtime_capacity_run(capacity,calls),prefix,result));
}
pub(crate) proof fn part2_mct_runtime_capacity_normal(capacity:Part2MctRuntimeCapacity)
    ensures part2_mct_runtime_capacity_result(capacity,Ok(())),
{part2_mct_runtime_capacity_observed(capacity,Ok(()));}
pub(crate) open spec fn part2_mct_collection_capacity(context:Part2MctRuntimeContext,role:Part2MctRuntimeRole)->Part2MctRuntimeCapacity {
    Part2MctRuntimeCapacity::Collection {context,role}
}
pub(crate) open spec fn part2_mct_prepare_storage_roles(context:Part2MctRuntimeContext)->Seq<Part2MctRuntimeRole> {
    if part2_mct_decorrelation_dimensions(context.collection).is_err(){Seq::empty()}else{
        seq![Part2MctRuntimeRole::SourceIndexes,Part2MctRuntimeRole::DestinationIndexes]
            + if part2_mct_runtime_preparation(context).0.is_ok(){seq![Part2MctRuntimeRole::FractionBits]}else{Seq::empty()}
    }
}
pub(crate) open spec fn part2_mct_prepare_refused_work(context:Part2MctRuntimeContext,role:Part2MctRuntimeRole)->u64 {
    if role==Part2MctRuntimeRole::FractionBits {part2_mct_runtime_preparation(context).1}else{context.work}
}
pub(crate) open spec fn part2_mct_prepare_storage_next(context:Part2MctRuntimeContext,roles:Seq<Part2MctRuntimeRole>,
    capacity:Result<(),crate::DecodeError>,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<(Result<Part2MctDecorrelationPreparation,crate::DecodeError>,u64)>
    decreases roles.len()*2,
{
    if roles.len()==0 {Some((Ok(part2_mct_runtime_preparation(context)),calls))}else{match capacity {
        Err(error)=>Some((Ok((Err(error),part2_mct_prepare_refused_work(context,roles[0]))),calls)),
        Ok(())=>part2_mct_prepare_storage_requests_run(context,roles.drop_first(),calls),
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_mct_prepare_storage_requests_run(context:Part2MctRuntimeContext,roles:Seq<Part2MctRuntimeRole>,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<(Result<Part2MctDecorrelationPreparation,crate::DecodeError>,u64)>
    decreases roles.len()*2+1,
{
    if roles.len()==0 {Some((Ok(part2_mct_runtime_preparation(context)),calls))}else{
        part2_tier1_storage_resume(part2_mct_runtime_capacity_run(part2_mct_collection_capacity(context,roles[0]),calls),
            |capacity,rest|part2_mct_prepare_storage_next(context,roles,capacity,rest))
    }
}
pub(crate) open spec fn part2_mct_prepare_storage_run(context:Part2MctRuntimeContext,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<(Result<Part2MctDecorrelationPreparation,crate::DecodeError>,u64)> {
    part2_mct_prepare_storage_requests_run(context,part2_mct_prepare_storage_roles(context),calls)
}
pub(crate) open spec fn part2_mct_prepare_storage_result(context:Part2MctRuntimeContext,result:(Result<Part2MctDecorrelationPreparation,crate::DecodeError>,u64))->bool {
    part2_tier1_storage_framed(|calls|part2_mct_prepare_storage_run(context,calls),Ok(result))
}
pub(crate) proof fn part2_mct_prepare_storage_requests_normal(context:Part2MctRuntimeContext,roles:Seq<Part2MctRuntimeRole>)
    ensures part2_tier1_storage_framed(|calls|part2_mct_prepare_storage_requests_run(context,roles,calls),Ok(part2_mct_runtime_preparation(context))),
    decreases roles.len(),
{
    reveal(part2_mct_prepare_storage_requests_run);
    if roles.len()==0 {part2_tier1_storage_pure(Ok(part2_mct_runtime_preparation(context)));}else{
        part2_mct_runtime_capacity_normal(part2_mct_collection_capacity(context,roles[0]));
        part2_mct_prepare_storage_requests_normal(context,roles.drop_first());
        part2_tier1_storage_eta(|calls|part2_mct_prepare_storage_requests_run(context,roles.drop_first(),calls),Ok(part2_mct_runtime_preparation(context)));
        part2_tier1_resume_frame(|calls|part2_mct_runtime_capacity_run(part2_mct_collection_capacity(context,roles[0]),calls),
            |capacity,rest|part2_mct_prepare_storage_next(context,roles,capacity,rest),Ok(()),Ok(part2_mct_runtime_preparation(context)));
    }
}
pub(crate) proof fn part2_mct_prepare_storage_normal(context:Part2MctRuntimeContext)
    ensures part2_mct_prepare_storage_result(context,part2_mct_runtime_preparation(context)),
{
    part2_mct_prepare_storage_requests_normal(context,part2_mct_prepare_storage_roles(context));
    part2_tier1_storage_eta(|calls|part2_mct_prepare_storage_requests_run(context,part2_mct_prepare_storage_roles(context),calls),
        Ok(part2_mct_runtime_preparation(context)));
}
pub(crate) proof fn part2_mct_prepare_storage_requests_refused(context:Part2MctRuntimeContext,roles:Seq<Part2MctRuntimeRole>,position:nat,error:crate::DecodeError)
    requires position<roles.len(),part2_mct_runtime_capacity_result(part2_mct_collection_capacity(context,roles[position as int]),Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_mct_prepare_storage_requests_run(context,roles,calls),
        Ok((Err(error),part2_mct_prepare_refused_work(context,roles[position as int])))),
    decreases position,
{
    reveal(part2_mct_prepare_storage_requests_run);
    let result=(Err::<Part2MctDecorrelationPreparation,crate::DecodeError>(error),part2_mct_prepare_refused_work(context,roles[position as int]));
    let capacity=part2_mct_collection_capacity(context,roles[0]);
    if position==0 {
        part2_tier1_storage_pure(Ok(result));
        part2_tier1_resume_frame(|calls|part2_mct_runtime_capacity_run(capacity,calls),
            |capacity,rest|part2_mct_prepare_storage_next(context,roles,capacity,rest),Err(error),Ok(result));
    }else{
        assert(roles.drop_first()[position as int-1]==roles[position as int]);
        part2_mct_prepare_storage_requests_refused(context,roles.drop_first(),(position-1) as nat,error);
        part2_tier1_storage_eta(|calls|part2_mct_prepare_storage_requests_run(context,roles.drop_first(),calls),Ok(result));
        part2_mct_runtime_capacity_normal(capacity);
        part2_tier1_resume_frame(|calls|part2_mct_runtime_capacity_run(capacity,calls),
            |capacity,rest|part2_mct_prepare_storage_next(context,roles,capacity,rest),Ok(()),Ok(result));
    }
}
pub(crate) proof fn part2_mct_prepare_storage_refused(context:Part2MctRuntimeContext,position:nat,error:crate::DecodeError)
    requires position<part2_mct_prepare_storage_roles(context).len(),
        part2_mct_runtime_capacity_result(part2_mct_collection_capacity(context,part2_mct_prepare_storage_roles(context)[position as int]),Err(error)),
    ensures part2_mct_prepare_storage_result(context,
        (Err(error),part2_mct_prepare_refused_work(context,part2_mct_prepare_storage_roles(context)[position as int]))),
{
    part2_mct_prepare_storage_requests_refused(context,part2_mct_prepare_storage_roles(context),position,error);
    part2_tier1_storage_eta(|calls|part2_mct_prepare_storage_requests_run(context,part2_mct_prepare_storage_roles(context),calls),
        Ok((Err::<Part2MctDecorrelationPreparation,crate::DecodeError>(error),
            part2_mct_prepare_refused_work(context,part2_mct_prepare_storage_roles(context)[position as int]))));
}

pub(crate) proof fn part2_mct_scale_no_allocation(values:Seq<i64>,width:usize,count:nat)
    ensures part2_mct_scale_prefix(values,width,count)!=Err(crate::DecodeError::AllocationFailed),
    decreases count,
{
    reveal(part2_mct_scale_prefix);
    if count>0 {part2_mct_scale_no_allocation(values,width,(count-1) as nat);}
}
pub(crate) proof fn part2_mct_sum_no_allocation(initial:i128,matrix:Part2MctArray,source:Seq<i64>,start:usize,target:usize,count:nat)
    ensures part2_reversible_mct_sum(initial,matrix,source,start,target,count)!=Err(crate::DecodeError::AllocationFailed),
    decreases count,
{
    reveal(part2_reversible_mct_sum);
    if count>0 {part2_mct_sum_no_allocation(initial,matrix,source,start,target,(count-1) as nat);}
}
pub(crate) proof fn part2_mct_stage_no_allocation(matrix:Part2MctArray,source:Seq<i64>,stage:usize)
    ensures part2_reversible_mct_stage(matrix,source,stage)!=Err(crate::DecodeError::AllocationFailed),
{
    let width=source.len();
    if width>0 && stage<=width && matrix.3==0 {
        let target=if stage==width {width as int-1}else{width as int-1-stage as int};
        let start=stage as int*width as int;
        if start<=usize::MAX && start+target<=usize::MAX && start+target<matrix.4.len() {
            let pivot=matrix.4[start+target];
            if let Ok(divisor)=part2_reversible_mct_scale(pivot,stage==width) {
                part2_mct_sum_no_allocation((divisor/2) as i128,matrix,source,start as usize,target as usize,width);
            }
        }
    }
}
pub(crate) proof fn part2_mct_stages_no_allocation(matrix:Part2MctArray,source:Seq<i64>,count:nat)
    ensures part2_reversible_mct_stages(matrix,source,count)!=Err(crate::DecodeError::AllocationFailed),
    decreases count,
{
    reveal(part2_reversible_mct_stages);
    if count>0 {
        part2_mct_stages_no_allocation(matrix,source,(count-1) as nat);
        if let Ok(previous)=part2_reversible_mct_stages(matrix,source,(count-1) as nat) {
            if count-1<=usize::MAX {part2_mct_stage_no_allocation(matrix,previous,(count-1) as usize);}
        }
    }
}
pub(crate) proof fn part2_mct_inverse_no_allocation(matrix:Part2MctArray,source:Seq<i64>)
    ensures part2_inverse_reversible_mct(matrix,source)!=Err(crate::DecodeError::AllocationFailed),
{
    let width=source.len() as usize;
    part2_mct_scale_no_allocation(matrix.4,width,(width as nat+1) as nat);
    part2_mct_stages_no_allocation(matrix,source,(source.len()+1) as nat);
}

pub(crate) open spec fn part2_mct_inverse_storage_run(matrix:Part2MctArray,source:Seq<i64>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    if !part2_mct_inverse_storage_admitted(matrix,source){Some((part2_inverse_reversible_mct(matrix,source),calls))}else{
        part2_tier1_storage_bind(part2_mct_runtime_capacity_run(Part2MctRuntimeCapacity::Inverse {matrix,source},calls),
            |_:(),rest|Some((part2_inverse_reversible_mct(matrix,source),rest)))
    }
}
pub(crate) open spec fn part2_mct_inverse_storage_result(matrix:Part2MctArray,source:Seq<i64>,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_inverse_storage_run(matrix,source,calls),result)
}
pub(crate) proof fn part2_mct_inverse_storage_normal(matrix:Part2MctArray,source:Seq<i64>)
    ensures part2_mct_inverse_storage_result(matrix,source,part2_inverse_reversible_mct(matrix,source)),
{
    let result=part2_inverse_reversible_mct(matrix,source);part2_tier1_storage_pure(result);
    if part2_mct_inverse_storage_admitted(matrix,source) {
        let capacity=Part2MctRuntimeCapacity::Inverse {matrix,source};
        part2_mct_runtime_capacity_normal(capacity);
        part2_tier1_storage_bind_frame(|calls|part2_mct_runtime_capacity_run(capacity,calls),
            |_:(),rest|Some((result,rest)),Ok(()),result);
    }
}
pub(crate) proof fn part2_mct_inverse_storage_refused(matrix:Part2MctArray,source:Seq<i64>,error:crate::DecodeError)
    requires part2_mct_inverse_storage_admitted(matrix,source),
        part2_mct_runtime_capacity_result(Part2MctRuntimeCapacity::Inverse {matrix,source},Err(error)),
    ensures part2_mct_inverse_storage_result(matrix,source,Err(error)),
{
    part2_tier1_storage_bind_frame(|calls|part2_mct_runtime_capacity_run(Part2MctRuntimeCapacity::Inverse {matrix,source},calls),
        |_:(),rest|Some((part2_inverse_reversible_mct(matrix,source),rest)),Err(error),Err(error));
}

pub(crate) open spec fn part2_mct_reversible_row_storage_run(matrix:Part2MctArray,offsets:Option<Part2MctArray>,
    source:Seq<i64>,row:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<i64> {
    if matrix.3!=0 || (match offsets {Some(array)=>array.3!=0,None=>false}) {
        Some((part2_reversible_mct_row(matrix,offsets,source,row),calls))
    }else{
        part2_tier1_storage_bind(part2_mct_inverse_storage_run(matrix,source,calls),
            |values,rest|Some((part2_reversible_mct_output(values,offsets,row),rest)))
    }
}
pub(crate) open spec fn part2_mct_reversible_row_storage_result(matrix:Part2MctArray,offsets:Option<Part2MctArray>,
    source:Seq<i64>,row:usize,result:Result<i64,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_reversible_row_storage_run(matrix,offsets,source,row,calls),result)
}
pub(crate) proof fn part2_mct_reversible_row_storage_normal(matrix:Part2MctArray,offsets:Option<Part2MctArray>,source:Seq<i64>,row:usize)
    ensures part2_mct_reversible_row_storage_result(matrix,offsets,source,row,part2_reversible_mct_row(matrix,offsets,source,row)),
{
    let result=part2_reversible_mct_row(matrix,offsets,source,row);
    part2_tier1_storage_pure(result);
    if matrix.3==0 && (match offsets {Some(array)=>array.3==0,None=>true}) {
        let inverted=part2_inverse_reversible_mct(matrix,source);
        part2_mct_inverse_storage_normal(matrix,source);
        if let Ok(values)=inverted {part2_tier1_storage_pure(part2_reversible_mct_output(values,offsets,row));}
        part2_tier1_storage_bind_frame(|calls|part2_mct_inverse_storage_run(matrix,source,calls),
            |values,rest|Some((part2_reversible_mct_output(values,offsets,row),rest)),inverted,result);
    }
}
pub(crate) proof fn part2_mct_reversible_row_storage_observed(matrix:Part2MctArray,offsets:Option<Part2MctArray>,source:Seq<i64>,row:usize,
    inverted:Result<Seq<i64>,crate::DecodeError>,result:Result<i64,crate::DecodeError>)
    requires matrix.3==0,(match offsets {Some(array)=>array.3==0,None=>true}),
        part2_mct_inverse_storage_result(matrix,source,inverted),
        result==(match inverted {Err(error)=>Err(error),Ok(values)=>part2_reversible_mct_output(values,offsets,row)}),
    ensures part2_mct_reversible_row_storage_result(matrix,offsets,source,row,result),
{
    if let Ok(values)=inverted {part2_tier1_storage_pure(part2_reversible_mct_output(values,offsets,row));}
    part2_tier1_storage_bind_frame(|calls|part2_mct_inverse_storage_run(matrix,source,calls),
        |values,rest|Some((part2_reversible_mct_output(values,offsets,row),rest)),inverted,result);
}
pub(crate) open spec fn part2_mct_scalar_storage_run(collection:Part2MctCollection,source:Seq<i64>,fractions:Seq<u8>,row:usize,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<i64> {
    if collection.0 && collection.4.is_some() {
        part2_mct_reversible_row_storage_run(collection.4.unwrap(),collection.5,source,row,calls)
    }else{Some((part2_mct_decorrelation_row(collection,source,fractions,row),calls))}
}
pub(crate) open spec fn part2_mct_scalar_storage_result(collection:Part2MctCollection,source:Seq<i64>,fractions:Seq<u8>,row:usize,
    result:Result<i64,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_scalar_storage_run(collection,source,fractions,row,calls),result)
        && ((!collection.0 || collection.4.is_none()) ==> result==part2_mct_decorrelation_row(collection,source,fractions,row))
}
pub(crate) proof fn part2_mct_scalar_storage_normal(collection:Part2MctCollection,source:Seq<i64>,fractions:Seq<u8>,row:usize)
    ensures part2_mct_scalar_storage_result(collection,source,fractions,row,part2_mct_decorrelation_row(collection,source,fractions,row)),
{
    let result=part2_mct_decorrelation_row(collection,source,fractions,row);
    if collection.0 && collection.4.is_some() {
        part2_mct_reversible_row_storage_normal(collection.4.unwrap(),collection.5,source,row);
        part2_tier1_storage_eta(|calls|part2_mct_reversible_row_storage_run(collection.4.unwrap(),collection.5,source,row,calls),result);
    }else{part2_tier1_storage_pure(result);}
}
pub(crate) proof fn part2_mct_scalar_storage_reversible_observed(collection:Part2MctCollection,source:Seq<i64>,fractions:Seq<u8>,row:usize,
    result:Result<i64,crate::DecodeError>)
    requires collection.0,collection.4.is_some(),part2_mct_reversible_row_storage_result(collection.4.unwrap(),collection.5,source,row,result),
    ensures part2_mct_scalar_storage_result(collection,source,fractions,row,result),
{
    part2_tier1_storage_eta(|calls|part2_mct_reversible_row_storage_run(collection.4.unwrap(),collection.5,source,row,calls),result);
}

pub(crate) struct Part2MctRowsStorageContext {
    pub output:Seq<i64>,pub collection:Part2MctCollection,pub source:Seq<i64>,pub fractions:Seq<u8>,pub rows:usize,
}
pub(crate) open spec fn part2_mct_rows_storage_value(context:Part2MctRowsStorageContext)->(Result<(),crate::DecodeError>,Seq<i64>) {
    part2_mct_decorrelation_rows(context.output,context.collection,context.source,context.fractions,context.rows as nat)
}
pub(crate) open spec fn part2_mct_rows_uses_inverse(context:Part2MctRowsStorageContext)->bool {
    context.rows>0 && context.collection.0 && context.collection.4.is_some()
        && (match context.collection.5 {Some(offsets)=>offsets.3==0,None=>true})
}
pub(crate) open spec fn part2_mct_rows_storage_after(context:Part2MctRowsStorageContext,result:Result<Seq<i64>,crate::DecodeError>)
    ->(Result<(),crate::DecodeError>,Seq<i64>) {
    if result==Err(crate::DecodeError::AllocationFailed){(Err(crate::DecodeError::AllocationFailed),context.output)}
    else{part2_mct_rows_storage_value(context)}
}
pub(crate) open spec fn part2_mct_rows_storage_run(context:Part2MctRowsStorageContext,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<(Result<(),crate::DecodeError>,Seq<i64>)> {
    if !part2_mct_rows_uses_inverse(context){Some((Ok(part2_mct_rows_storage_value(context)),calls))}else{
        part2_tier1_storage_resume(part2_mct_inverse_storage_run(context.collection.4.unwrap(),context.source,calls),
            |result,rest|Some((Ok(part2_mct_rows_storage_after(context,result)),rest)))
    }
}
pub(crate) open spec fn part2_mct_rows_storage_result(context:Part2MctRowsStorageContext,result:(Result<(),crate::DecodeError>,Seq<i64>))->bool {
    part2_tier1_storage_framed(|calls|part2_mct_rows_storage_run(context,calls),Ok(result))
}
pub(crate) proof fn part2_mct_rows_storage_normal(context:Part2MctRowsStorageContext)
    ensures part2_mct_rows_storage_result(context,part2_mct_rows_storage_value(context)),
{
    let result=part2_mct_rows_storage_value(context);part2_tier1_storage_pure(Ok(result));
    if part2_mct_rows_uses_inverse(context){
        let matrix=context.collection.4.unwrap();
        let computed=part2_inverse_reversible_mct(matrix,context.source);
        part2_mct_inverse_no_allocation(matrix,context.source);
        assert(computed!=Err(crate::DecodeError::AllocationFailed));
        part2_mct_inverse_storage_normal(matrix,context.source);
        part2_tier1_resume_frame(|calls|part2_mct_inverse_storage_run(matrix,context.source,calls),
            |computed,rest|Some((Ok(part2_mct_rows_storage_after(context,computed)),rest)),computed,Ok(result));
    }
}
pub(crate) proof fn part2_mct_rows_storage_inverse_error(context:Part2MctRowsStorageContext)
    requires part2_mct_rows_uses_inverse(context),
        part2_mct_inverse_storage_result(context.collection.4.unwrap(),context.source,Err(crate::DecodeError::AllocationFailed)),
    ensures part2_mct_rows_storage_result(context,(Err(crate::DecodeError::AllocationFailed),context.output)),
{
    let result=(Err::<(),crate::DecodeError>(crate::DecodeError::AllocationFailed),context.output);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_resume_frame(|calls|part2_mct_inverse_storage_run(context.collection.4.unwrap(),context.source,calls),
        |computed,rest|Some((Ok(part2_mct_rows_storage_after(context,computed)),rest)),Err(crate::DecodeError::AllocationFailed),Ok(result));
}

pub(crate) type Part2MctRuntimePixelEffect=(Result<(),crate::DecodeError>,Seq<Part2MctComponent>,Seq<i64>,Seq<i64>);
pub(crate) type Part2MctRuntimePixelsEffect=(Result<(),crate::DecodeError>,Seq<Part2MctComponent>);
pub(crate) open spec fn part2_mct_pixel_rows_context(before:Seq<Part2MctComponent>,collection:Part2MctCollection,
    plan:Part2MctDecorrelationPreparation,sample:usize)->Part2MctRowsStorageContext {
    let snapshot=part2_mct_source_snapshot(before,plan.0,sample,plan.0.len());
    Part2MctRowsStorageContext {output:Seq::empty(),collection,source:snapshot.1,fractions:plan.2,rows:plan.4}
}
pub(crate) open spec fn part2_mct_pixel_storage_after_rows(before:Seq<Part2MctComponent>,plan:Part2MctDecorrelationPreparation,
    sample:usize,source:Seq<i64>,rows:(Result<(),crate::DecodeError>,Seq<i64>))->Part2MctRuntimePixelEffect {
    match rows.0 {
        Err(error)=>(Err(error),before,source,rows.1),
        Ok(())=>{
            let stored=part2_mct_store_output_rows(before,plan.1,rows.1,sample,plan.4 as nat);
            (stored.0,stored.1,source,rows.1)
        },
    }
}
pub(crate) open spec fn part2_mct_pixel_storage_run(before:Seq<Part2MctComponent>,collection:Part2MctCollection,
    plan:Part2MctDecorrelationPreparation,sample:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctRuntimePixelEffect> {
    let snapshot=part2_mct_source_snapshot(before,plan.0,sample,plan.0.len());
    match snapshot.0 {
        Err(error)=>Some((Ok((Err(error),before,snapshot.1,Seq::empty())),calls)),
        Ok(())=>part2_tier1_storage_bind(part2_mct_rows_storage_run(part2_mct_pixel_rows_context(before,collection,plan,sample),calls),
            |rows,rest|Some((Ok(part2_mct_pixel_storage_after_rows(before,plan,sample,snapshot.1,rows)),rest))),
    }
}
pub(crate) open spec fn part2_mct_pixel_storage_result(before:Seq<Part2MctComponent>,collection:Part2MctCollection,
    plan:Part2MctDecorrelationPreparation,sample:usize,result:Part2MctRuntimePixelEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_pixel_storage_run(before,collection,plan,sample,calls),Ok(result))
}
pub(crate) proof fn part2_mct_pixel_storage_normal(before:Seq<Part2MctComponent>,collection:Part2MctCollection,plan:Part2MctDecorrelationPreparation,sample:usize)
    ensures part2_mct_pixel_storage_result(before,collection,plan,sample,part2_mct_decorrelation_pixel(before,collection,plan,sample)),
{
    let result=part2_mct_decorrelation_pixel(before,collection,plan,sample);
    part2_tier1_storage_pure(Ok(result));
    let snapshot=part2_mct_source_snapshot(before,plan.0,sample,plan.0.len());
    if snapshot.0.is_ok() {
        let context=part2_mct_pixel_rows_context(before,collection,plan,sample);
        let rows=part2_mct_rows_storage_value(context);
        part2_mct_rows_storage_normal(context);
        part2_tier1_storage_bind_frame(|calls|part2_mct_rows_storage_run(context,calls),
            |rows,rest|Some((Ok(part2_mct_pixel_storage_after_rows(before,plan,sample,snapshot.1,rows)),rest)),Ok(rows),Ok(result));
    }
}
pub(crate) proof fn part2_mct_pixel_storage_rows_observed(before:Seq<Part2MctComponent>,collection:Part2MctCollection,
    plan:Part2MctDecorrelationPreparation,sample:usize,rows:(Result<(),crate::DecodeError>,Seq<i64>))
    requires part2_mct_source_snapshot(before,plan.0,sample,plan.0.len()).0.is_ok(),
        part2_mct_rows_storage_result(part2_mct_pixel_rows_context(before,collection,plan,sample),rows),
    ensures part2_mct_pixel_storage_result(before,collection,plan,sample,
        part2_mct_pixel_storage_after_rows(before,plan,sample,part2_mct_source_snapshot(before,plan.0,sample,plan.0.len()).1,rows)),
{
    let context=part2_mct_pixel_rows_context(before,collection,plan,sample);
    let snapshot=part2_mct_source_snapshot(before,plan.0,sample,plan.0.len());
    let result=part2_mct_pixel_storage_after_rows(before,plan,sample,snapshot.1,rows);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_mct_rows_storage_run(context,calls),
        |rows,rest|Some((Ok(part2_mct_pixel_storage_after_rows(before,plan,sample,snapshot.1,rows)),rest)),Ok(rows),Ok(result));
}
pub(crate) open spec fn part2_mct_pixels_storage_next(previous:Part2MctRuntimePixelsEffect,collection:Part2MctCollection,
    plan:Part2MctDecorrelationPreparation,index:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctRuntimePixelsEffect> {
    if previous.0.is_err(){Some((Ok(previous),calls))}else if index>usize::MAX {
        Some((Ok((Err(part1_transform_error(true)),previous.1)),calls))
    }else{
        part2_tier1_storage_bind(part2_mct_pixel_storage_run(previous.1,collection,plan,index as usize,calls),
            |pixel:Part2MctRuntimePixelEffect,rest|Some((Ok((pixel.0,pixel.1)),rest)))
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_mct_pixels_storage_run(before:Seq<Part2MctComponent>,collection:Part2MctCollection,
    plan:Part2MctDecorrelationPreparation,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctRuntimePixelsEffect>
    decreases count,
{
    if count==0 {Some((Ok((Ok(()),before)),calls))}else{
        part2_tier1_storage_bind(part2_mct_pixels_storage_run(before,collection,plan,(count-1) as nat,calls),
            |previous,rest|part2_mct_pixels_storage_next(previous,collection,plan,(count-1) as nat,rest))
    }
}
pub(crate) open spec fn part2_mct_pixels_storage_result(before:Seq<Part2MctComponent>,collection:Part2MctCollection,
    plan:Part2MctDecorrelationPreparation,count:nat,result:Part2MctRuntimePixelsEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_pixels_storage_run(before,collection,plan,count,calls),Ok(result))
}
pub(crate) proof fn part2_mct_pixels_storage_normal(before:Seq<Part2MctComponent>,collection:Part2MctCollection,plan:Part2MctDecorrelationPreparation,count:nat)
    ensures part2_mct_pixels_storage_result(before,collection,plan,count,part2_mct_decorrelation_pixels(before,collection,plan,count)),
    decreases count,
{
    reveal(part2_mct_pixels_storage_run);reveal(part2_mct_decorrelation_pixels);
    let result=part2_mct_decorrelation_pixels(before,collection,plan,count);
    part2_tier1_storage_pure(Ok(result));
    if count>0 {
        let previous=part2_mct_decorrelation_pixels(before,collection,plan,(count-1) as nat);
        part2_mct_pixels_storage_normal(before,collection,plan,(count-1) as nat);
        if previous.0.is_ok() && count-1<=usize::MAX {
            let pixel=part2_mct_decorrelation_pixel(previous.1,collection,plan,(count-1) as usize);
            part2_mct_pixel_storage_normal(previous.1,collection,plan,(count-1) as usize);
            part2_tier1_storage_bind_frame(|calls|part2_mct_pixel_storage_run(previous.1,collection,plan,(count-1) as usize,calls),
                |pixel:Part2MctRuntimePixelEffect,rest|Some((Ok((pixel.0,pixel.1)),rest)),Ok(pixel),Ok(result));
        }
        part2_tier1_storage_eta(|calls|part2_mct_pixels_storage_run(before,collection,plan,(count-1) as nat,calls),Ok(previous));
        part2_tier1_storage_bind_frame(|calls|part2_mct_pixels_storage_run(before,collection,plan,(count-1) as nat,calls),
            |previous,rest|part2_mct_pixels_storage_next(previous,collection,plan,(count-1) as nat,rest),Ok(previous),Ok(result));
    }
}
pub(crate) proof fn part2_mct_pixels_storage_advance(before:Seq<Part2MctComponent>,collection:Part2MctCollection,
    plan:Part2MctDecorrelationPreparation,index:nat,current:Seq<Part2MctComponent>,pixel:Part2MctRuntimePixelEffect)
    requires index<=usize::MAX,part2_mct_pixels_storage_result(before,collection,plan,index,(Ok(()),current)),
        part2_mct_pixel_storage_result(current,collection,plan,index as usize,pixel),
    ensures part2_mct_pixels_storage_result(before,collection,plan,index+1,(pixel.0,pixel.1)),
{
    reveal(part2_mct_pixels_storage_run);
    let result=(pixel.0,pixel.1);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_mct_pixel_storage_run(current,collection,plan,index as usize,calls),
        |pixel:Part2MctRuntimePixelEffect,rest|Some((Ok((pixel.0,pixel.1)),rest)),Ok(pixel),Ok(result));
    part2_tier1_storage_eta(|calls|part2_mct_pixels_storage_run(before,collection,plan,index,calls),Ok((Ok::<(),crate::DecodeError>(()),current)));
    part2_tier1_storage_bind_frame(|calls|part2_mct_pixels_storage_run(before,collection,plan,index,calls),
        |previous,rest|part2_mct_pixels_storage_next(previous,collection,plan,index,rest),Ok((Ok(()),current)),Ok(result));
}
pub(crate) proof fn part2_mct_pixels_storage_error_suffix(before:Seq<Part2MctComponent>,collection:Part2MctCollection,
    plan:Part2MctDecorrelationPreparation,prefix:nat,count:nat,result:Part2MctRuntimePixelsEffect)
    requires prefix<=count,result.0.is_err(),part2_mct_pixels_storage_result(before,collection,plan,prefix,result),
    ensures part2_mct_pixels_storage_result(before,collection,plan,count,result),
    decreases count-prefix,
{
    if prefix<count {
        reveal(part2_mct_pixels_storage_run);
        part2_mct_pixels_storage_error_suffix(before,collection,plan,prefix,(count-1) as nat,result);
        part2_tier1_storage_eta(|calls|part2_mct_pixels_storage_run(before,collection,plan,(count-1) as nat,calls),Ok(result));
        part2_tier1_storage_pure(Ok(result));
        part2_tier1_storage_bind_frame(|calls|part2_mct_pixels_storage_run(before,collection,plan,(count-1) as nat,calls),
            |previous,rest|part2_mct_pixels_storage_next(previous,collection,plan,(count-1) as nat,rest),Ok(result),Ok(result));
    }
}

pub(crate) open spec fn part2_mct_decorrelation_storage_finish(plan:Part2MctDecorrelationPreparation,charged:u64,pixels:Part2MctRuntimePixelsEffect,
    reversible:bool)->Part2MctLineEffect {
    match pixels.0 {
        Err(error)=>(Err(error),pixels.1,charged),
        Ok(())=>{
            let tagged=part2_mct_destination_precisions(pixels.1,plan.1,if reversible{0}else{32},plan.1.len());
            (tagged.0,tagged.1,charged)
        },
    }
}
pub(crate) open spec fn part2_mct_decorrelation_after_output(context:Part2MctRuntimeContext,plan:Part2MctDecorrelationPreparation,charged:u64,
    capacity:Result<(),crate::DecodeError>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLineEffect> {
    match capacity {
        Err(error)=>Some((Ok((Err(error),context.components,charged)),calls)),
        Ok(())=>part2_tier1_storage_bind(part2_mct_pixels_storage_run(context.components,context.collection,plan,plan.3 as nat,calls),
            |pixels,rest|Some((Ok(part2_mct_decorrelation_storage_finish(plan,charged,pixels,context.collection.0)),rest))),
    }
}
pub(crate) open spec fn part2_mct_decorrelation_after_source(context:Part2MctRuntimeContext,plan:Part2MctDecorrelationPreparation,charged:u64,
    capacity:Result<(),crate::DecodeError>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLineEffect> {
    match capacity {
        Err(error)=>Some((Ok((Err(error),context.components,charged)),calls)),
        Ok(())=>part2_tier1_storage_resume(part2_mct_runtime_capacity_run(part2_mct_collection_capacity(context,Part2MctRuntimeRole::OutputSamples),calls),
            |capacity,rest|part2_mct_decorrelation_after_output(context,plan,charged,capacity,rest)),
    }
}
pub(crate) open spec fn part2_mct_decorrelation_after_preparation(context:Part2MctRuntimeContext,
    prepared:(Result<Part2MctDecorrelationPreparation,crate::DecodeError>,u64),calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLineEffect> {
    match prepared.0 {
        Err(error)=>Some((Ok((Err(error),context.components,prepared.1)),calls)),
        Ok(plan)=>part2_tier1_storage_resume(part2_mct_runtime_capacity_run(part2_mct_collection_capacity(context,Part2MctRuntimeRole::SourceSamples),calls),
            |capacity,rest|part2_mct_decorrelation_after_source(context,plan,prepared.1,capacity,rest)),
    }
}
pub(crate) open spec fn part2_mct_decorrelation_storage_run(context:Part2MctRuntimeContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2MctLineEffect> {
    part2_tier1_storage_bind(part2_mct_prepare_storage_run(context,calls),
        |prepared,rest|part2_mct_decorrelation_after_preparation(context,prepared,rest))
}
pub(crate) open spec fn part2_mct_decorrelation_storage_result(context:Part2MctRuntimeContext,result:Part2MctLineEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_mct_decorrelation_storage_run(context,calls),Ok(result))
}
pub(crate) proof fn part2_mct_decorrelation_storage_from_prepared(context:Part2MctRuntimeContext,
    prepared:(Result<Part2MctDecorrelationPreparation,crate::DecodeError>,u64),result:Part2MctLineEffect)
    requires part2_mct_prepare_storage_result(context,prepared),
        part2_tier1_storage_framed(|calls|part2_mct_decorrelation_after_preparation(context,prepared,calls),Ok(result)),
    ensures part2_mct_decorrelation_storage_result(context,result),
{
    part2_tier1_storage_eta(|calls|part2_mct_prepare_storage_run(context,calls),Ok(prepared));
    part2_tier1_storage_eta(|calls|part2_mct_decorrelation_after_preparation(context,prepared,calls),Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_mct_prepare_storage_run(context,calls),
        |prepared,rest|part2_mct_decorrelation_after_preparation(context,prepared,rest),Ok(prepared),Ok(result));
}
pub(crate) proof fn part2_mct_decorrelation_storage_pixels(context:Part2MctRuntimeContext,plan:Part2MctDecorrelationPreparation,charged:u64,
    pixels:Part2MctRuntimePixelsEffect)
    requires part2_mct_prepare_storage_result(context,(Ok(plan),charged)),
        part2_mct_runtime_capacity_result(part2_mct_collection_capacity(context,Part2MctRuntimeRole::SourceSamples),Ok(())),
        part2_mct_runtime_capacity_result(part2_mct_collection_capacity(context,Part2MctRuntimeRole::OutputSamples),Ok(())),
        part2_mct_pixels_storage_result(context.components,context.collection,plan,plan.3 as nat,pixels),
    ensures part2_mct_decorrelation_storage_result(context,part2_mct_decorrelation_storage_finish(plan,charged,pixels,context.collection.0)),
{
    let result=part2_mct_decorrelation_storage_finish(plan,charged,pixels,context.collection.0);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_eta(|calls|part2_mct_pixels_storage_run(context.components,context.collection,plan,plan.3 as nat,calls),Ok(pixels));
    part2_tier1_storage_bind_frame(|calls|part2_mct_pixels_storage_run(context.components,context.collection,plan,plan.3 as nat,calls),
        |pixels,rest|Some((Ok(part2_mct_decorrelation_storage_finish(plan,charged,pixels,context.collection.0)),rest)),Ok(pixels),Ok(result));
    part2_tier1_resume_frame(|calls|part2_mct_runtime_capacity_run(part2_mct_collection_capacity(context,Part2MctRuntimeRole::OutputSamples),calls),
        |capacity,rest|part2_mct_decorrelation_after_output(context,plan,charged,capacity,rest),Ok(()),Ok(result));
    part2_tier1_resume_frame(|calls|part2_mct_runtime_capacity_run(part2_mct_collection_capacity(context,Part2MctRuntimeRole::SourceSamples),calls),
        |capacity,rest|part2_mct_decorrelation_after_source(context,plan,charged,capacity,rest),Ok(()),Ok(result));
    part2_mct_decorrelation_storage_from_prepared(context,(Ok(plan),charged),result);
}
pub(crate) proof fn part2_mct_decorrelation_storage_normal(context:Part2MctRuntimeContext)
    ensures part2_mct_decorrelation_storage_result(context,part2_mct_decorrelation(context.components,context.collection,
        context.work,context.maximum_work,context.maximum_bytes)),
{
    let prepared=part2_mct_runtime_preparation(context);
    part2_mct_prepare_storage_normal(context);
    match prepared.0 {
        Err(error)=>{
            let result=(Err::<(),crate::DecodeError>(error),context.components,prepared.1);
            part2_tier1_storage_pure(Ok(result));
            part2_mct_decorrelation_storage_from_prepared(context,prepared,result);
        },
        Ok(plan)=>{
            part2_mct_runtime_capacity_normal(part2_mct_collection_capacity(context,Part2MctRuntimeRole::SourceSamples));
            part2_mct_runtime_capacity_normal(part2_mct_collection_capacity(context,Part2MctRuntimeRole::OutputSamples));
            part2_mct_pixels_storage_normal(context.components,context.collection,plan,plan.3 as nat);
            part2_mct_decorrelation_storage_pixels(context,plan,prepared.1,part2_mct_decorrelation_pixels(context.components,context.collection,plan,plan.3 as nat));
        },
    }
}
pub(crate) proof fn part2_mct_decorrelation_storage_prepare_error(context:Part2MctRuntimeContext,error:crate::DecodeError,charged:u64)
    requires part2_mct_prepare_storage_result(context,(Err(error),charged)),
    ensures part2_mct_decorrelation_storage_result(context,(Err(error),context.components,charged)),
{
    part2_tier1_storage_pure(Ok((Err::<(),crate::DecodeError>(error),context.components,charged)));
    part2_mct_decorrelation_storage_from_prepared(context,(Err(error),charged),(Err(error),context.components,charged));
}
pub(crate) proof fn part2_mct_decorrelation_storage_scratch_error(context:Part2MctRuntimeContext,plan:Part2MctDecorrelationPreparation,charged:u64,
    role:Part2MctRuntimeRole,error:crate::DecodeError)
    requires part2_mct_prepare_storage_result(context,(Ok(plan),charged)),
        role==Part2MctRuntimeRole::SourceSamples || role==Part2MctRuntimeRole::OutputSamples,
        part2_mct_runtime_capacity_result(part2_mct_collection_capacity(context,role),Err(error)),
        role==Part2MctRuntimeRole::OutputSamples ==> part2_mct_runtime_capacity_result(part2_mct_collection_capacity(context,Part2MctRuntimeRole::SourceSamples),Ok(())),
    ensures part2_mct_decorrelation_storage_result(context,(Err(error),context.components,charged)),
{
    let result=(Err::<(),crate::DecodeError>(error),context.components,charged);
    part2_tier1_storage_pure(Ok(result));
    if role==Part2MctRuntimeRole::OutputSamples {
        part2_tier1_resume_frame(|calls|part2_mct_runtime_capacity_run(part2_mct_collection_capacity(context,role),calls),
            |capacity,rest|part2_mct_decorrelation_after_output(context,plan,charged,capacity,rest),Err(error),Ok(result));
    }
    part2_tier1_resume_frame(|calls|part2_mct_runtime_capacity_run(part2_mct_collection_capacity(context,Part2MctRuntimeRole::SourceSamples),calls),
        |capacity,rest|part2_mct_decorrelation_after_source(context,plan,charged,capacity,rest),
        if role==Part2MctRuntimeRole::SourceSamples{Err(error)}else{Ok(())},Ok(result));
    part2_mct_decorrelation_storage_from_prepared(context,(Ok(plan),charged),result);
}
}
