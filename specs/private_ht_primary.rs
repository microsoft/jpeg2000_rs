use super::*;
verus! {
pub enum PrivatePrimaryPhase { Initial, Snapshot, Retention }

pub type PrivatePrimaryValue=(Tier1RawPlane,bool);

pub(crate) open spec fn private_primary_shape(source:Tier1RawPlane,packed:bool)->bool {
    !packed || (source.width>0 && source.height>0
        && 0<source.coefficients.len()<=4096
        && source.width as nat*source.height as nat==source.coefficients.len())
}

pub(crate) open spec fn private_primary_selected(source:Tier1RawPlane)->bool {
    part2_ht_checkpoint_selected(source,true)
}

pub(crate) proof fn private_primary_shape_duplicate(source:Tier1RawPlane)
    requires private_primary_shape(source,true),
    ensures tier1_duplicate_plane(source)==Ok(source),
{
    reveal(tier1_empty_plane);
}

pub(crate) proof fn private_primary_empty_shape(width:u16,height:u16,plane:Tier1RawPlane)
    requires tier1_empty_plane(width,height)==Ok(plane),
    ensures private_primary_shape(plane,true),
{
    reveal(tier1_empty_plane);
    assert(0<(width as int)*(height as int)) by(nonlinear_arith)
        requires width>0,height>0;
}

pub(crate) open spec fn private_primary_words_run(
    phase:PrivatePrimaryPhase,source:Tier1RawPlane,elements:nat,calls:Seq<Part2Tier1StorageEvent>,
) -> Part2Tier1Run<()> {
    if elements==0 && phase==PrivatePrimaryPhase::Snapshot {Some((Ok(()),calls))}
    else if calls.len()==0 {None} else {
        match calls[0] {
            Part2Tier1StorageEvent::PrivatePrimaryWords {phase:actual_phase,source:actual_source,elements:actual_elements,succeeded} =>
                if phase!=actual_phase || source!=actual_source || elements!=actual_elements {None}
                else {Some((if succeeded {Ok(())} else {Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
            _ => None,
        }
    }
}

pub(crate) open spec fn private_primary_words_result(
    phase:PrivatePrimaryPhase,source:Tier1RawPlane,elements:nat,result:Result<(),crate::DecodeError>,
) -> bool {
    part2_tier1_storage_framed(|calls|private_primary_words_run(phase,source,elements,calls),result)
}

pub(crate) proof fn private_primary_words_observed(
    phase:PrivatePrimaryPhase,source:Tier1RawPlane,elements:nat,result:Result<(),crate::DecodeError>,
)
    requires elements>0, result==Ok(()) || result==Err(crate::DecodeError::AllocationFailed),
    ensures private_primary_words_result(phase,source,elements,result),
{
    let prefix=seq![Part2Tier1StorageEvent::PrivatePrimaryWords {phase,source,elements,succeeded:result.is_ok()}];
    let run=|calls|private_primary_words_run(phase,source,elements,calls);
    assert forall|tail:Seq<Part2Tier1StorageEvent>| #[trigger] run(prefix+tail)==Some((result,tail)) by {
        assert((prefix+tail)[0]==prefix[0]);
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_tier1_storage_prefix(run,prefix,result));
}

pub(crate) proof fn private_primary_words_empty(source:Tier1RawPlane)
    ensures private_primary_words_result(PrivatePrimaryPhase::Snapshot,source,0,Ok(())),
{
    let run=|calls|private_primary_words_run(PrivatePrimaryPhase::Snapshot,source,0,calls);
    assert forall|tail:Seq<Part2Tier1StorageEvent>| #[trigger] run(Seq::empty()+tail)==Some((Ok(()),tail)) by {
        assert(Seq::empty()+tail =~= tail);
    }
    assert(part2_tier1_storage_prefix(run,Seq::empty(),Ok(())));
}

pub(crate) open spec fn private_primary_initial_run(width:u16,height:u16,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<PrivatePrimaryValue> {
    match tier1_empty_plane(width,height) {
        Err(error)=>Some((Err(error),calls)),
        Ok(source)=>part2_tier1_storage_bind(
            private_primary_words_run(PrivatePrimaryPhase::Initial,source,source.coefficients.len()+1,calls),
            |_:(),rest|Some((Ok((source,true)),rest))),
    }
}

pub(crate) open spec fn private_primary_initial_result(width:u16,height:u16,result:Result<PrivatePrimaryValue,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|private_primary_initial_run(width,height,calls),result)
}

pub(crate) proof fn private_primary_initial_normal(width:u16,height:u16)
    ensures private_primary_initial_result(width,height,match tier1_empty_plane(width,height){
        Err(error)=>Err(error),Ok(plane)=>Ok((plane,true)),
    }),
{
    match tier1_empty_plane(width,height){
        Err(error)=>{part2_tier1_storage_pure::<PrivatePrimaryValue>(Err(error));},
        Ok(plane)=>{
            private_primary_words_observed(PrivatePrimaryPhase::Initial,plane,plane.coefficients.len()+1,Ok(()));
            private_primary_initial_observed(width,height,Ok((plane,true)));
        },
    }
}

pub(crate) proof fn private_primary_initial_observed(width:u16,height:u16,result:Result<PrivatePrimaryValue,crate::DecodeError>)
    requires match tier1_empty_plane(width,height) {
        Err(error)=>result==Err(error),
        Ok(source)=>private_primary_words_result(PrivatePrimaryPhase::Initial,source,source.coefficients.len()+1,
            match result{Err(error)=>Err(error),Ok(_)=>Ok(())})
            && match result{Ok(value)=>value==(source,true),Err(_)=>true},
    },
    ensures private_primary_initial_result(width,height,result),
{
    match tier1_empty_plane(width,height) {
        Err(_)=>{part2_tier1_storage_pure(result);},
        Ok(source)=>{
            let unit=match result{Err(error)=>Err(error),Ok(_)=>Ok(())};
            if result.is_ok(){part2_tier1_storage_pure(Ok((source,true)));}
            part2_tier1_storage_bind_frame(
                |calls|private_primary_words_run(PrivatePrimaryPhase::Initial,source,source.coefficients.len()+1,calls),
                |_:(),rest|Some((Ok((source,true)),rest)),unit,result);
        },
    }
}

pub(crate) open spec fn private_primary_copy_run(source:PrivatePrimaryValue,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<PrivatePrimaryValue> {
    if source.1 {
        part2_tier1_storage_bind(
            private_primary_words_run(PrivatePrimaryPhase::Snapshot,source.0,source.0.coefficients.len()+1,calls),
            |_:(),rest|Some((Ok(source),rest)))
    }else{
        part2_tier1_storage_bind(part2_decoder_plane_run(source.0,crate::tier1::HtRefinementCopyRole::PacketStaging,false,calls),
            |_:Tier1RawPlane,rest|Some((Ok(source),rest)))
    }
}

pub(crate) open spec fn private_primary_copy_result(source:PrivatePrimaryValue,result:Result<PrivatePrimaryValue,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|private_primary_copy_run(source,calls),result)
}

pub(crate) proof fn private_primary_copy_normal(source:PrivatePrimaryValue)
    ensures private_primary_copy_result(source,Ok(source)),
{
    if source.1{
        private_primary_words_observed(PrivatePrimaryPhase::Snapshot,source.0,source.0.coefficients.len()+1,Ok(()));
    }else{
        part2_decoder_plane_normal(source.0,crate::tier1::HtRefinementCopyRole::PacketStaging,false);
    }
    private_primary_copy_observed(source,Ok(source));
}

pub(crate) proof fn private_primary_copy_observed(source:PrivatePrimaryValue,result:Result<PrivatePrimaryValue,crate::DecodeError>)
    requires match result{Ok(value)=>value==source,Err(_)=>true},
        if source.1 {private_primary_words_result(PrivatePrimaryPhase::Snapshot,source.0,source.0.coefficients.len()+1,
            match result{Err(error)=>Err(error),Ok(_)=>Ok(())})}
        else{part2_decoder_plane_result(source.0,crate::tier1::HtRefinementCopyRole::PacketStaging,false,
            match result{Err(error)=>Err(error),Ok(_)=>Ok(source.0)})},
    ensures private_primary_copy_result(source,result),
{
    if result.is_ok(){part2_tier1_storage_pure(Ok(source));}
    if source.1 {
        part2_tier1_storage_bind_frame(
            |calls|private_primary_words_run(PrivatePrimaryPhase::Snapshot,source.0,source.0.coefficients.len()+1,calls),
            |_:(),rest|Some((Ok(source),rest)),match result{Err(error)=>Err(error),Ok(_)=>Ok(())},result);
    }else{
        part2_decoder_plane_frames(source.0,crate::tier1::HtRefinementCopyRole::PacketStaging,false,
            match result{Err(error)=>Err(error),Ok(_)=>Ok(source.0)});
        part2_tier1_storage_bind_frame(
            |calls|part2_decoder_plane_run(source.0,crate::tier1::HtRefinementCopyRole::PacketStaging,false,calls),
            |_:Tier1RawPlane,rest|Some((Ok(source),rest)),match result{Err(error)=>Err(error),Ok(_)=>Ok(source.0)},result);
    }
}

pub(crate) open spec fn private_primary_retention_run(source:Tier1RawPlane,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<PrivatePrimaryValue> {
    if !private_primary_selected(source){Some((Ok((source,false)),calls))}
    else{part2_tier1_storage_bind(
        private_primary_words_run(PrivatePrimaryPhase::Retention,source,source.coefficients.len()+1,calls),
        |_:(),rest|Some((Ok((source,true)),rest)))}
}

pub(crate) proof fn private_primary_retention_normal(source:Tier1RawPlane)
    ensures private_primary_retention_result(source,Ok((source,private_primary_selected(source)))),
{
    if private_primary_selected(source){
        private_primary_words_observed(PrivatePrimaryPhase::Retention,source,source.coefficients.len()+1,Ok(()));
        private_primary_retention_observed(source,Ok((source,true)));
    }else{part2_tier1_storage_pure(Ok((source,false)));}
}

pub(crate) open spec fn private_primary_retention_result(source:Tier1RawPlane,result:Result<PrivatePrimaryValue,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|private_primary_retention_run(source,calls),result)
}

pub(crate) proof fn private_primary_retention_observed(source:Tier1RawPlane,result:Result<PrivatePrimaryValue,crate::DecodeError>)
    requires match result{Ok(value)=>value==(source,private_primary_selected(source)),Err(_)=>private_primary_selected(source)},
        private_primary_selected(source) ==> private_primary_words_result(PrivatePrimaryPhase::Retention,source,source.coefficients.len()+1,
            match result{Err(error)=>Err(error),Ok(_)=>Ok(())}),
    ensures private_primary_retention_result(source,result),
{
    if !private_primary_selected(source){part2_tier1_storage_pure(result);}
    else{
        if result.is_ok(){part2_tier1_storage_pure(Ok((source,true)));}
        part2_tier1_storage_bind_frame(
            |calls|private_primary_words_run(PrivatePrimaryPhase::Retention,source,source.coefficients.len()+1,calls),
            |_:(),rest|Some((Ok((source,true)),rest)),match result{Err(error)=>Err(error),Ok(_)=>Ok(())},result);
    }
}

pub(crate) open spec fn private_primary_materialize_run(source:PrivatePrimaryValue,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1RawPlane> {
    if source.1 {part2_plane_duplicate_run(source.0,crate::tier1::CoefficientStorageRole::PrivatePrimaryOutput,calls)}
    else{Some((Ok(source.0),calls))}
}

pub(crate) open spec fn private_primary_materialize_result(source:PrivatePrimaryValue,result:Result<Tier1RawPlane,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|private_primary_materialize_run(source,calls),result)
}

pub(crate) proof fn private_primary_materialize_observed(source:PrivatePrimaryValue,result:Result<Tier1RawPlane,crate::DecodeError>)
    requires if source.1 {part1_plane_duplicate_storage_result(source.0,crate::tier1::CoefficientStorageRole::PrivatePrimaryOutput,result)}
        else {result==Ok(source.0)},
    ensures private_primary_materialize_result(source,result),
{
    if source.1 {
        part2_plane_duplicate_frames(source.0,crate::tier1::CoefficientStorageRole::PrivatePrimaryOutput,result);
        part2_tier1_storage_eta(|calls|part2_plane_duplicate_run(source.0,crate::tier1::CoefficientStorageRole::PrivatePrimaryOutput,calls),result);
    }else{part2_tier1_storage_pure(result);}
}
}
