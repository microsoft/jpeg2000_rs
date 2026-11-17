//! Reached JP2 metadata and typed sample copies, before original output admission.
use super::*;
verus! {
pub closed spec fn part2_definition_storage_result(context:Part2TypedCapacityContext,response:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_typed_capacity_run(context,calls),response)
}
pub(crate) proof fn part2_definition_storage_observed(context:Part2TypedCapacityContext,response:Result<(),crate::DecodeError>)
    requires response==Ok(()) || (response==Err(crate::DecodeError::AllocationFailed) && part2_typed_capacity_count(context)>0),
    ensures part2_definition_storage_result(context,response),
{
    part2_typed_capacity_observed(context,response);
}
pub(crate) proof fn part2_definition_storage_frames(context:Part2TypedCapacityContext,response:Result<(),crate::DecodeError>)
    requires part2_definition_storage_result(context,response),
    ensures part2_tier1_storage_framed(|calls|part2_typed_capacity_run(context,calls),response),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()>|
            (forall|calls| #[trigger] other(calls)==part2_typed_capacity_run(context,calls)) ==> #[trigger] part2_tier1_storage_framed(other,response),
{
    part2_tier1_storage_eta(|calls|part2_typed_capacity_run(context,calls),response);
}
pub struct Part2OutputStorageContext {
    pub image:Part1DecodedTypedImage,
    pub header:Part2OutputHeader,
    pub components:u16,
    pub maximum:u64,
}
pub(crate) open spec fn part2_output_capacity_count(context:Part2OutputStorageContext)->nat {
    if context.header.1.len()==0{context.image.1.len()}else{context.header.1.len()}
}
pub(crate) open spec fn part2_output_inputs(context:Part2OutputStorageContext)->Seq<Part2TypedComponentOutput> {
    Seq::new(context.image.1.len(),|i:int|(context.image.1[i],context.image.2[i]))
}
pub(crate) open spec fn part2_output_copy_run(source:Part2TypedComponentOutput,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2TypedComponentOutput> {
    part2_tier1_storage_bind(part2_typed_capacity_run(Part2TypedCapacityContext::Copy {source},calls),
        |_:(),rest|part2_tier1_storage_bind(
            part2_typed_capacity_run(part2_output_definition_copy_context(source),rest),
            |_:(),tail|Some((part2_typed_component_copy(source),tail))))
}
pub(crate) open spec fn part2_output_definition_copy_context(source:Part2TypedComponentOutput)->Part2TypedCapacityContext {
    Part2TypedCapacityContext::DefinitionCopy {source,target:(source.0,Seq::empty())}
}
pub closed spec fn part2_output_copy_result(source:Part2TypedComponentOutput,result:Result<Part2TypedComponentOutput,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_output_copy_run(source,calls),result)
}
pub(crate) proof fn part2_output_copy_normal(source:Part2TypedComponentOutput)
    ensures part2_output_copy_result(source,part2_typed_component_copy(source)),
{
    let context=Part2TypedCapacityContext::Copy {source};
    part2_typed_capacity_observed(context,Ok(()));part2_tier1_storage_pure(part2_typed_component_copy(source));
    part2_typed_capacity_observed(part2_output_definition_copy_context(source),Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(part2_output_definition_copy_context(source),calls),
        |_:(),tail|Some((part2_typed_component_copy(source),tail)),Ok(()),part2_typed_component_copy(source));
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(context,calls),
        |_:(),rest|part2_tier1_storage_bind(part2_typed_capacity_run(part2_output_definition_copy_context(source),rest),
            |_:(),tail|Some((part2_typed_component_copy(source),tail))),Ok(()),part2_typed_component_copy(source));
}
pub(crate) proof fn part2_output_copy_refused(source:Part2TypedComponentOutput)
    requires part2_tier1_storage_framed(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Copy {source},calls),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_output_copy_result(source,Err(crate::DecodeError::AllocationFailed)),
{
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Copy {source},calls),
        |_:(),rest|part2_tier1_storage_bind(part2_typed_capacity_run(part2_output_definition_copy_context(source),rest),
            |_:(),tail|Some((part2_typed_component_copy(source),tail))),Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_output_definition_copy_refused(source:Part2TypedComponentOutput,error:crate::DecodeError)
    requires part2_definition_storage_result(part2_output_definition_copy_context(source),Err(error)),
    ensures part2_output_copy_result(source,Err(error)),
{
    part2_definition_storage_frames(part2_output_definition_copy_context(source),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(part2_output_definition_copy_context(source),calls),
        |_:(),tail|Some((part2_typed_component_copy(source),tail)),Err(error),Err(error));
    part2_typed_capacity_observed(Part2TypedCapacityContext::Copy {source},Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Copy {source},calls),
        |_:(),rest|part2_tier1_storage_bind(part2_typed_capacity_run(part2_output_definition_copy_context(source),rest),
            |_:(),tail|Some((part2_typed_component_copy(source),tail))),Ok(()),Err(error));
}
pub(crate) proof fn part2_output_copy_frames(source:Part2TypedComponentOutput,result:Result<Part2TypedComponentOutput,crate::DecodeError>)
    requires part2_output_copy_result(source,result),
    ensures part2_tier1_storage_framed(|calls|part2_output_copy_run(source,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2TypedComponentOutput>|
            (forall|calls| #[trigger] other(calls)==part2_output_copy_run(source,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{part2_tier1_storage_eta(|calls|part2_output_copy_run(source,calls),result);}
pub(crate) open spec fn part2_output_selected_source(context:Part2OutputStorageContext,index:nat)->Result<Part2TypedComponentOutput,crate::DecodeError> {
    let input=part2_output_inputs(context);
    if context.header.1.len()==0{Ok(input[index as int])}else{part2_typed_image_component(input,context.header.1[index as int].0)}
}
pub(crate) open spec fn part2_palette_component_storage_admit(palette:Part2PaletteModel,column:u8)
    ->Result<(),crate::DecodeError> {
    if column>=palette.1.len() {Err(part2_color_input_error())}
    else if palette.1[column as int].precision==0 || palette.1[column as int].precision>38 {
        Err(part2_color_input_error())
    }else {Ok(())}
}
pub(crate) open spec fn part2_palette_component_storage_run(source:Part2TypedComponentOutput,
    palette:Part2PaletteModel,column:u8,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2TypedComponentOutput> {
    match part2_palette_component_storage_admit(palette,column) {
        Err(error)=>Some((Err(error),calls)),
        Ok(())=>part2_tier1_storage_bind(part2_typed_capacity_run(
            Part2TypedCapacityContext::Palette {source,palette,column},calls),
            |_:(),rest|Some((part2_palette_component(source.0,palette,column),rest))),
    }
}
pub closed spec fn part2_palette_component_storage_result(source:Part2TypedComponentOutput,
    palette:Part2PaletteModel,column:u8,result:Result<Part2TypedComponentOutput,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_palette_component_storage_run(source,palette,column,calls),result)
}
pub(crate) proof fn part2_palette_component_storage_normal(source:Part2TypedComponentOutput,
    palette:Part2PaletteModel,column:u8)
    ensures part2_palette_component_storage_result(source,palette,column,part2_palette_component(source.0,palette,column)),
{
    let result=part2_palette_component(source.0,palette,column);
    part2_tier1_storage_pure(result);
    if part2_palette_component_storage_admit(palette,column).is_ok() {
        let context=Part2TypedCapacityContext::Palette {source,palette,column};
        part2_typed_capacity_observed(context,Ok(()));
        part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(context,calls),
            |_:(),rest|Some((result,rest)),Ok(()),result);
    }
}
pub(crate) proof fn part2_palette_component_storage_refused(source:Part2TypedComponentOutput,
    palette:Part2PaletteModel,column:u8)
    requires part2_palette_component_storage_admit(palette,column)==Ok(()),
        part2_tier1_storage_framed(|calls|part2_typed_capacity_run(
            Part2TypedCapacityContext::Palette {source,palette,column},calls),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_palette_component_storage_result(source,palette,column,Err(crate::DecodeError::AllocationFailed)),
{
    let context=Part2TypedCapacityContext::Palette {source,palette,column};
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(context,calls),
        |_:(),rest|Some((part2_palette_component(source.0,palette,column),rest)),
        Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_palette_component_storage_frames(source:Part2TypedComponentOutput,
    palette:Part2PaletteModel,column:u8,result:Result<Part2TypedComponentOutput,crate::DecodeError>)
    requires part2_palette_component_storage_result(source,palette,column,result),
    ensures part2_tier1_storage_framed(|calls|part2_palette_component_storage_run(source,palette,column,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2TypedComponentOutput>|
            (forall|calls| #[trigger] other(calls)==part2_palette_component_storage_run(source,palette,column,calls)) ==>
                #[trigger] part2_tier1_storage_framed(other,result),
{
    part2_tier1_storage_eta(|calls|part2_palette_component_storage_run(source,palette,column,calls),result);
}
pub(crate) open spec fn part2_output_palette_component_run(context:Part2OutputStorageContext,index:nat,
    source:Part2TypedComponentOutput,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2TypedComponentOutput> {
    match context.header.1[index as int].1 {
        crate::jp2::MappingType::Direct=>part2_output_copy_run(source,calls),
        crate::jp2::MappingType::Palette {column}=>match context.header.0 {
            None=>Some((Err(part2_color_input_error()),calls)),
            Some(palette)=>part2_palette_component_storage_run(source,palette,column,calls),
        },
    }
}
pub(crate) open spec fn part2_output_direct(context:Part2OutputStorageContext,index:nat)->bool {
    context.header.1.len()==0 || context.header.1[index as int].1==crate::jp2::MappingType::Direct
}
pub(crate) open spec fn part2_output_component_value(context:Part2OutputStorageContext,index:nat)->Result<Part2TypedComponentOutput,crate::DecodeError> {
    if context.header.1.len()==0{part2_typed_component_copy(part2_output_inputs(context)[index as int])}
    else{part2_output_mapped_component(part2_output_inputs(context),context.header.0,context.header.1[index as int])}
}
pub(crate) open spec fn part2_output_component_run(context:Part2OutputStorageContext,index:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2TypedComponentOutput> {
    match part2_output_selected_source(context,index) {
        Err(error)=>Some((Err(error),calls)),
        Ok(source)=>if part2_output_direct(context,index){part2_output_copy_run(source,calls)}
            else{part2_output_palette_component_run(context,index,source,calls)},
    }
}
pub(crate) proof fn part2_output_component_normal(context:Part2OutputStorageContext,index:nat)
    ensures part2_tier1_storage_framed(|calls|part2_output_component_run(context,index,calls),part2_output_component_value(context,index)),
{
    match part2_output_selected_source(context,index) {
        Err(error)=>{part2_tier1_storage_pure::<Part2TypedComponentOutput>(Err(error));},
        Ok(source)=>if part2_output_direct(context,index){
            part2_output_copy_normal(source);part2_output_copy_frames(source,part2_typed_component_copy(source));
        }else{
            match context.header.1[index as int].1 {
                crate::jp2::MappingType::Direct=>{
                    part2_output_copy_normal(source);part2_output_copy_frames(source,part2_typed_component_copy(source));
                },
                crate::jp2::MappingType::Palette {column}=>match context.header.0 {
                    None=>part2_tier1_storage_pure(part2_output_component_value(context,index)),
                    Some(palette)=>{
                        let result=part2_palette_component(source.0,palette,column);
                        part2_palette_component_storage_normal(source,palette,column);
                        part2_palette_component_storage_frames(source,palette,column,result);
                    },
                },
            }
        },
    }
}
pub(crate) proof fn part2_output_component_palette_error(context:Part2OutputStorageContext,index:nat,
    source:Part2TypedComponentOutput,palette:Part2PaletteModel,column:u8,error:crate::DecodeError)
    requires index<context.header.1.len(),
        context.header.1[index as int].1==(crate::jp2::MappingType::Palette {column}),
        part2_output_selected_source(context,index)==Ok(source),context.header.0==Some(palette),
        part2_palette_component_storage_result(source,palette,column,Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_output_component_run(context,index,calls),Err(error)),
{
    part2_palette_component_storage_frames(source,palette,column,Err(error));
}
pub(crate) open spec fn part2_output_components_value(context:Part2OutputStorageContext,count:nat)->Result<Seq<Part2TypedComponentOutput>,crate::DecodeError> {
    if context.header.1.len()==0{Ok(part2_output_inputs(context).take(count as int))}
    else{part2_output_mapping_prefix(part2_output_inputs(context),context.header,count)}
}
#[verifier::opaque]
pub(crate) open spec fn part2_output_components_run(context:Part2OutputStorageContext,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<Part2TypedComponentOutput>>
    decreases count,
{
    if count==0{Some((Ok(Seq::empty()),calls))}else{
        part2_tier1_storage_bind(part2_output_components_run(context,(count-1) as nat,calls),
            |before:Seq<Part2TypedComponentOutput>,rest|part2_tier1_storage_bind(part2_output_component_run(context,(count-1) as nat,rest),
                |component:Part2TypedComponentOutput,tail|Some((Ok(before.push(component)),tail))))
    }
}
pub(crate) open spec fn part2_output_finish(context:Part2OutputStorageContext,mapped:Seq<Part2TypedComponentOutput>)->Result<Part1DecodedTypedImage,crate::DecodeError> {
    match part2_output_definition_prefix(mapped,context.header.2,context.header.2.len()) {
        Err(error)=>Err(error),
        Ok(defined)=>part2_typed_image_from_parts(context.image.0.0,context.image.0.1,context.image.0.2,context.image.0.3,defined,context.components,context.maximum),
    }
}
pub(crate) open spec fn part2_output_definition_run(
    components:Seq<Part2TypedComponentOutput>,record:(u16,ColorDefinition),calls:Seq<Part2Tier1StorageEvent>,
)->Part2Tier1Run<Seq<Part2TypedComponentOutput>> {
    if record.0 as nat>=components.len(){Some((Err(part2_color_input_error()),calls))}
    else{part2_tier1_storage_bind(
        part2_typed_capacity_run(Part2TypedCapacityContext::Definition {source:components[record.0 as int],definition:record.1},calls),
        |_:(),rest|Some((part2_output_apply_definition(components,record),rest)))}
}
#[verifier::opaque]
pub(crate) open spec fn part2_output_definitions_run(
    mapped:Seq<Part2TypedComponentOutput>,records:Seq<(u16,ColorDefinition)>,count:nat,calls:Seq<Part2Tier1StorageEvent>,
)->Part2Tier1Run<Seq<Part2TypedComponentOutput>>
    decreases count,
{
    if count==0{Some((Ok(mapped),calls))}else{
        part2_tier1_storage_bind(part2_output_definitions_run(mapped,records,(count-1) as nat,calls),
            |before:Seq<Part2TypedComponentOutput>,rest|part2_output_definition_run(before,records[count-1],rest))
    }
}
pub(crate) proof fn part2_output_definition_normal(components:Seq<Part2TypedComponentOutput>,record:(u16,ColorDefinition))
    ensures part2_tier1_storage_framed(|calls|part2_output_definition_run(components,record,calls),part2_output_apply_definition(components,record)),
{
    let result=part2_output_apply_definition(components,record);
    part2_tier1_storage_pure(result);
    if (record.0 as nat) < components.len(){
        let context=Part2TypedCapacityContext::Definition {source:components[record.0 as int],definition:record.1};
        part2_typed_capacity_observed(context,Ok(()));
        part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(context,calls),
            |_:(),rest|Some((result,rest)),Ok(()),result);
    }
}
pub(crate) proof fn part2_output_definitions_normal(mapped:Seq<Part2TypedComponentOutput>,records:Seq<(u16,ColorDefinition)>,count:nat)
    ensures part2_tier1_storage_framed(|calls|part2_output_definitions_run(mapped,records,count,calls),
        part2_output_definition_prefix(mapped,records,count)),
    decreases count,
{
    reveal_with_fuel(part2_output_definitions_run,1);
    reveal_with_fuel(part2_output_definition_prefix,1);
    let result=part2_output_definition_prefix(mapped,records,count);
    if count==0{part2_tier1_storage_pure(result);}else{
        let prior=part2_output_definition_prefix(mapped,records,(count-1) as nat);
        part2_output_definitions_normal(mapped,records,(count-1) as nat);
        if let Ok(before)=prior{
            part2_output_definition_normal(before,records[count-1]);
            part2_tier1_storage_eta(|calls|part2_output_definition_run(before,records[count-1],calls),result);
        }
        part2_tier1_storage_bind_frame(|calls|part2_output_definitions_run(mapped,records,(count-1) as nat,calls),
            |before:Seq<Part2TypedComponentOutput>,rest|part2_output_definition_run(before,records[count-1],rest),prior,result);
    }
}
pub(crate) proof fn part2_output_definitions_error(mapped:Seq<Part2TypedComponentOutput>,records:Seq<(u16,ColorDefinition)>,from:nat,to:nat,error:crate::DecodeError)
    requires from<=to,
        part2_tier1_storage_framed(|calls|part2_output_definitions_run(mapped,records,from,calls),Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_output_definitions_run(mapped,records,to,calls),Err(error)),
    decreases to-from,
{
    if from<to{
        reveal_with_fuel(part2_output_definitions_run,1);
        part2_output_definitions_error(mapped,records,from,(to-1) as nat,error);
        part2_tier1_storage_bind_frame(|calls|part2_output_definitions_run(mapped,records,(to-1) as nat,calls),
            |before:Seq<Part2TypedComponentOutput>,rest|part2_output_definition_run(before,records[to-1],rest),Err(error),Err(error));
    }
}
pub(crate) open spec fn part2_output_finish_run(context:Part2OutputStorageContext,mapped:Seq<Part2TypedComponentOutput>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1DecodedTypedImage> {
    part2_tier1_storage_bind(part2_output_definitions_run(mapped,context.header.2,context.header.2.len(),calls),
        |defined:Seq<Part2TypedComponentOutput>,rest|Some((part2_typed_image_from_parts(
            context.image.0.0,context.image.0.1,context.image.0.2,context.image.0.3,defined,context.components,context.maximum),rest)))
}
pub(crate) proof fn part2_output_finish_normal(context:Part2OutputStorageContext,mapped:Seq<Part2TypedComponentOutput>)
    ensures part2_tier1_storage_framed(|calls|part2_output_finish_run(context,mapped,calls),part2_output_finish(context,mapped)),
{
    let definitions=part2_output_definition_prefix(mapped,context.header.2,context.header.2.len());
    part2_output_definitions_normal(mapped,context.header.2,context.header.2.len());
    if let Ok(defined)=definitions{part2_tier1_storage_pure(part2_output_finish(context,mapped));}
    part2_tier1_storage_bind_frame(|calls|part2_output_definitions_run(mapped,context.header.2,context.header.2.len(),calls),
        |defined:Seq<Part2TypedComponentOutput>,rest|Some((part2_typed_image_from_parts(
            context.image.0.0,context.image.0.1,context.image.0.2,context.image.0.3,defined,context.components,context.maximum),rest)),
        definitions,part2_output_finish(context,mapped));
}
pub(crate) open spec fn part2_output_storage_run(context:Part2OutputStorageContext,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1DecodedTypedImage> {
    part2_tier1_storage_bind(part2_typed_capacity_run(Part2TypedCapacityContext::Output {context},calls),
        |_:(),rest|part2_tier1_storage_bind(part2_output_components_run(context,part2_output_capacity_count(context),rest),
            |mapped:Seq<Part2TypedComponentOutput>,tail|part2_output_finish_run(context,mapped,tail)))
}
pub closed spec fn part2_output_storage_result(context:Part2OutputStorageContext,result:Result<Part1DecodedTypedImage,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_output_storage_run(context,calls),result)
}
pub(crate) proof fn part2_output_components_normal(context:Part2OutputStorageContext,count:nat)
    requires count<=part2_output_capacity_count(context),
    ensures part2_tier1_storage_framed(|calls|part2_output_components_run(context,count,calls),part2_output_components_value(context,count)),
    decreases count,
{
    reveal_with_fuel(part2_output_components_run,1);reveal_with_fuel(part2_output_mapping_prefix,1);
    let result=part2_output_components_value(context,count);
    if count==0{
        assert(part2_output_inputs(context).take(0) =~= Seq::<Part2TypedComponentOutput>::empty());
        part2_tier1_storage_pure(result);
    }else{
        let prior=part2_output_components_value(context,(count-1) as nat);
        part2_output_components_normal(context,(count-1) as nat);
        if let Ok(before)=prior {
            let component=part2_output_component_value(context,(count-1) as nat);
            part2_output_component_normal(context,(count-1) as nat);
            part2_tier1_storage_eta(|calls|part2_output_component_run(context,(count-1) as nat,calls),component);
            if let Ok(value)=component{
                if context.header.1.len()==0{
                    assert(part2_output_inputs(context).take(count as int) =~= before.push(value));
                }
                part2_tier1_storage_pure(Ok(before.push(value)));
            }
            part2_tier1_storage_bind_frame(|calls|part2_output_component_run(context,(count-1) as nat,calls),
                |component:Part2TypedComponentOutput,tail|Some((Ok(before.push(component)),tail)),component,result);
        }
        part2_tier1_storage_bind_frame(|calls|part2_output_components_run(context,(count-1) as nat,calls),
            |before:Seq<Part2TypedComponentOutput>,rest|part2_tier1_storage_bind(part2_output_component_run(context,(count-1) as nat,rest),
                |component:Part2TypedComponentOutput,tail|Some((Ok(before.push(component)),tail))),prior,result);
    }
}
pub(crate) proof fn part2_output_components_error(context:Part2OutputStorageContext,from:nat,to:nat,error:crate::DecodeError)
    requires from<=to,
        part2_tier1_storage_framed(|calls|part2_output_components_run(context,from,calls),Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_output_components_run(context,to,calls),Err(error)),
    decreases to-from,
{
    if from<to{
        reveal_with_fuel(part2_output_components_run,1);
        part2_output_components_error(context,from,(to-1) as nat,error);
        part2_tier1_storage_bind_frame(|calls|part2_output_components_run(context,(to-1) as nat,calls),
            |before:Seq<Part2TypedComponentOutput>,rest|part2_tier1_storage_bind(part2_output_component_run(context,(to-1) as nat,rest),
                |component:Part2TypedComponentOutput,tail|Some((Ok(before.push(component)),tail))),Err(error),Err(error));
    }
}
pub(crate) proof fn part2_output_component_copy_error(context:Part2OutputStorageContext,index:nat,source:Part2TypedComponentOutput,error:crate::DecodeError)
    requires part2_output_selected_source(context,index)==Ok(source),part2_output_direct(context,index),part2_output_copy_result(source,Err(error)),
    ensures part2_tier1_storage_framed(|calls|part2_output_component_run(context,index,calls),Err(error)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2TypedComponentOutput>|
            (forall|calls| #[trigger] other(calls)==part2_output_component_run(context,index,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Err(error)),
{
    part2_output_copy_frames(source,Err(error));
    part2_tier1_storage_eta(|calls|part2_output_component_run(context,index,calls),Err(error));
}
pub(crate) proof fn part2_output_storage_owner_refused(context:Part2OutputStorageContext)
    requires part2_tier1_storage_framed(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Output {context},calls),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_output_storage_result(context,Err(crate::DecodeError::AllocationFailed)),
{
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Output {context},calls),
        |_:(),rest|part2_tier1_storage_bind(part2_output_components_run(context,part2_output_capacity_count(context),rest),
            |mapped:Seq<Part2TypedComponentOutput>,tail|part2_output_finish_run(context,mapped,tail)),
        Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_output_storage_component_error(context:Part2OutputStorageContext,index:nat,before:Seq<Part2TypedComponentOutput>,error:crate::DecodeError)
    requires index<part2_output_capacity_count(context),part2_output_components_value(context,index)==Ok(before),
        part2_tier1_storage_framed(|calls|part2_output_component_run(context,index,calls),Err(error)),
    ensures part2_output_storage_result(context,Err(error)),
{
    reveal_with_fuel(part2_output_components_run,1);
    part2_tier1_storage_eta(|calls|part2_output_component_run(context,index,calls),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_output_component_run(context,index,calls),
        |component:Part2TypedComponentOutput,tail|Some((Ok(before.push(component)),tail)),Err(error),Err(error));
    part2_output_components_normal(context,index);
    part2_tier1_storage_bind_frame(|calls|part2_output_components_run(context,index,calls),
        |before:Seq<Part2TypedComponentOutput>,rest|part2_tier1_storage_bind(part2_output_component_run(context,index,rest),
            |component:Part2TypedComponentOutput,tail|Some((Ok(before.push(component)),tail))),Ok(before),Err(error));
    assert(part2_tier1_storage_framed(|calls|part2_output_components_run(context,index+1,calls),Err(error)));
    part2_output_components_error(context,index+1,part2_output_capacity_count(context),error);
    part2_tier1_storage_bind_frame(|calls|part2_output_components_run(context,part2_output_capacity_count(context),calls),
        |mapped:Seq<Part2TypedComponentOutput>,tail|part2_output_finish_run(context,mapped,tail),Err(error),Err(error));
    part2_typed_capacity_observed(Part2TypedCapacityContext::Output {context},Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Output {context},calls),
        |_:(),rest|part2_tier1_storage_bind(part2_output_components_run(context,part2_output_capacity_count(context),rest),
            |mapped:Seq<Part2TypedComponentOutput>,tail|part2_output_finish_run(context,mapped,tail)),Ok(()),Err(error));
}
pub(crate) proof fn part2_output_storage_definition_error(
    context:Part2OutputStorageContext,mapped:Seq<Part2TypedComponentOutput>,index:nat,before:Seq<Part2TypedComponentOutput>,error:crate::DecodeError,
)
    requires index<context.header.2.len(),
        part2_output_components_value(context,part2_output_capacity_count(context))==Ok(mapped),
        part2_output_definition_prefix(mapped,context.header.2,index)==Ok(before),
        (context.header.2[index as int].0 as nat) < before.len(),
        part2_definition_storage_result(Part2TypedCapacityContext::Definition {
            source:before[context.header.2[index as int].0 as int],definition:context.header.2[index as int].1},Err(error)),
    ensures part2_output_storage_result(context,Err(error)),
{
    let record=context.header.2[index as int];
    let capacity=Part2TypedCapacityContext::Definition {source:before[record.0 as int],definition:record.1};
    part2_definition_storage_frames(capacity,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(capacity,calls),
        |_:(),rest|Some((part2_output_apply_definition(before,record),rest)),Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_output_definition_run(before,record,calls),Err(error));
    part2_output_definitions_normal(mapped,context.header.2,index);
    reveal_with_fuel(part2_output_definitions_run,1);
    part2_tier1_storage_bind_frame(|calls|part2_output_definitions_run(mapped,context.header.2,index,calls),
        |before:Seq<Part2TypedComponentOutput>,rest|part2_output_definition_run(before,record,rest),Ok(before),Err(error));
    part2_output_definitions_error(mapped,context.header.2,index+1,context.header.2.len(),error);
    part2_tier1_storage_bind_frame(|calls|part2_output_definitions_run(mapped,context.header.2,context.header.2.len(),calls),
        |defined:Seq<Part2TypedComponentOutput>,rest|Some((part2_typed_image_from_parts(
            context.image.0.0,context.image.0.1,context.image.0.2,context.image.0.3,defined,context.components,context.maximum),rest)),Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_output_finish_run(context,mapped,calls),Err(error));
    part2_output_components_normal(context,part2_output_capacity_count(context));
    part2_tier1_storage_bind_frame(|calls|part2_output_components_run(context,part2_output_capacity_count(context),calls),
        |mapped:Seq<Part2TypedComponentOutput>,tail|part2_output_finish_run(context,mapped,tail),Ok(mapped),Err(error));
    part2_typed_capacity_observed(Part2TypedCapacityContext::Output {context},Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Output {context},calls),
        |_:(),rest|part2_tier1_storage_bind(part2_output_components_run(context,part2_output_capacity_count(context),rest),
            |mapped:Seq<Part2TypedComponentOutput>,tail|part2_output_finish_run(context,mapped,tail)),Ok(()),Err(error));
}
pub(crate) proof fn part2_output_storage_frames(context:Part2OutputStorageContext,result:Result<Part1DecodedTypedImage,crate::DecodeError>)
    requires part2_output_storage_result(context,result),
    ensures part2_tier1_storage_framed(|calls|part2_output_storage_run(context,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1DecodedTypedImage>|
            (forall|calls| #[trigger] other(calls)==part2_output_storage_run(context,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{part2_tier1_storage_eta(|calls|part2_output_storage_run(context,calls),result);}
pub(crate) open spec fn part2_output_calls_run(context:Part2OutputStorageContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage> {
    if events.len()==0{None}else{match events[0] {
        Part2JpipSnapshotEvent::OutputHeaderCalls {context:actual,calls}=>if actual!=context{None}else{
            match part2_output_storage_run(context,calls){Some((result,rest))=>if rest.len()==0{Some((result,events.drop_first()))}else{None},None=>None}
        },
        _=>None,
    }}
}
pub(crate) proof fn part2_output_calls_observed(context:Part2OutputStorageContext,result:Result<Part1DecodedTypedImage,crate::DecodeError>)
    requires part2_output_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_output_calls_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage>|
            (forall|events| #[trigger] other(events)==part2_output_calls_run(context,events)) ==> #[trigger] part2_cold_framed(other,result),
{
    part2_output_storage_frames(context,result);
    let run=|calls|part2_output_storage_run(context,calls);
    let calls=choose|prefix| #[trigger] part2_tier1_storage_prefix(run,prefix,result);
    assert(calls+Seq::empty() =~= calls);
    assert(run(calls)==Some((result,Seq::empty())));
    let prefix=seq![Part2JpipSnapshotEvent::OutputHeaderCalls {context,calls}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_output_calls_run(context,prefix+tail)==Some((result,tail)) by{
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|part2_output_calls_run(context,events),prefix,result));
    part2_decode_eta(|events|part2_output_calls_run(context,events),result);
}
pub(crate) open spec fn part2_apply_output_run(image:Part1DecodedTypedImage,header:Part2OutputHeader,components:u16,maximum:u64,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage> {
    part2_output_calls_run(Part2OutputStorageContext {image,header,components,maximum},events)
}
pub(crate) proof fn part2_apply_output_observed(image:Part1DecodedTypedImage,header:Part2OutputHeader,components:u16,maximum:u64,
    result:Result<Part1DecodedTypedImage,crate::DecodeError>)
    requires part2_output_storage_result(Part2OutputStorageContext {image,header,components,maximum},result),
    ensures part2_cold_framed(|events|part2_apply_output_run(image,header,components,maximum,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage>|
            (forall|events| #[trigger] other(events)==part2_apply_output_run(image,header,components,maximum,events)) ==> #[trigger] part2_cold_framed(other,result),
{
    part2_output_calls_observed(Part2OutputStorageContext {image,header,components,maximum},result);
    part2_decode_eta(|events|part2_apply_output_run(image,header,components,maximum,events),result);
}
pub(crate) proof fn part2_apply_output_normal(image:Part1DecodedTypedImage,header:Part2OutputHeader,components:u16,maximum:u64)
    ensures part2_cold_framed(|events|part2_apply_output_run(image,header,components,maximum,events),part2_apply_output_header(image,header,components,maximum)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage>|
            (forall|events| #[trigger] other(events)==part2_apply_output_run(image,header,components,maximum,events)) ==> #[trigger] part2_cold_framed(other,part2_apply_output_header(image,header,components,maximum)),
{
    part2_output_storage_normal(Part2OutputStorageContext {image,header,components,maximum});
    part2_apply_output_observed(image,header,components,maximum,part2_apply_output_header(image,header,components,maximum));
}
pub(crate) open spec fn part2_associated_output_run(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,components:u16,maximum:u64,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Part1DecodedTypedImage,Option<Part2AssociatedHeader>)> {
    match header {
        None=>Some((Ok((image,None)),events)),
        Some(value)=>part2_jpip_snapshot_bind(part2_apply_output_run(image,value.0,components,maximum,events),
            |mapped:Part1DecodedTypedImage,rest|Some((Ok((mapped,header)),rest))),
    }
}
pub closed spec fn part2_associated_output_result(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,components:u16,maximum:u64,
    result:Part2AssociatedImageResult)->bool {
    part2_cold_framed(|events|part2_associated_output_run(image,header,components,maximum,events),result)
}
pub(crate) proof fn part2_associated_output_normal(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,components:u16,maximum:u64)
    ensures part2_associated_output_result(image,header,components,maximum,part2_apply_associated_output(image,header,components,maximum)),
{
    let result=part2_apply_associated_output(image,header,components,maximum);
    match header {
        None=>{part2_cold_pure(result);},
        Some(value)=>{
            let mapped=part2_apply_output_header(image,value.0,components,maximum);
            part2_apply_output_normal(image,value.0,components,maximum);
            if let Ok(value)=mapped{part2_cold_pure(Ok((value,header)));}
            part2_cold_bind(|events|part2_apply_output_run(image,value.0,components,maximum,events),
                |mapped:Part1DecodedTypedImage,rest|Some((Ok((mapped,header)),rest)),mapped,result);
        },
    }
}
pub(crate) proof fn part2_associated_output_error(image:Part1DecodedTypedImage,header:Part2AssociatedHeader,components:u16,maximum:u64,error:crate::DecodeError)
    requires part2_output_storage_result(Part2OutputStorageContext {image,header:header.0,components,maximum},Err(error)),
    ensures part2_associated_output_result(image,Some(header),components,maximum,Err(error)),
{
    part2_apply_output_observed(image,header.0,components,maximum,Err(error));
    part2_cold_bind(|events|part2_apply_output_run(image,header.0,components,maximum,events),
        |mapped:Part1DecodedTypedImage,rest|Some((Ok((mapped,Some(header))),rest)),Err(error),Err::<(Part1DecodedTypedImage,Option<Part2AssociatedHeader>),_>(error));
}
pub(crate) proof fn part2_associated_output_frames(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,components:u16,maximum:u64,result:Part2AssociatedImageResult)
    requires part2_associated_output_result(image,header,components,maximum,result),
    ensures part2_cold_framed(|events|part2_associated_output_run(image,header,components,maximum,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Part1DecodedTypedImage,Option<Part2AssociatedHeader>)>|
            (forall|events| #[trigger] other(events)==part2_associated_output_run(image,header,components,maximum,events)) ==> #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_associated_output_run(image,header,components,maximum,events),result);}
pub(crate) open spec fn part2_selected_output_run(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,target:[u32;4],
    components:u16,maximum:u64,work:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage> {
    part2_jpip_snapshot_bind(part2_associated_output_run(image,header,components,maximum,events),
        |mapped:(Part1DecodedTypedImage,Option<Part2AssociatedHeader>),rest|Some((part2_convert_associated_selected(mapped.0,mapped.1,target,maximum,work),rest)))
}
pub closed spec fn part2_selected_output_result(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,target:[u32;4],
    components:u16,maximum:u64,work:u64,result:Part2ConvertedImageResult)->bool {
    part2_cold_framed(|events|part2_selected_output_run(image,header,target,components,maximum,work,events),result)
}
pub(crate) proof fn part2_selected_output_normal(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,target:[u32;4],components:u16,maximum:u64,work:u64)
    ensures part2_selected_output_result(image,header,target,components,maximum,work,part2_finish_associated_selected_output(image,header,target,components,maximum,work)),
{
    let mapped=part2_apply_associated_output(image,header,components,maximum);
    part2_associated_output_normal(image,header,components,maximum);part2_associated_output_frames(image,header,components,maximum,mapped);
    if let Ok(value)=mapped{part2_cold_pure(part2_convert_associated_selected(value.0,value.1,target,maximum,work));}
    part2_cold_bind(|events|part2_associated_output_run(image,header,components,maximum,events),
        |mapped:(Part1DecodedTypedImage,Option<Part2AssociatedHeader>),rest|Some((part2_convert_associated_selected(mapped.0,mapped.1,target,maximum,work),rest)),
        mapped,part2_finish_associated_selected_output(image,header,target,components,maximum,work));
}
pub(crate) proof fn part2_selected_output_error(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,target:[u32;4],
    components:u16,maximum:u64,work:u64,error:crate::DecodeError)
    requires part2_associated_output_result(image,header,components,maximum,Err(error)),
    ensures part2_selected_output_result(image,header,target,components,maximum,work,Err(error)),
{
    part2_associated_output_frames(image,header,components,maximum,Err(error));
    part2_cold_bind(|events|part2_associated_output_run(image,header,components,maximum,events),
        |mapped:(Part1DecodedTypedImage,Option<Part2AssociatedHeader>),rest|Some((part2_convert_associated_selected(mapped.0,mapped.1,target,maximum,work),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_selected_output_frames(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,target:[u32;4],
    components:u16,maximum:u64,work:u64,result:Part2ConvertedImageResult)
    requires part2_selected_output_result(image,header,target,components,maximum,work,result),
    ensures part2_cold_framed(|events|part2_selected_output_run(image,header,target,components,maximum,work,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage>|
            (forall|events| #[trigger] other(events)==part2_selected_output_run(image,header,target,components,maximum,work,events)) ==> #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_selected_output_run(image,header,target,components,maximum,work,events),result);}
pub(crate) proof fn part2_output_storage_normal(context:Part2OutputStorageContext)
    ensures part2_output_storage_result(context,part2_apply_output_header(context.image,context.header,context.components,context.maximum)),
{
    let count=part2_output_capacity_count(context);let mapped=part2_output_components_value(context,count);
    let result=part2_apply_output_header(context.image,context.header,context.components,context.maximum);
    if context.header.1.len()==0{assert(part2_output_inputs(context).take(count as int) =~= part2_output_inputs(context));}
    part2_output_components_normal(context,count);
    if let Ok(value)=mapped{
        part2_output_finish_normal(context,value);
        part2_tier1_storage_eta(|calls|part2_output_finish_run(context,value,calls),part2_output_finish(context,value));
    }
    part2_tier1_storage_bind_frame(|calls|part2_output_components_run(context,count,calls),
        |mapped:Seq<Part2TypedComponentOutput>,tail|part2_output_finish_run(context,mapped,tail),mapped,result);
    part2_typed_capacity_observed(Part2TypedCapacityContext::Output {context},Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_typed_capacity_run(Part2TypedCapacityContext::Output {context},calls),
        |_:(),rest|part2_tier1_storage_bind(part2_output_components_run(context,count,rest),
            |mapped:Seq<Part2TypedComponentOutput>,tail|part2_output_finish_run(context,mapped,tail)),Ok(()),result);
}
}
