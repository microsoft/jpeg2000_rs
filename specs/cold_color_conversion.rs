//! Ordered color-output storage requests derived from the actual source values.
use super::*;
verus! {
pub struct Part2ColorConvertContext {
    pub image:Part1DecodedTypedImage,pub method:crate::jp2::ColorMethod,pub bytes:u64,pub work:u64,
}
pub(crate) struct Part2ColorNormalizeContext {
    pub component:Part1TypedComponentModel,pub width:u32,pub height:u32,pub x:u32,pub y:u32,
}
pub(crate) struct Part2ColorCropContext {
    pub image:ColorImageModel,pub x:u32,pub y:u32,pub width:u32,pub height:u32,
}
pub(crate) enum Part2ColorOutputCapacity {
    Definition {context:Part2TypedCapacityContext},
    LayoutColors {definitions:Seq<Seq<ColorDefinition>>,colors:usize},
    LayoutAlpha {definitions:Seq<Seq<ColorDefinition>>,colors:usize,component:nat,record:nat},
    Normalize {context:Part2ColorNormalizeContext},
    Channels {context:Part2ColorConvertContext},
    Sycc {context:Part2ColorConvertContext,role:u8},
    EsrgbChannels {context:Part2ColorConvertContext},
    EsrgbPlane {image:Part1DecodedTypedImage,colors:Seq<usize>,role:usize},
    CropChannels {context:Part2ColorCropContext},
    CropPlane {source:Seq<u16>,source_width:u32,x:u32,y:u32,x1:u32,y1:u32,count:usize},
}
pub(crate) open spec fn part2_color_layout_has_definitions(definitions:Seq<Seq<ColorDefinition>>)->bool {
    exists|i:int|#![trigger definitions[i]]0<=i<definitions.len() && definitions[i].len()>0
}
pub(crate) open spec fn part2_color_layout_alpha_before(definitions:Seq<Seq<ColorDefinition>>,colors:usize,component:nat,record:nat)
    ->Option<ColorLayoutState> {
    if component>=definitions.len() || component>usize::MAX || record>=definitions[component as int].len(){None}else{
        match color_layout_components_prefix(definitions,colors,component) {
            Err(_)=>None,Ok(before)=>match color_layout_definitions_prefix(before,definitions[component as int],component as usize,colors,record) {
                Err(_)=>None,Ok(state)=>Some(state),
            },
        }
    }
}
pub(crate) open spec fn part2_color_layout_alpha_admitted(definitions:Seq<Seq<ColorDefinition>>,colors:usize,component:nat,record:nat)->bool {
    match part2_color_layout_alpha_before(definitions,colors,component,record) {
        None=>false,Some(before)=>match color_layout_definition_step(before,definitions[component as int][record as int],component as usize,colors) {
            Err(_)=>false,Ok(after)=>after.1.len()==before.1.len()+1,
        },
    }
}
pub(crate) open spec fn part2_color_convert_preflight(context:Part2ColorConvertContext)
    ->Result<((usize,crate::color::ConvertedColorSpace,bool),ColorLayoutState,usize),crate::DecodeError> {
    let image=context.image;let geometry=image.0;
    if geometry.0==0 || geometry.1==0 {Err(part2_color_input_error())}else{
        match color_output_format(context.method) {
            Err(error)=>Err(error),Ok(format)=>match color_channel_layout(image.2,format.0) {
                Err(error)=>Err(error),Ok(layout)=>match color_validate_components(image.1,geometry,layout) {
                    Err(error)=>Err(error),Ok(())=>match color_validate_output_size(geometry.0,geometry.1,format.0,layout.1.len() as usize,context.bytes,context.work) {
                        Err(error)=>Err(error),Ok(())=>match part2_layer_area(geometry.0,geometry.1) {
                            Err(error)=>Err(error),Ok(count)=>Ok((format,layout,count)),
                        },
                    },
                },
            },
        }
    }
}
pub(crate) open spec fn part2_color_normalize_count(context:Part2ColorNormalizeContext)->nat {
    if context.width==0 || context.width as nat>usize::MAX {0}else{
        match part2_layer_area(context.width,context.height){Err(_)=>0,Ok(count)=>count as nat}
    }
}
pub(crate) open spec fn part2_color_crop_admitted(context:Part2ColorCropContext)->bool {
    context.width>0 && context.height>0 && context.x as nat+context.width as nat<=u32::MAX
        && context.y as nat+context.height as nat<=u32::MAX
        && context.x as nat+context.width as nat<=context.image.0
        && context.y as nat+context.height as nat<=context.image.1
        && !(context.x==0 && context.y==0 && context.width==context.image.0 && context.height==context.image.1)
        && part2_layer_area(context.width,context.height).is_ok()
}
pub(crate) open spec fn part2_color_output_capacity_count(context:Part2ColorOutputCapacity)->nat {
    match context {
        Part2ColorOutputCapacity::Definition {context}=>match context {
            Part2TypedCapacityContext::Definition {..}|Part2TypedCapacityContext::DefinitionCopy {..}=>part2_typed_capacity_count(context),
            _=>0,
        },
        Part2ColorOutputCapacity::LayoutColors {definitions,colors}=>if part2_color_layout_has_definitions(definitions) || definitions.len()==colors {colors as nat}else{0},
        Part2ColorOutputCapacity::LayoutAlpha {definitions,colors,component,record}=>if part2_color_layout_alpha_admitted(definitions,colors,component,record){1}else{0},
        Part2ColorOutputCapacity::Normalize {context}=>part2_color_normalize_count(context),
        Part2ColorOutputCapacity::Channels {context}=>match part2_color_convert_preflight(context){Err(_)=>0,Ok((format,layout,_))=>format.0 as nat+layout.1.len()},
        Part2ColorOutputCapacity::Sycc {context,role}=>match part2_color_convert_preflight(context){Err(_)=>0,Ok((format,_,count))=>if format.2 && role<3 {count as nat}else{0}},
        Part2ColorOutputCapacity::EsrgbChannels {context}=>if color_esrgb_preflight(context).is_ok(){3}else{0},
        Part2ColorOutputCapacity::EsrgbPlane {image,colors,role}=>match color_esrgb_plane_admission(image,colors,role){Err(_)=>0,Ok((_,_,count))=>count as nat},
        Part2ColorOutputCapacity::CropChannels {context}=>if part2_color_crop_admitted(context){context.image.4.len()}else{0},
        Part2ColorOutputCapacity::CropPlane {count,..}=>count as nat,
    }
}
pub(crate) open spec fn part2_color_output_capacity_run(context:Part2ColorOutputCapacity,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_color_output_capacity_count(context);
    if count==0 {Some((Ok(()),events))}else if events.len()==0 {None}else{
        match events[0] {
            Part2JpipSnapshotEvent::ColorOutputCapacity {context:actual,elements,succeeded}=>
                if actual!=context || elements!=count {None}else{
                    Some((if succeeded {Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))
                },
            _=>None,
        }
    }
}
pub(crate) open spec fn part2_color_output_capacity_result(context:Part2ColorOutputCapacity,result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_color_output_capacity_run(context,events),result)
}
pub(crate) proof fn part2_color_output_capacity_observed(context:Part2ColorOutputCapacity,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_color_output_capacity_count(context)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_color_output_capacity_result(context,result),
{
    let count=part2_color_output_capacity_count(context);
    let prefix=if count==0 {Seq::empty()}else{
        seq![Part2JpipSnapshotEvent::ColorOutputCapacity {context,elements:count,succeeded:result.is_ok()}]
    };
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_color_output_capacity_run(context,prefix+tail)==Some((result,tail)) by {
        if count==0 {assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_color_output_capacity_run(context,events),prefix,result));
}
pub(crate) proof fn part2_color_definition_storage_observed(context:Part2TypedCapacityContext,response:Result<(),crate::DecodeError>)
    requires matches!(context,Part2TypedCapacityContext::Definition {..}|Part2TypedCapacityContext::DefinitionCopy {..}),
        part2_definition_storage_result(context,response),
    ensures part2_color_output_capacity_result(Part2ColorOutputCapacity::Definition {context},response),
{
    part2_definition_storage_frames(context,response);
    let run=|calls|part2_typed_capacity_run(context,calls);
    let prefix=choose|prefix:Seq<Part2Tier1StorageEvent>|part2_tier1_storage_prefix(run,prefix,response);
    part2_tier1_storage_at(run,prefix,response,Seq::empty());
    assert(prefix+Seq::<Part2Tier1StorageEvent>::empty() =~= prefix);
    part2_color_output_capacity_observed(Part2ColorOutputCapacity::Definition {context},response);
}
#[verifier::opaque]
pub(crate) open spec fn part2_color_output_requests_run(requests:Seq<Part2ColorOutputCapacity>,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>
    decreases requests.len(),
{
    if requests.len()==0 {Some((Ok(()),events))}else{
        part2_jpip_snapshot_bind(part2_color_output_capacity_run(requests[0],events),
            |_:(),rest|part2_color_output_requests_run(requests.drop_first(),rest))
    }
}
pub(crate) open spec fn part2_color_output_program_run<T>(requests:Seq<Part2ColorOutputCapacity>,ordinary:Result<T,crate::DecodeError>,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<T> {
    part2_jpip_snapshot_bind(part2_color_output_requests_run(requests,events),|_:(),rest|Some((ordinary,rest)))
}
pub(crate) open spec fn part2_color_output_program_result<T>(requests:Seq<Part2ColorOutputCapacity>,ordinary:Result<T,crate::DecodeError>,
    result:Result<T,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_color_output_program_run(requests,ordinary,events),result)
}
pub(crate) open spec fn part2_color_output_trace(step:spec_fn(nat)->Seq<Part2ColorOutputCapacity>,count:nat)->Seq<Part2ColorOutputCapacity>
    decreases count,
{
    if count==0 {Seq::empty()}else{part2_color_output_trace(step,(count-1) as nat)+step((count-1) as nat)}
}
pub(crate) open spec fn part2_color_layout_step_requests(definitions:Seq<Seq<ColorDefinition>>,colors:usize,component:nat,record:nat)->Seq<Part2ColorOutputCapacity> {
    if part2_color_layout_alpha_admitted(definitions,colors,component,record){
        seq![Part2ColorOutputCapacity::LayoutAlpha {definitions,colors,component,record}]
    }else{Seq::empty()}
}
pub(crate) open spec fn part2_color_layout_requests(definitions:Seq<Seq<ColorDefinition>>,colors:usize)->Seq<Part2ColorOutputCapacity> {
    let initial=seq![Part2ColorOutputCapacity::LayoutColors {definitions,colors}];
    initial+if part2_color_layout_has_definitions(definitions) {
        part2_color_output_trace(|component|part2_color_output_trace(|record|
            part2_color_layout_step_requests(definitions,colors,component,record),definitions[component as int].len()),definitions.len())
    }else{Seq::empty()}
}
pub(crate) open spec fn part2_color_normalize_requests(context:Part2ColorNormalizeContext)->Seq<Part2ColorOutputCapacity> {
    seq![Part2ColorOutputCapacity::Normalize {context}]
}
pub(crate) open spec fn part2_color_normalize_value(context:Part2ColorNormalizeContext)->Result<Seq<u16>,crate::DecodeError> {
    color_normalize_component(context.component,context.width,context.height,context.x,context.y)
}
pub(crate) open spec fn part2_color_channel_requests(components:Seq<Part1TypedComponentModel>,geometry:ColorGeometry,colors:Seq<usize>,index:usize)
    ->Seq<Part2ColorOutputCapacity> {
    if index>=colors.len() || colors[index as int]>=components.len() {Seq::empty()}else{
        part2_color_normalize_requests(Part2ColorNormalizeContext {component:components[colors[index as int] as int],
            width:geometry.0,height:geometry.1,x:geometry.2,y:geometry.3})
    }
}
pub(crate) open spec fn part2_color_alpha_requests(components:Seq<Part1TypedComponentModel>,geometry:ColorGeometry,alpha:(usize,bool,crate::image::ChannelAssociation))
    ->Seq<Part2ColorOutputCapacity> {
    if alpha.0>=components.len() {Seq::empty()}else{
        part2_color_normalize_requests(Part2ColorNormalizeContext {component:components[alpha.0 as int],
            width:geometry.0,height:geometry.1,x:geometry.2,y:geometry.3})
    }
}
pub(crate) open spec fn part2_color_convert_color_requests(context:Part2ColorConvertContext)->Seq<Part2ColorOutputCapacity> {
    let image=context.image;let geometry=image.0;
    match part2_color_convert_preflight(context) {
        Err(_)=>Seq::empty(),Ok((format,layout,_))=>if format.2 {
            seq![Part2ColorOutputCapacity::Sycc {context,role:0},Part2ColorOutputCapacity::Sycc {context,role:1},
                Part2ColorOutputCapacity::Sycc {context,role:2}]
        }else{
            part2_color_output_trace(|index:nat|if index<=usize::MAX
                && color_convert_channels_prefix(image.1,geometry,layout.0,format.0,index).is_ok() {
                part2_color_channel_requests(image.1,geometry,layout.0,index as usize)
            }else{Seq::empty()},format.0 as nat)
        },
    }
}
pub(crate) open spec fn part2_color_convert_alpha_requests(context:Part2ColorConvertContext)->Seq<Part2ColorOutputCapacity> {
    let image=context.image;let geometry=image.0;
    match part2_color_convert_preflight(context) {
        Err(_)=>Seq::empty(),Ok((format,layout,_))=>match color_convert_colors(image.1,geometry,layout.0,format.0,format.2) {
            Err(_)=>Seq::empty(),Ok(channels)=>part2_color_output_trace(|index:nat|
                if color_append_alphas_prefix(image.1,geometry,layout.1,channels,index).is_ok() {
                    part2_color_alpha_requests(image.1,geometry,layout.1[index as int])
                }else{Seq::empty()},layout.1.len()),
        },
    }
}
pub(crate) open spec fn part2_color_convert_after_layout_requests(context:Part2ColorConvertContext)->Seq<Part2ColorOutputCapacity> {
    if part2_color_convert_preflight(context).is_err(){Seq::empty()}else{
        seq![Part2ColorOutputCapacity::Channels {context}]+part2_color_convert_color_requests(context)+part2_color_convert_alpha_requests(context)
    }
}
pub(crate) open spec fn part2_color_convert_requests(context:Part2ColorConvertContext)->Seq<Part2ColorOutputCapacity> {
    if color_is_esrgb(context.method) {part2_esrgb_convert_requests(context)}else{
        let image=context.image;
        if image.0.0==0 || image.0.1==0 {Seq::empty()}else{
            match color_output_format(context.method) {
                Err(_)=>Seq::empty(),Ok(format)=>part2_color_layout_requests(image.2,format.0)+part2_color_convert_after_layout_requests(context),
            }
        }
    }
}
pub(crate) open spec fn part2_color_convert_value(context:Part2ColorConvertContext)->Part2ConvertedImageResult {
    color_convert_jp2(context.image.1,context.image.2,context.image.0,context.method,context.bytes,context.work)
}
pub(crate) open spec fn part2_color_convert_storage_run(context:Part2ColorConvertContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage> {
    part2_color_output_program_run(part2_color_convert_requests(context),part2_color_convert_value(context),events)
}
pub closed spec fn part2_color_convert_storage_result(context:Part2ColorConvertContext,result:Part2ConvertedImageResult)->bool {
    part2_cold_framed(|events|part2_color_convert_storage_run(context,events),result)
}
pub(crate) proof fn part2_color_convert_storage_from_program(context:Part2ColorConvertContext,result:Part2ConvertedImageResult)
    requires part2_color_output_program_result(part2_color_convert_requests(context),part2_color_convert_value(context),result),
    ensures part2_color_convert_storage_result(context,result),
{
    reveal(part2_color_convert_storage_result);
    part2_decode_eta(|events|part2_color_output_program_run(part2_color_convert_requests(context),part2_color_convert_value(context),events),result);
}

pub(crate) proof fn part2_color_output_trace_member(step:spec_fn(nat)->Seq<Part2ColorOutputCapacity>,count:nat,index:nat,request:Part2ColorOutputCapacity)
    requires index<count,step(index).contains(request),
    ensures part2_color_output_trace(step,count).contains(request),
    decreases count,
{
    reveal_with_fuel(part2_color_output_trace,1);
    if index<count-1 {part2_color_output_trace_member(step,(count-1) as nat,index,request);}
    part2_color_output_concat_member(part2_color_output_trace(step,(count-1) as nat),step((count-1) as nat),request);
}
pub(crate) proof fn part2_color_output_concat_member(left:Seq<Part2ColorOutputCapacity>,right:Seq<Part2ColorOutputCapacity>,request:Part2ColorOutputCapacity)
    requires left.contains(request) || right.contains(request),
    ensures (left+right).contains(request),
{
    if left.contains(request) {
        let index=choose|i:int|0<=i<left.len() && left[i]==request;
        assert((left+right)[index]==request);
    }else{
        let index=choose|i:int|0<=i<right.len() && right[i]==request;
        assert((left+right)[left.len()+index]==request);
    }
}
pub(crate) proof fn part2_color_output_requests_normal(requests:Seq<Part2ColorOutputCapacity>)
    ensures part2_cold_framed(|events|part2_color_output_requests_run(requests,events),Ok(())),
    decreases requests.len(),
{
    reveal(part2_color_output_requests_run);
    if requests.len()==0 {part2_cold_pure(Ok(()));}else{
        part2_color_output_capacity_observed(requests[0],Ok(()));
        part2_color_output_requests_normal(requests.drop_first());
        part2_decode_eta(|events|part2_color_output_requests_run(requests.drop_first(),events),Ok(()));
        part2_cold_bind(|events|part2_color_output_capacity_run(requests[0],events),
            |_:(),rest|part2_color_output_requests_run(requests.drop_first(),rest),Ok(()),Ok(()));
    }
}
pub(crate) proof fn part2_color_output_program_normal<T>(requests:Seq<Part2ColorOutputCapacity>,ordinary:Result<T,crate::DecodeError>)
    ensures part2_color_output_program_result(requests,ordinary,ordinary),
{
    part2_color_output_requests_normal(requests);part2_cold_pure(ordinary);
    part2_decode_eta(|events|part2_color_output_requests_run(requests,events),Ok(()));
    part2_cold_bind(|events|part2_color_output_requests_run(requests,events),|_:(),rest|Some((ordinary,rest)),Ok(()),ordinary);
}
pub(crate) proof fn part2_color_output_requests_refused(requests:Seq<Part2ColorOutputCapacity>,position:nat,error:crate::DecodeError)
    requires position<requests.len(),part2_color_output_capacity_result(requests[position as int],Err(error)),
    ensures part2_cold_framed(|events|part2_color_output_requests_run(requests,events),Err(error)),
    decreases position,
{
    reveal(part2_color_output_requests_run);
    if position==0 {
        part2_cold_bind(|events|part2_color_output_capacity_run(requests[0],events),
            |_:(),rest|part2_color_output_requests_run(requests.drop_first(),rest),Err(error),Err(error));
    }else{
        assert(requests.drop_first()[position as int-1]==requests[position as int]);
        part2_color_output_requests_refused(requests.drop_first(),(position-1) as nat,error);
        part2_decode_eta(|events|part2_color_output_requests_run(requests.drop_first(),events),Err(error));
        part2_color_output_capacity_observed(requests[0],Ok(()));
        part2_cold_bind(|events|part2_color_output_capacity_run(requests[0],events),
            |_:(),rest|part2_color_output_requests_run(requests.drop_first(),rest),Ok(()),Err(error));
    }
}
pub(crate) proof fn part2_color_output_program_refused<T>(requests:Seq<Part2ColorOutputCapacity>,ordinary:Result<T,crate::DecodeError>,
    request:Part2ColorOutputCapacity,error:crate::DecodeError)
    requires requests.contains(request),part2_color_output_capacity_result(request,Err(error)),
    ensures part2_color_output_program_result(requests,ordinary,Err(error)),
{
    let position=choose|i:int|0<=i<requests.len() && requests[i]==request;
    part2_color_output_requests_refused(requests,position as nat,error);
    part2_decode_eta(|events|part2_color_output_requests_run(requests,events),Err(error));
    part2_cold_bind(|events|part2_color_output_requests_run(requests,events),|_:(),rest|Some((ordinary,rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_color_output_requests_error(requests:Seq<Part2ColorOutputCapacity>,events:Seq<Part2JpipSnapshotEvent>,
    error:crate::DecodeError,rest:Seq<Part2JpipSnapshotEvent>)
    requires part2_color_output_requests_run(requests,events)==Some((Err(error),rest)),
    ensures exists|request:Part2ColorOutputCapacity|requests.contains(request) && part2_color_output_capacity_result(request,Err(error)),
    decreases requests.len(),
{
    reveal(part2_color_output_requests_run);
    if requests.len()>0 {
        if let Some((capacity,after))=part2_color_output_capacity_run(requests[0],events) {
            match capacity {
                Err(failed)=>{
                    part2_color_output_capacity_observed(requests[0],Err(failed));
                    assert(requests.contains(requests[0]));
                },
                Ok(())=>{
                    part2_color_output_requests_error(requests.drop_first(),after,error,rest);
                    let request=choose|request:Part2ColorOutputCapacity|requests.drop_first().contains(request)
                        && part2_color_output_capacity_result(request,Err(error));
                    assert(requests.contains(request));
                },
            }
        }
    }
}
pub(crate) proof fn part2_color_output_program_error_info<T>(requests:Seq<Part2ColorOutputCapacity>,ordinary:Result<T,crate::DecodeError>,error:crate::DecodeError)
    requires part2_color_output_program_result(requests,ordinary,Err(error)),
    ensures ordinary==Err(error) || (exists|request:Part2ColorOutputCapacity|requests.contains(request)
        && part2_color_output_capacity_result(request,Err(error))),
{
    let run=|events|part2_color_output_program_run(requests,ordinary,events);
    let prefix=choose|prefix:Seq<Part2JpipSnapshotEvent>|part2_cold_prefix(run,prefix,Err(error));
    part2_cold_prefix_at(run,prefix,Err(error),Seq::empty());
    assert(prefix+Seq::<Part2JpipSnapshotEvent>::empty() =~= prefix);
    if let Some((capacity,rest))=part2_color_output_requests_run(requests,prefix) {
        if capacity.is_err(){part2_color_output_requests_error(requests,prefix,error,rest);}
    }
}
pub(crate) proof fn part2_color_output_program_child_error<A,B>(
    whole:Seq<Part2ColorOutputCapacity>,ordinary:Result<B,crate::DecodeError>,
    child:Seq<Part2ColorOutputCapacity>,child_value:Result<A,crate::DecodeError>,error:crate::DecodeError,
)
    requires part2_color_output_program_result(child,child_value,Err(error)),
        child_value==Err(error) ==> ordinary==Err(error),
        forall|request:Part2ColorOutputCapacity|child.contains(request) ==> whole.contains(request),
    ensures part2_color_output_program_result(whole,ordinary,Err(error)),
{
    part2_color_output_program_error_info(child,child_value,error);
    if child_value==Err(error) {part2_color_output_program_normal(whole,ordinary);}else{
        let request=choose|request:Part2ColorOutputCapacity|child.contains(request) && part2_color_output_capacity_result(request,Err(error));
        part2_color_output_program_refused(whole,ordinary,request,error);
    }
}
pub(crate) proof fn part2_color_layout_alpha_present(definitions:Seq<Seq<ColorDefinition>>,colors:usize,component:nat,record:nat)
    requires component<definitions.len(),record<definitions[component as int].len(),
        part2_color_layout_has_definitions(definitions),part2_color_layout_alpha_admitted(definitions,colors,component,record),
    ensures part2_color_layout_requests(definitions,colors).contains(Part2ColorOutputCapacity::LayoutAlpha {definitions,colors,component,record}),
{
    let request=Part2ColorOutputCapacity::LayoutAlpha {definitions,colors,component,record};
    let definitions_step=|index|part2_color_layout_step_requests(definitions,colors,component,index);
    assert(definitions_step(record)==seq![request]);
    assert(definitions_step(record)[0]==request);
    assert(definitions_step(record).contains(request));
    part2_color_output_trace_member(definitions_step,definitions[component as int].len(),record,request);
    let components_step=|index|part2_color_output_trace(|record|part2_color_layout_step_requests(definitions,colors,index,record),definitions[index as int].len());
    part2_color_output_trace_member(components_step,definitions.len(),component,request);
    part2_color_output_concat_member(seq![Part2ColorOutputCapacity::LayoutColors {definitions,colors}],
        part2_color_output_trace(components_step,definitions.len()),request);
}
pub(crate) proof fn part2_color_convert_storage_normal(context:Part2ColorConvertContext)
    ensures part2_color_convert_storage_result(context,part2_color_convert_value(context)),
{
    reveal(part2_color_convert_storage_result);
    part2_color_output_program_normal(part2_color_convert_requests(context),part2_color_convert_value(context));
    part2_decode_eta(|events|part2_color_output_program_run(part2_color_convert_requests(context),part2_color_convert_value(context),events),
        part2_color_convert_value(context));
}
pub(crate) proof fn part2_color_convert_storage_frames(context:Part2ColorConvertContext,result:Part2ConvertedImageResult)
    requires part2_color_convert_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_color_convert_storage_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage>|
            (forall|events|#[trigger]other(events)==part2_color_convert_storage_run(context,events)) ==> #[trigger]part2_cold_framed(other,result),
{
    reveal(part2_color_convert_storage_result);
    part2_decode_eta(|events|part2_color_convert_storage_run(context,events),result);
}
pub(crate) proof fn part2_color_layout_owner_present(definitions:Seq<Seq<ColorDefinition>>,colors:usize)
    ensures part2_color_layout_requests(definitions,colors).contains(Part2ColorOutputCapacity::LayoutColors {definitions,colors}),
{
    assert(part2_color_layout_requests(definitions,colors)[0]==(Part2ColorOutputCapacity::LayoutColors {definitions,colors}));
}
pub(crate) open spec fn part2_color_layout_storage_result(definitions:Seq<Seq<ColorDefinition>>,colors:usize,result:ColorLayoutResult)->bool {
    part2_color_output_program_result(part2_color_layout_requests(definitions,colors),color_channel_layout(definitions,colors),result)
}
pub(crate) proof fn part2_color_layout_storage_normal(definitions:Seq<Seq<ColorDefinition>>,colors:usize)
    ensures part2_color_layout_storage_result(definitions,colors,color_channel_layout(definitions,colors)),
{part2_color_output_program_normal(part2_color_layout_requests(definitions,colors),color_channel_layout(definitions,colors));}
pub(crate) proof fn part2_color_layout_storage_refused(definitions:Seq<Seq<ColorDefinition>>,colors:usize,request:Part2ColorOutputCapacity,error:crate::DecodeError)
    requires part2_color_layout_requests(definitions,colors).contains(request),part2_color_output_capacity_result(request,Err(error)),
    ensures part2_color_layout_storage_result(definitions,colors,Err(error)),
{part2_color_output_program_refused(part2_color_layout_requests(definitions,colors),color_channel_layout(definitions,colors),request,error);}
pub(crate) open spec fn part2_color_normalize_storage_result(context:Part2ColorNormalizeContext,result:Result<Seq<u16>,crate::DecodeError>)->bool {
    part2_color_output_program_result(part2_color_normalize_requests(context),part2_color_normalize_value(context),result)
}
pub(crate) proof fn part2_color_normalize_storage_normal(context:Part2ColorNormalizeContext)
    ensures part2_color_normalize_storage_result(context,part2_color_normalize_value(context)),
{part2_color_output_program_normal(part2_color_normalize_requests(context),part2_color_normalize_value(context));}
pub(crate) proof fn part2_color_normalize_storage_refused(context:Part2ColorNormalizeContext,error:crate::DecodeError)
    requires part2_color_output_capacity_result(Part2ColorOutputCapacity::Normalize {context},Err(error)),
    ensures part2_color_normalize_storage_result(context,Err(error)),
{
    let request=Part2ColorOutputCapacity::Normalize {context};
    assert(part2_color_normalize_requests(context)[0]==request);
    part2_color_output_program_refused(part2_color_normalize_requests(context),part2_color_normalize_value(context),request,error);
}
pub(crate) open spec fn part2_color_channel_storage_result(components:Seq<Part1TypedComponentModel>,geometry:ColorGeometry,
    colors:Seq<usize>,count:usize,index:usize,result:Result<ColorChannelModel,crate::DecodeError>)->bool {
    part2_color_output_program_result(part2_color_channel_requests(components,geometry,colors,index),
        color_convert_channel(components,geometry,colors,count,index),result)
}
pub(crate) proof fn part2_color_channel_storage_normal(components:Seq<Part1TypedComponentModel>,geometry:ColorGeometry,colors:Seq<usize>,count:usize,index:usize)
    ensures part2_color_channel_storage_result(components,geometry,colors,count,index,color_convert_channel(components,geometry,colors,count,index)),
{
    part2_color_output_program_normal(part2_color_channel_requests(components,geometry,colors,index),color_convert_channel(components,geometry,colors,count,index));
}
pub(crate) proof fn part2_color_channel_storage_normalize_error(components:Seq<Part1TypedComponentModel>,geometry:ColorGeometry,colors:Seq<usize>,count:usize,index:usize,error:crate::DecodeError)
    requires index<colors.len(),colors[index as int]<components.len(),
        part2_color_normalize_storage_result(Part2ColorNormalizeContext {component:components[colors[index as int] as int],
            width:geometry.0,height:geometry.1,x:geometry.2,y:geometry.3},Err(error)),
    ensures part2_color_channel_storage_result(components,geometry,colors,count,index,Err(error)),
{
    let context=Part2ColorNormalizeContext {component:components[colors[index as int] as int],width:geometry.0,height:geometry.1,x:geometry.2,y:geometry.3};
    part2_color_output_program_child_error(part2_color_channel_requests(components,geometry,colors,index),
        color_convert_channel(components,geometry,colors,count,index),
        part2_color_normalize_requests(context),part2_color_normalize_value(context),error);
}
pub(crate) open spec fn part2_color_alpha_storage_result(components:Seq<Part1TypedComponentModel>,geometry:ColorGeometry,
    alpha:(usize,bool,crate::image::ChannelAssociation),result:Result<ColorChannelModel,crate::DecodeError>)->bool {
    part2_color_output_program_result(part2_color_alpha_requests(components,geometry,alpha),color_convert_alpha(components,geometry,alpha),result)
}
pub(crate) proof fn part2_color_alpha_storage_normal(components:Seq<Part1TypedComponentModel>,geometry:ColorGeometry,alpha:(usize,bool,crate::image::ChannelAssociation))
    ensures part2_color_alpha_storage_result(components,geometry,alpha,color_convert_alpha(components,geometry,alpha)),
{part2_color_output_program_normal(part2_color_alpha_requests(components,geometry,alpha),color_convert_alpha(components,geometry,alpha));}
pub(crate) proof fn part2_color_alpha_storage_normalize_error(components:Seq<Part1TypedComponentModel>,geometry:ColorGeometry,
    alpha:(usize,bool,crate::image::ChannelAssociation),error:crate::DecodeError)
    requires alpha.0<components.len(),part2_color_normalize_storage_result(Part2ColorNormalizeContext {component:components[alpha.0 as int],
        width:geometry.0,height:geometry.1,x:geometry.2,y:geometry.3},Err(error)),
    ensures part2_color_alpha_storage_result(components,geometry,alpha,Err(error)),
{
    let context=Part2ColorNormalizeContext {component:components[alpha.0 as int],width:geometry.0,height:geometry.1,x:geometry.2,y:geometry.3};
    part2_color_output_program_child_error(part2_color_alpha_requests(components,geometry,alpha),color_convert_alpha(components,geometry,alpha),
        part2_color_normalize_requests(context),part2_color_normalize_value(context),error);
}
pub(crate) proof fn part2_color_convert_layout_error(context:Part2ColorConvertContext,format:(usize,crate::color::ConvertedColorSpace,bool),error:crate::DecodeError)
    requires context.image.0.0>0,context.image.0.1>0,color_output_format(context.method)==Ok(format),
        part2_color_layout_storage_result(context.image.2,format.0,Err(error)),
    ensures part2_color_convert_storage_result(context,Err(error)),
{
    color_output_format_not_esrgb(context.method);
    reveal(part2_color_convert_storage_result);
    let child=part2_color_layout_requests(context.image.2,format.0);
    let after=part2_color_convert_after_layout_requests(context);
    assert forall|request:Part2ColorOutputCapacity|child.contains(request) implies part2_color_convert_requests(context).contains(request) by {
        part2_color_output_concat_member(child,after,request);
    }
    part2_color_output_program_child_error(part2_color_convert_requests(context),part2_color_convert_value(context),child,
        color_channel_layout(context.image.2,format.0),error);
    part2_decode_eta(|events|part2_color_output_program_run(part2_color_convert_requests(context),part2_color_convert_value(context),events),Err(error));
}
pub(crate) proof fn part2_color_convert_after_layout_member(context:Part2ColorConvertContext,request:Part2ColorOutputCapacity)
    requires part2_color_convert_preflight(context).is_ok(),part2_color_convert_after_layout_requests(context).contains(request),
    ensures part2_color_convert_requests(context).contains(request),
{
    assert(color_output_format(context.method).is_ok());
    color_output_format_not_esrgb(context.method);
    let preflight=part2_color_convert_preflight(context).get_Ok_0();
    part2_color_output_concat_member(part2_color_layout_requests(context.image.2,preflight.0.0),part2_color_convert_after_layout_requests(context),request);
}
pub(crate) proof fn part2_color_convert_owner_present(context:Part2ColorConvertContext)
    requires part2_color_convert_preflight(context).is_ok(),
    ensures part2_color_convert_requests(context).contains(Part2ColorOutputCapacity::Channels {context}),
{
    let request=Part2ColorOutputCapacity::Channels {context};
    assert(part2_color_convert_after_layout_requests(context)[0]==request);
    assert(part2_color_convert_after_layout_requests(context).contains(request));
    part2_color_convert_after_layout_member(context,request);
}
pub(crate) proof fn part2_color_convert_sycc_present(context:Part2ColorConvertContext,role:u8)
    requires part2_color_convert_preflight(context).is_ok(),part2_color_convert_preflight(context).get_Ok_0().0.2,role<3,
    ensures part2_color_convert_requests(context).contains(Part2ColorOutputCapacity::Sycc {context,role}),
{
    let request=Part2ColorOutputCapacity::Sycc {context,role};
    assert(part2_color_convert_color_requests(context)[role as int]==request) by {
        if role==0 {}else if role==1 {}else{assert(role==2);}
    }
    assert(part2_color_convert_color_requests(context).contains(request));
    part2_color_output_concat_member(seq![Part2ColorOutputCapacity::Channels {context}],part2_color_convert_color_requests(context),request);
    part2_color_output_concat_member(seq![Part2ColorOutputCapacity::Channels {context}]+part2_color_convert_color_requests(context),
        part2_color_convert_alpha_requests(context),request);
    part2_color_convert_after_layout_member(context,request);
}
pub(crate) proof fn part2_color_convert_storage_refused(context:Part2ColorConvertContext,request:Part2ColorOutputCapacity,error:crate::DecodeError)
    requires part2_color_convert_requests(context).contains(request),part2_color_output_capacity_result(request,Err(error)),
    ensures part2_color_convert_storage_result(context,Err(error)),
{
    reveal(part2_color_convert_storage_result);
    part2_color_output_program_refused(part2_color_convert_requests(context),part2_color_convert_value(context),request,error);
    part2_decode_eta(|events|part2_color_output_program_run(part2_color_convert_requests(context),part2_color_convert_value(context),events),Err(error));
}
pub(crate) proof fn part2_color_convert_channel_error(context:Part2ColorConvertContext,format:(usize,crate::color::ConvertedColorSpace,bool),
    layout:ColorLayoutState,count:usize,index:usize,error:crate::DecodeError)
    requires part2_color_convert_preflight(context)==Ok((format,layout,count)),!format.2,index<format.0,
        color_convert_channels_prefix(context.image.1,context.image.0,layout.0,format.0,index as nat).is_ok(),
        part2_color_channel_storage_result(context.image.1,context.image.0,layout.0,format.0,index,Err(error)),
        color_convert_channel(context.image.1,context.image.0,layout.0,format.0,index)==Err(error) ==> part2_color_convert_value(context)==Err(error),
    ensures part2_color_convert_storage_result(context,Err(error)),
{
    reveal(part2_color_convert_storage_result);
    let child=part2_color_channel_requests(context.image.1,context.image.0,layout.0,index);
    let step=|i:nat|if i<=usize::MAX && color_convert_channels_prefix(context.image.1,context.image.0,layout.0,format.0,i).is_ok() {
        part2_color_channel_requests(context.image.1,context.image.0,layout.0,i as usize)
    }else{Seq::empty()};
    assert forall|request:Part2ColorOutputCapacity|child.contains(request) implies part2_color_convert_requests(context).contains(request) by {
        assert(step(index as nat)==child);
        part2_color_output_trace_member(step,format.0 as nat,index as nat,request);
        part2_color_output_concat_member(seq![Part2ColorOutputCapacity::Channels {context}],part2_color_convert_color_requests(context),request);
        part2_color_output_concat_member(seq![Part2ColorOutputCapacity::Channels {context}]+part2_color_convert_color_requests(context),
            part2_color_convert_alpha_requests(context),request);
        part2_color_convert_after_layout_member(context,request);
    }
    part2_color_output_program_child_error(part2_color_convert_requests(context),part2_color_convert_value(context),child,
        color_convert_channel(context.image.1,context.image.0,layout.0,format.0,index),error);
    part2_decode_eta(|events|part2_color_output_program_run(part2_color_convert_requests(context),part2_color_convert_value(context),events),Err(error));
}
pub(crate) proof fn part2_color_convert_alpha_error(context:Part2ColorConvertContext,format:(usize,crate::color::ConvertedColorSpace,bool),
    layout:ColorLayoutState,count:usize,initial:Seq<ColorChannelModel>,index:nat,error:crate::DecodeError)
    requires part2_color_convert_preflight(context)==Ok((format,layout,count)),index<layout.1.len(),
        color_convert_colors(context.image.1,context.image.0,layout.0,format.0,format.2)==Ok(initial),
        color_append_alphas_prefix(context.image.1,context.image.0,layout.1,initial,index).is_ok(),
        part2_color_alpha_storage_result(context.image.1,context.image.0,layout.1[index as int],Err(error)),
        color_convert_alpha(context.image.1,context.image.0,layout.1[index as int])==Err(error) ==> part2_color_convert_value(context)==Err(error),
    ensures part2_color_convert_storage_result(context,Err(error)),
{
    reveal(part2_color_convert_storage_result);
    let child=part2_color_alpha_requests(context.image.1,context.image.0,layout.1[index as int]);
    let step=|i:nat|if color_append_alphas_prefix(context.image.1,context.image.0,layout.1,initial,i).is_ok() {
        part2_color_alpha_requests(context.image.1,context.image.0,layout.1[i as int])
    }else{Seq::empty()};
    assert forall|request:Part2ColorOutputCapacity|child.contains(request) implies part2_color_convert_requests(context).contains(request) by {
        assert(step(index)==child);
        part2_color_output_trace_member(step,layout.1.len(),index,request);
        part2_color_output_concat_member(seq![Part2ColorOutputCapacity::Channels {context}]+part2_color_convert_color_requests(context),
            part2_color_convert_alpha_requests(context),request);
        part2_color_convert_after_layout_member(context,request);
    }
    part2_color_output_program_child_error(part2_color_convert_requests(context),part2_color_convert_value(context),child,
        color_convert_alpha(context.image.1,context.image.0,layout.1[index as int]),error);
    part2_decode_eta(|events|part2_color_output_program_run(part2_color_convert_requests(context),part2_color_convert_value(context),events),Err(error));
}
pub(crate) open spec fn part2_color_crop_plane_request(source:Seq<u16>,source_width:u32,x:u32,y:u32,x1:u32,y1:u32,count:usize)->Part2ColorOutputCapacity {
    Part2ColorOutputCapacity::CropPlane {source,source_width,x,y,x1,y1,count}
}
pub(crate) open spec fn part2_color_crop_requests(context:Part2ColorCropContext)->Seq<Part2ColorOutputCapacity> {
    if !part2_color_crop_admitted(context){Seq::empty()}else{
        let x1=(context.x+context.width) as u32;let y1=(context.y+context.height) as u32;
        let count=part2_layer_area(context.width,context.height).get_Ok_0();
        seq![Part2ColorOutputCapacity::CropChannels {context}]
        +part2_color_output_trace(|index:nat|if color_crop_channels(context.image.4,context.image.0,context.x,context.y,x1,y1,index).is_ok() {
            seq![part2_color_crop_plane_request(context.image.4[index as int].1,context.image.0,context.x,context.y,x1,y1,count)]
        }else{Seq::empty()},context.image.4.len())
    }
}
pub(crate) open spec fn part2_color_crop_value(context:Part2ColorCropContext)->Part2ConvertedImageResult {
    color_crop_image(context.image,context.x,context.y,context.width,context.height)
}
pub(crate) open spec fn part2_color_crop_storage_run(context:Part2ColorCropContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage> {
    part2_color_output_program_run(part2_color_crop_requests(context),part2_color_crop_value(context),events)
}
pub(crate) open spec fn part2_color_crop_storage_result(context:Part2ColorCropContext,result:Part2ConvertedImageResult)->bool {
    part2_cold_framed(|events|part2_color_crop_storage_run(context,events),result)
}
pub(crate) proof fn part2_color_crop_storage_normal(context:Part2ColorCropContext)
    ensures part2_color_crop_storage_result(context,part2_color_crop_value(context)),
{
    part2_color_output_program_normal(part2_color_crop_requests(context),part2_color_crop_value(context));
    part2_decode_eta(|events|part2_color_output_program_run(part2_color_crop_requests(context),part2_color_crop_value(context),events),part2_color_crop_value(context));
}
pub(crate) proof fn part2_color_crop_storage_owner_refused(context:Part2ColorCropContext,error:crate::DecodeError)
    requires part2_color_crop_admitted(context),part2_color_output_capacity_result(Part2ColorOutputCapacity::CropChannels {context},Err(error)),
    ensures part2_color_crop_storage_result(context,Err(error)),
{
    let request=Part2ColorOutputCapacity::CropChannels {context};
    assert(part2_color_crop_requests(context)[0]==request);
    part2_color_output_program_refused(part2_color_crop_requests(context),part2_color_crop_value(context),request,error);
    part2_decode_eta(|events|part2_color_output_program_run(part2_color_crop_requests(context),part2_color_crop_value(context),events),Err(error));
}
pub(crate) open spec fn part2_color_crop_plane_storage_result(source:Seq<u16>,source_width:u32,x:u32,y:u32,x1:u32,y1:u32,count:usize,
    result:Result<Seq<u16>,crate::DecodeError>)->bool {
    part2_color_output_program_result(seq![part2_color_crop_plane_request(source,source_width,x,y,x1,y1,count)],
        color_crop_plane(source,source_width,x,y,x1,y1),result)
}
pub(crate) proof fn part2_color_crop_plane_storage_normal(source:Seq<u16>,source_width:u32,x:u32,y:u32,x1:u32,y1:u32,count:usize)
    ensures part2_color_crop_plane_storage_result(source,source_width,x,y,x1,y1,count,color_crop_plane(source,source_width,x,y,x1,y1)),
{
    part2_color_output_program_normal(seq![part2_color_crop_plane_request(source,source_width,x,y,x1,y1,count)],
        color_crop_plane(source,source_width,x,y,x1,y1));
}
pub(crate) proof fn part2_color_crop_plane_storage_refused(source:Seq<u16>,source_width:u32,x:u32,y:u32,x1:u32,y1:u32,count:usize,error:crate::DecodeError)
    requires part2_color_output_capacity_result(part2_color_crop_plane_request(source,source_width,x,y,x1,y1,count),Err(error)),
    ensures part2_color_crop_plane_storage_result(source,source_width,x,y,x1,y1,count,Err(error)),
{
    let request=part2_color_crop_plane_request(source,source_width,x,y,x1,y1,count);
    assert(seq![request][0]==request);
    part2_color_output_program_refused(seq![request],color_crop_plane(source,source_width,x,y,x1,y1),request,error);
}
pub(crate) proof fn part2_color_crop_storage_plane_error(context:Part2ColorCropContext,index:nat,count:usize,error:crate::DecodeError)
    requires part2_color_crop_admitted(context),index<context.image.4.len(),part2_layer_area(context.width,context.height)==Ok(count),
        color_crop_channels(context.image.4,context.image.0,context.x,context.y,(context.x+context.width) as u32,(context.y+context.height) as u32,index).is_ok(),
        part2_color_crop_plane_storage_result(context.image.4[index as int].1,context.image.0,context.x,context.y,
            (context.x+context.width) as u32,(context.y+context.height) as u32,count,Err(error)),
        color_crop_plane(context.image.4[index as int].1,context.image.0,context.x,context.y,
            (context.x+context.width) as u32,(context.y+context.height) as u32)==Err(error) ==> part2_color_crop_value(context)==Err(error),
    ensures part2_color_crop_storage_result(context,Err(error)),
{
    let x1=(context.x+context.width) as u32;let y1=(context.y+context.height) as u32;
    let request=part2_color_crop_plane_request(context.image.4[index as int].1,context.image.0,context.x,context.y,x1,y1,count);
    let step=|i:nat|if color_crop_channels(context.image.4,context.image.0,context.x,context.y,x1,y1,i).is_ok() {
        seq![part2_color_crop_plane_request(context.image.4[i as int].1,context.image.0,context.x,context.y,x1,y1,count)]
    }else{Seq::empty()};
    assert(step(index)[0]==request);
    part2_color_output_trace_member(step,context.image.4.len(),index,request);
    part2_color_output_concat_member(seq![Part2ColorOutputCapacity::CropChannels {context}],part2_color_output_trace(step,context.image.4.len()),request);
    assert forall|child:Part2ColorOutputCapacity|seq![request].contains(child) implies part2_color_crop_requests(context).contains(child) by {
        assert(child==request);
    }
    part2_color_output_program_child_error(part2_color_crop_requests(context),part2_color_crop_value(context),seq![request],
        color_crop_plane(context.image.4[index as int].1,context.image.0,context.x,context.y,x1,y1),error);
    part2_decode_eta(|events|part2_color_output_program_run(part2_color_crop_requests(context),part2_color_crop_value(context),events),Err(error));
}
pub(crate) open spec fn part2_color_selected_after(context:Part2ColorConvertContext,target:[u32;4],converted:ColorImageModel,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage> {
    let geometry=context.image.0;
    if target[0]<geometry.2 || target[1]<geometry.3 || target[2]<target[0] || target[3]<target[1] {
        Some((Err(color_selection_target_error()),events))
    }else{
        part2_color_crop_storage_run(Part2ColorCropContext {image:converted,x:(target[0]-geometry.2) as u32,y:(target[1]-geometry.3) as u32,
            width:(target[2]-target[0]) as u32,height:(target[3]-target[1]) as u32},events)
    }
}
pub(crate) open spec fn part2_color_selected_storage_run(context:Part2ColorConvertContext,target:[u32;4],events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage> {
    part2_jpip_snapshot_bind(part2_color_convert_storage_run(context,events),
        |converted,rest|part2_color_selected_after(context,target,converted,rest))
}
pub(crate) open spec fn part2_color_selected_storage_result(context:Part2ColorConvertContext,target:[u32;4],result:Part2ConvertedImageResult)->bool {
    part2_cold_framed(|events|part2_color_selected_storage_run(context,target,events),result)
}
pub(crate) proof fn part2_color_selected_storage_normal(context:Part2ColorConvertContext,target:[u32;4])
    ensures part2_color_selected_storage_result(context,target,color_convert_selected(context.image.1,context.image.2,context.image.0,
        context.method,target,context.bytes,context.work)),
{
    reveal(part2_color_convert_storage_result);
    let converted=part2_color_convert_value(context);
    let result=color_convert_selected(context.image.1,context.image.2,context.image.0,context.method,target,context.bytes,context.work);
    part2_color_convert_storage_normal(context);
    if let Ok(image)=converted {
        let geometry=context.image.0;
        if target[0]<geometry.2 || target[1]<geometry.3 || target[2]<target[0] || target[3]<target[1] {part2_cold_pure(result);}else{
            let crop=Part2ColorCropContext {image,x:(target[0]-geometry.2) as u32,y:(target[1]-geometry.3) as u32,
                width:(target[2]-target[0]) as u32,height:(target[3]-target[1]) as u32};
            part2_color_crop_storage_normal(crop);
            part2_decode_eta(|events|part2_color_crop_storage_run(crop,events),result);
        }
    }
    part2_cold_bind(|events|part2_color_convert_storage_run(context,events),
        |converted,rest|part2_color_selected_after(context,target,converted,rest),converted,result);
}
pub(crate) proof fn part2_color_selected_storage_convert_error(context:Part2ColorConvertContext,target:[u32;4],error:crate::DecodeError)
    requires part2_color_convert_storage_result(context,Err(error)),
    ensures part2_color_selected_storage_result(context,target,Err(error)),
{
    reveal(part2_color_convert_storage_result);
    part2_cold_bind(|events|part2_color_convert_storage_run(context,events),
        |converted,rest|part2_color_selected_after(context,target,converted,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_color_selected_storage_crop_actual(context:Part2ColorConvertContext,target:[u32;4],converted:ColorImageModel,result:Part2ConvertedImageResult)
    requires part2_color_convert_storage_result(context,Ok(converted)),
        target[0]>=context.image.0.2,target[1]>=context.image.0.3,target[2]>=target[0],target[3]>=target[1],
        part2_color_crop_storage_result(Part2ColorCropContext {image:converted,
            x:(target[0]-context.image.0.2) as u32,y:(target[1]-context.image.0.3) as u32,
            width:(target[2]-target[0]) as u32,height:(target[3]-target[1]) as u32},result),
    ensures part2_color_selected_storage_result(context,target,result),
{
    reveal(part2_color_convert_storage_result);
    let crop=Part2ColorCropContext {image:converted,x:(target[0]-context.image.0.2) as u32,y:(target[1]-context.image.0.3) as u32,
        width:(target[2]-target[0]) as u32,height:(target[3]-target[1]) as u32};
    part2_decode_eta(|events|part2_color_crop_storage_run(crop,events),result);
    part2_cold_bind(|events|part2_color_convert_storage_run(context,events),
        |converted,rest|part2_color_selected_after(context,target,converted,rest),Ok(converted),result);
}
pub(crate) open spec fn part2_color_associated_storage_run(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,target:Option<[u32;4]>,
    bytes:u64,work:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage> {
    match header {
        None=>Some((Err(crate::DecodeError::MalformedInput {offset:0,kind:crate::MalformedKind::MissingRequiredStructure}),events)),
        Some(header)=>{
            let context=Part2ColorConvertContext {image,method:header.2,bytes,work};
            match target {None=>part2_color_convert_storage_run(context,events),Some(target)=>part2_color_selected_storage_run(context,target,events)}
        },
    }
}
pub(crate) open spec fn part2_color_associated_storage_result(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,target:Option<[u32;4]>,
    bytes:u64,work:u64,result:Part2ConvertedImageResult)->bool {
    part2_cold_framed(|events|part2_color_associated_storage_run(image,header,target,bytes,work,events),result)
}
pub(crate) proof fn part2_color_associated_storage_normal(image:Part1DecodedTypedImage,header:Option<Part2AssociatedHeader>,target:Option<[u32;4]>,bytes:u64,work:u64)
    ensures part2_color_associated_storage_result(image,header,target,bytes,work,
        match target {None=>part2_convert_associated(image,header,bytes,work),Some(target)=>part2_convert_associated_selected(image,header,target,bytes,work)}),
{
    let result=match target {None=>part2_convert_associated(image,header,bytes,work),Some(target)=>part2_convert_associated_selected(image,header,target,bytes,work)};
    match header {
        None=>part2_cold_pure(result),
        Some(header)=>{
            let context=Part2ColorConvertContext {image,method:header.2,bytes,work};
            match target {
                None=>{
                    reveal(part2_color_convert_storage_result);part2_color_convert_storage_normal(context);
                    part2_decode_eta(|events|part2_color_convert_storage_run(context,events),result);
                },
                Some(target)=>{
                    part2_color_selected_storage_normal(context,target);
                    part2_decode_eta(|events|part2_color_selected_storage_run(context,target,events),result);
                },
            }
        },
    }
}
pub(crate) proof fn part2_color_associated_storage_actual(image:Part1DecodedTypedImage,header:Part2AssociatedHeader,target:Option<[u32;4]>,
    bytes:u64,work:u64,result:Part2ConvertedImageResult)
    requires match target {
        None=>part2_color_convert_storage_result(Part2ColorConvertContext {image,method:header.2,bytes,work},result),
        Some(target)=>part2_color_selected_storage_result(Part2ColorConvertContext {image,method:header.2,bytes,work},target,result),
    },
    ensures part2_color_associated_storage_result(image,Some(header),target,bytes,work,result),
{
    let context=Part2ColorConvertContext {image,method:header.2,bytes,work};
    match target {
        None=>{reveal(part2_color_convert_storage_result);part2_decode_eta(|events|part2_color_convert_storage_run(context,events),result);},
        Some(target)=>part2_decode_eta(|events|part2_color_selected_storage_run(context,target,events),result),
    }
}
}
