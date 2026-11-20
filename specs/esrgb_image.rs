//! PIMA Annex A default RGB clipping, with source-derived ordered storage.
use super::*;
verus! {

pub open spec fn color_is_esrgb(method:crate::jp2::ColorMethod)->bool {
    matches!(method,crate::jp2::ColorMethod::Enumerated {color_space:20})
}
pub(crate) proof fn color_output_format_not_esrgb(method:crate::jp2::ColorMethod)
    requires color_output_format(method).is_ok(),
    ensures !color_is_esrgb(method),
{
    reveal(color_output_format);
    if color_is_esrgb(method) {
        assert(method==crate::jp2::ColorMethod::Enumerated {color_space:20});
        assert(color_output_format(method).is_err());
    }
}
pub open spec fn color_esrgb_source_component(component:Part1TypedComponentModel,precision:u8)
    ->Result<(),crate::DecodeError> {
    if component.info.precision!=precision || component.info.signed
        || matches!(component.samples,Part1TypedSampleSequence::Signed(_)) {
        Err(part2_color_input_error())
    }else{Ok(())}
}
pub open spec fn color_esrgb_source(image:Part1DecodedTypedImage)->Result<(),crate::DecodeError> {
    if image.0.0==0 || image.0.1==0 {Err(part2_color_input_error())}
    else if image.1.len()!=3 {Err(color_layout_error())}
    else {
        let precision=image.1[0].info.precision;
        if precision!=10 && precision!=12 && precision!=16 {
            Err(crate::DecodeError::UnsupportedColorConversion {reason:crate::UnsupportedColorConversion::EnumeratedColorSpace})
        }else{match color_esrgb_source_component(image.1[0],precision) {
            Err(error)=>Err(error),Ok(())=>match color_esrgb_source_component(image.1[1],precision) {
                Err(error)=>Err(error),Ok(())=>color_esrgb_source_component(image.1[2],precision),
            },
        }}
    }
}
pub open spec fn color_esrgb_after_layout(image:Part1DecodedTypedImage,layout:ColorLayoutState,bytes:u64,work:u64)
    ->Result<usize,crate::DecodeError> {
    if layout.0.len()!=3 {Err(color_layout_error())}
    else if layout.1.len()!=0 {
        Err(crate::DecodeError::UnsupportedColorConversion {reason:crate::UnsupportedColorConversion::AlphaAssociation})
    }else{match color_validate_components(image.1,image.0,layout) {
        Err(error)=>Err(error),Ok(())=>match color_validate_output_size(image.0.0,image.0.1,3,0,bytes,work) {
            Err(error)=>Err(error),Ok(())=>part2_layer_area(image.0.0,image.0.1),
        },
    }}
}
pub open spec fn color_esrgb_preflight(context:Part2ColorConvertContext)->Result<(ColorLayoutState,usize),crate::DecodeError> {
    match color_esrgb_source(context.image) {
        Err(error)=>Err(error),Ok(())=>match color_channel_layout(context.image.2,3) {
            Err(error)=>Err(error),Ok(layout)=>match color_esrgb_after_layout(context.image,layout,context.bytes,context.work) {
                Err(error)=>Err(error),Ok(count)=>Ok((layout,count)),
            },
        },
    }
}
pub open spec fn color_esrgb_pixel(component:Part1TypedComponentModel,geometry:ColorGeometry,width:usize,pixel:usize)
    ->Result<u16,crate::DecodeError> {
    match color_pixel_coordinates(pixel,width) {
        Err(error)=>Err(error),Ok((x,y))=>match color_component_nominal(component,geometry.2,geometry.3,x,y) {
            Err(error)=>Err(error),Ok(value)=>color_esrgb_sample_to_srgb16(value,component.info.precision),
        },
    }
}
#[verifier::opaque]
pub open spec fn color_esrgb_plane_prefix(component:Part1TypedComponentModel,geometry:ColorGeometry,width:usize,count:nat)
    ->Result<Seq<u16>,crate::DecodeError>
    decreases count,
{
    if count==0 {Ok(Seq::empty())}else{
        match color_esrgb_plane_prefix(component,geometry,width,(count-1) as nat) {
            Err(error)=>Err(error),Ok(samples)=>if count-1>usize::MAX {Err(part2_composition_error(true))}else{
                match color_esrgb_pixel(component,geometry,width,(count-1) as usize) {
                    Err(error)=>Err(error),Ok(sample)=>Ok(samples.push(sample)),
                }
            },
        }
    }
}
pub open spec fn color_esrgb_plane_admission(image:Part1DecodedTypedImage,colors:Seq<usize>,role:usize)
    ->Result<(Part1TypedComponentModel,usize,usize),crate::DecodeError> {
    if role>=colors.len() || colors[role as int]>=image.1.len() {Err(part2_color_input_error())}
    else if image.0.0 as nat>usize::MAX {Err(part2_composition_error(true))}
    else if image.0.0==0 {Err(part2_color_input_error())}
    else {match part2_layer_area(image.0.0,image.0.1) {
        Err(error)=>Err(error),Ok(count)=>Ok((image.1[colors[role as int] as int],image.0.0 as usize,count)),
    }}
}
pub open spec fn color_esrgb_plane(image:Part1DecodedTypedImage,colors:Seq<usize>,role:usize)
    ->Result<Seq<u16>,crate::DecodeError> {
    match color_esrgb_plane_admission(image,colors,role) {
        Err(error)=>Err(error),Ok((component,width,count))=>color_esrgb_plane_prefix(component,image.0,width,count as nat),
    }
}
pub open spec fn color_esrgb_planes(image:Part1DecodedTypedImage,colors:Seq<usize>)->Result<Seq<ColorChannelModel>,crate::DecodeError> {
    match color_esrgb_plane(image,colors,0) {
        Err(error)=>Err(error),Ok(red)=>match color_esrgb_plane(image,colors,1) {
            Err(error)=>Err(error),Ok(green)=>match color_esrgb_plane(image,colors,2) {
                Err(error)=>Err(error),Ok(blue)=>Ok(seq![
                    (crate::color::ConvertedChannelType::Red,red),
                    (crate::color::ConvertedChannelType::Green,green),
                    (crate::color::ConvertedChannelType::Blue,blue)]),
            },
        },
    }
}
pub open spec fn color_convert_esrgb(image:Part1DecodedTypedImage,bytes:u64,work:u64)->Part2ConvertedImageResult {
    let context=Part2ColorConvertContext {image,method:crate::jp2::ColorMethod::Enumerated {color_space:20},bytes,work};
    match color_esrgb_preflight(context) {
        Err(error)=>Err(error),Ok((layout,_))=>match color_esrgb_planes(image,layout.0) {
            Err(error)=>Err(error),Ok(channels)=>Ok((image.0.0,image.0.1,crate::color::ConvertedColorSpace::Srgb,16,channels)),
        },
    }
}
pub(crate) open spec fn part2_esrgb_plane_requests(image:Part1DecodedTypedImage,colors:Seq<usize>,role:usize)->Seq<Part2ColorOutputCapacity> {
    if color_esrgb_plane_admission(image,colors,role).is_err(){Seq::empty()}else{
        seq![Part2ColorOutputCapacity::EsrgbPlane {image,colors,role}]
    }
}
pub(crate) open spec fn part2_esrgb_plane_storage_result(image:Part1DecodedTypedImage,colors:Seq<usize>,role:usize,result:Result<Seq<u16>,crate::DecodeError>)->bool {
    part2_color_output_program_result(part2_esrgb_plane_requests(image,colors,role),color_esrgb_plane(image,colors,role),result)
}
pub(crate) open spec fn part2_esrgb_after_layout_requests(context:Part2ColorConvertContext)->Seq<Part2ColorOutputCapacity> {
    match color_esrgb_preflight(context) {
        Err(_)=>Seq::empty(),Ok((layout,_))=>{
            let image=context.image;let colors=layout.0;
            seq![Part2ColorOutputCapacity::EsrgbChannels {context}]
            +part2_esrgb_plane_requests(image,colors,0)
            +if color_esrgb_plane(image,colors,0).is_ok() {
                part2_esrgb_plane_requests(image,colors,1)
                +if color_esrgb_plane(image,colors,1).is_ok(){part2_esrgb_plane_requests(image,colors,2)}else{Seq::empty()}
            }else{Seq::empty()}
        },
    }
}
pub(crate) open spec fn part2_esrgb_convert_requests(context:Part2ColorConvertContext)->Seq<Part2ColorOutputCapacity> {
    if color_esrgb_source(context.image).is_err(){Seq::empty()}else{
        part2_color_layout_requests(context.image.2,3)+part2_esrgb_after_layout_requests(context)
    }
}
pub(crate) proof fn color_esrgb_prefix_error(component:Part1TypedComponentModel,geometry:ColorGeometry,width:usize,start:nat,end:nat,error:crate::DecodeError)
    requires start<=end,color_esrgb_plane_prefix(component,geometry,width,start)==Err(error),
    ensures color_esrgb_plane_prefix(component,geometry,width,end)==Err(error),
    decreases end-start,
{
    reveal_with_fuel(color_esrgb_plane_prefix,1);
    if start<end {color_esrgb_prefix_error(component,geometry,width,start,(end-1) as nat,error);}
}
pub(crate) proof fn part2_esrgb_plane_normal(image:Part1DecodedTypedImage,colors:Seq<usize>,role:usize)
    ensures part2_esrgb_plane_storage_result(image,colors,role,color_esrgb_plane(image,colors,role)),
{part2_color_output_program_normal(part2_esrgb_plane_requests(image,colors,role),color_esrgb_plane(image,colors,role));}
pub(crate) proof fn part2_esrgb_plane_refused(image:Part1DecodedTypedImage,colors:Seq<usize>,role:usize,error:crate::DecodeError)
    requires color_esrgb_plane_admission(image,colors,role).is_ok(),
        part2_color_output_capacity_result(Part2ColorOutputCapacity::EsrgbPlane {image,colors,role},Err(error)),
    ensures part2_esrgb_plane_storage_result(image,colors,role,Err(error)),
{
    let request=Part2ColorOutputCapacity::EsrgbPlane {image,colors,role};
    assert(part2_esrgb_plane_requests(image,colors,role)[0]==request);
    assert(part2_esrgb_plane_requests(image,colors,role).contains(request));
    part2_color_output_program_refused(part2_esrgb_plane_requests(image,colors,role),color_esrgb_plane(image,colors,role),request,error);
}
pub(crate) proof fn part2_esrgb_layout_error(context:Part2ColorConvertContext,error:crate::DecodeError)
    requires color_is_esrgb(context.method),color_esrgb_source(context.image).is_ok(),
        part2_color_layout_storage_result(context.image.2,3,Err(error)),
    ensures part2_color_convert_storage_result(context,Err(error)),
{
    let child=part2_color_layout_requests(context.image.2,3);
    assert forall|request:Part2ColorOutputCapacity|child.contains(request) implies part2_color_convert_requests(context).contains(request) by {
        part2_color_output_concat_member(child,part2_esrgb_after_layout_requests(context),request);
    }
    part2_color_output_program_child_error(part2_color_convert_requests(context),part2_color_convert_value(context),child,color_channel_layout(context.image.2,3),error);
    part2_color_convert_storage_from_program(context,Err(error));
}
pub(crate) proof fn part2_esrgb_channels_present(context:Part2ColorConvertContext)
    requires color_is_esrgb(context.method),color_esrgb_preflight(context).is_ok(),
    ensures part2_color_convert_requests(context).contains(Part2ColorOutputCapacity::EsrgbChannels {context}),
{
    let request=Part2ColorOutputCapacity::EsrgbChannels {context};
    assert(part2_esrgb_after_layout_requests(context)[0]==request);
    assert(part2_esrgb_after_layout_requests(context).contains(request));
    part2_color_output_concat_member(part2_color_layout_requests(context.image.2,3),part2_esrgb_after_layout_requests(context),request);
}
pub(crate) proof fn part2_esrgb_child_error(context:Part2ColorConvertContext,colors:Seq<usize>,role:usize,error:crate::DecodeError)
    requires color_is_esrgb(context.method),color_esrgb_preflight(context).is_ok(),
        colors==color_esrgb_preflight(context).get_Ok_0().0.0,role<3,
        role>0 ==> color_esrgb_plane(context.image,colors,0).is_ok(),
        role>1 ==> color_esrgb_plane(context.image,colors,1).is_ok(),
        part2_esrgb_plane_storage_result(context.image,colors,role,Err(error)),
    ensures part2_color_convert_storage_result(context,Err(error)),
{
    let image=context.image;
    let initial=seq![Part2ColorOutputCapacity::EsrgbChannels {context}];
    let red=part2_esrgb_plane_requests(image,colors,0);
    let green=if color_esrgb_plane(image,colors,0).is_ok(){part2_esrgb_plane_requests(image,colors,1)}else{Seq::empty()};
    let blue=if color_esrgb_plane(image,colors,0).is_ok() && color_esrgb_plane(image,colors,1).is_ok(){part2_esrgb_plane_requests(image,colors,2)}else{Seq::empty()};
    assert(part2_esrgb_after_layout_requests(context) =~= initial+red+green+blue);
    let child=part2_esrgb_plane_requests(image,colors,role);
    assert forall|request:Part2ColorOutputCapacity|child.contains(request) implies part2_color_convert_requests(context).contains(request) by {
        if role==0 {part2_color_output_concat_member(initial,red,request);}
        if role<=1 {part2_color_output_concat_member(initial+red,green,request);}
        part2_color_output_concat_member(initial+red+green,blue,request);
        part2_color_output_concat_member(part2_color_layout_requests(image.2,3),part2_esrgb_after_layout_requests(context),request);
    }
    part2_color_output_program_child_error(part2_color_convert_requests(context),part2_color_convert_value(context),child,color_esrgb_plane(image,colors,role),error);
    part2_color_convert_storage_from_program(context,Err(error));
}
}
