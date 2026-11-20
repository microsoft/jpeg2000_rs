use super::*;
verus! {
pub type Part2CompatibleColorResult = Result<(Part2ConvertedImage, crate::color::ColorRecovery),crate::DecodeError>;

pub closed spec fn compatible_decode_value(input:Seq<u8>,limits:&crate::ResourceLimits)
    ->Part2CompatibleColorResult {
    match part2_decode_raw_single_container(input,limits,None,false) {
        Err(error)=>Err(error),
        Ok(image)=>match part2_parse_container(input,*limits) {
            Err(error)=>Err(error),
            Ok(file)=>compatible_after_parse_value(image,file,limits),
        },
    }
}
pub(crate) proof fn compatible_decode_value_unfold(input:Seq<u8>,limits:&crate::ResourceLimits)
    ensures compatible_decode_value(input,limits)==match part2_decode_raw_single_container(input,limits,None,false) {
        Err(error)=>Err(error),
        Ok(image)=>match part2_parse_container(input,*limits) {
            Err(error)=>Err(error),
            Ok(file)=>compatible_after_parse_value(image,file,limits),
        },
    },
{
    reveal(compatible_decode_value);
}

pub(crate) open spec fn compatible_container_context(image:Part1DecodedTypedImage,file:Part2RawJp2File,
    limits:&crate::ResourceLimits)->Part2ColorConvertContext {
    Part2ColorConvertContext {image,method:part2_raw_associated_header(file.header).2,
        bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits)}
}
pub(crate) open spec fn compatible_container_profile(image:Part1DecodedTypedImage,file:Part2RawJp2File)
    ->Result<(),crate::DecodeError> {
    if color_esrgb8_compatible(image,part2_raw_associated_header(file.header).2) {Ok(())}
    else {part2_esrgb_color_display_profile(file)}
}
pub(crate) open spec fn compatible_after_parse_value(image:Part1DecodedTypedImage,file:Part2RawJp2File,
    limits:&crate::ResourceLimits)->Part2CompatibleColorResult {
    match compatible_container_profile(image,file) {
        Err(error)=>Err(error),
        Ok(())=>color_compatible_value(compatible_container_context(image,file,limits)),
    }
}
pub(crate) open spec fn compatible_after_parse_run(image:Part1DecodedTypedImage,file:Part2RawJp2File,
    limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<(Part2ConvertedImage,crate::color::ColorRecovery)> {
    match compatible_container_profile(image,file) {
        Err(error)=>Some((Err(error),events)),
        Ok(())=>color_compatible_run(compatible_container_context(image,file,limits),events),
    }
}
pub(crate) open spec fn compatible_after_native_run(input:Seq<u8>,limits:&crate::ResourceLimits,
    image:Part1DecodedTypedImage,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<(Part2ConvertedImage,crate::color::ColorRecovery)> {
    part2_jpip_snapshot_bind(part2_parse_container_cold_run(input,*limits,events),
        |file:Part2RawJp2File,rest|compatible_after_parse_run(image,file,limits,rest))
}
pub(crate) open spec fn compatible_decode_run(input:Seq<u8>,limits:&crate::ResourceLimits,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Part2ConvertedImage,crate::color::ColorRecovery)> {
    part2_jpip_snapshot_bind(part2_decode_single_cold_run(input,limits,None,false,events),
        |image:Part1DecodedTypedImage,rest|compatible_after_native_run(input,limits,image,rest))
}
pub closed spec fn compatible_decode_result(input:Seq<u8>,limits:&crate::ResourceLimits,
    result:Part2CompatibleColorResult)->bool {
    part2_cold_framed(|events|compatible_decode_run(input,limits,events),result)
}
pub(crate) proof fn compatible_after_native_actual(input:Seq<u8>,limits:&crate::ResourceLimits,
    image:Part1DecodedTypedImage,parsed:Result<Part2RawJp2File,crate::DecodeError>,result:Part2CompatibleColorResult)
    requires part2_parse_container_cold_result(input,*limits,parsed),
        match parsed {
            Err(error)=>result==Err(error),
            Ok(file)=>match compatible_container_profile(image,file) {
                Err(error)=>result==Err(error),
                Ok(())=>color_compatible_result(compatible_container_context(image,file,limits),result),
            },
        },
    ensures part2_cold_framed(|events|compatible_after_native_run(input,limits,image,events),result),
{
    part2_parse_container_cold_frames(input,*limits,parsed);
    if let Ok(file)=parsed {
        match compatible_container_profile(image,file) {
            Err(error)=>{
                part2_cold_pure::<(Part2ConvertedImage,crate::color::ColorRecovery)>(Err(error));
                part2_cold_framed_extensional(|events|Some((Err(error),events)),
                    |events|compatible_after_parse_run(image,file,limits,events),result);
            },
            Ok(())=>{
                color_compatible_frames(compatible_container_context(image,file,limits),result);
                part2_cold_framed_extensional(
                    |events|color_compatible_run(compatible_container_context(image,file,limits),events),
                    |events|compatible_after_parse_run(image,file,limits,events),result);
            },
        }
        part2_decode_eta(|events|compatible_after_parse_run(image,file,limits,events),result);
    }
    part2_cold_bind(|events|part2_parse_container_cold_run(input,*limits,events),
        |file:Part2RawJp2File,rest|compatible_after_parse_run(image,file,limits,rest),parsed,result);
}
pub(crate) proof fn compatible_decode_actual(input:Seq<u8>,limits:&crate::ResourceLimits,
    decoded:Result<Part1DecodedTypedImage,crate::DecodeError>,result:Part2CompatibleColorResult)
    requires part2_decode_single_cold_result(input,limits,None,false,decoded),
        match decoded {
            Err(error)=>result==Err(error),
            Ok(image)=>part2_cold_framed(|events|compatible_after_native_run(input,limits,image,events),result),
        },
    ensures compatible_decode_result(input,limits,result),
{
    reveal(compatible_decode_result);
    part2_decode_single_cold_frames(input,limits,None,false,decoded);
    if let Ok(image)=decoded {
        part2_decode_eta(|events|compatible_after_native_run(input,limits,image,events),result);
    }
    part2_cold_bind(|events|part2_decode_single_cold_run(input,limits,None,false,events),
        |image:Part1DecodedTypedImage,rest|compatible_after_native_run(input,limits,image,rest),decoded,result);
}
}
